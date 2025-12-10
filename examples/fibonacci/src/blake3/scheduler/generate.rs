use std::simd::u32x16;

use itertools::{chain, Itertools};
use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedBaseField, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use tracing::{span, Level};

use super::BlakeElements;
use crate::blake3::blake3;
use crate::blake3::round::{BlakeRoundInput, RoundElements};
use crate::blake3::{to_felts, N_ROUNDS, N_ROUND_INPUT_FELTS, STATE_SIZE};

#[derive(Copy, Clone, Default)]
pub struct BlakeInput {
    pub v: [u32x16; STATE_SIZE],
    pub m: [u32x16; STATE_SIZE],
}

#[derive(Clone)]
pub struct BlakeSchedulerLookupData {
    pub round_lookups: [[BaseColumn; N_ROUND_INPUT_FELTS]; N_ROUNDS],
    pub blake_lookups: [BaseColumn; N_ROUND_INPUT_FELTS],
}
impl BlakeSchedulerLookupData {
    fn new(log_size: u32) -> Self {
        Self {
            round_lookups: std::array::from_fn(|_| {
                std::array::from_fn(|_| unsafe { BaseColumn::uninitialized(1 << log_size) })
            }),
            blake_lookups: std::array::from_fn(|_| unsafe {
                BaseColumn::uninitialized(1 << log_size)
            }),
        }
    }
}

pub fn gen_trace(
    log_size: u32,
    inputs: &[BlakeInput],
    fibonacci_index: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BlakeSchedulerLookupData,
    Vec<BlakeRoundInput>,
) {
    let _span = span!(Level::INFO, "Scheduler Generation").entered();
    let mut lookup_data = BlakeSchedulerLookupData::new(log_size);
    let mut round_inputs = Vec::with_capacity(inputs.len() * N_ROUNDS);

    // Calculate number of columns:
    // 16*2 (messages) + 16*2 (initial_v) + 7*16*2 (v after each round) + 2 (index columns)
    // = 32 + 32 + 224 + 2 = 290 columns
    let n_cols = STATE_SIZE * 2 + STATE_SIZE * 2 + N_ROUNDS * STATE_SIZE * 2 + 2;

    let mut trace = (0..n_cols)
        .map(|_| unsafe { BaseColumn::uninitialized(1 << log_size) })
        .collect_vec();

    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let mut col_index = 0;  // Start from column 0

        let mut write_u32_array = |x: [u32x16; STATE_SIZE], col_index: &mut usize| {
            x.iter().for_each(|x| {
                to_felts(x).iter().for_each(|x| {
                    trace[*col_index].data[vec_row] = *x;
                    *col_index += 1;
                });
            });
        };

        let BlakeInput { mut v, m } = inputs.get(vec_row).copied().unwrap_or_default();
        let initial_v = v;

        write_u32_array(m, &mut col_index);
        write_u32_array(v, &mut col_index);

        // Blake3 permutes message BETWEEN rounds using MSG_SCHEDULE
        let mut m_current = m;

        for r in 0..N_ROUNDS {
            let prev_v = v;
            blake3::round(&mut v, m_current, r);
            write_u32_array(v, &mut col_index);

            // Pass current message state to round_inputs
            round_inputs.push(BlakeRoundInput {
                v: prev_v,
                m: m_current,
            });

            chain![
                prev_v.iter().flat_map(to_felts),
                v.iter().flat_map(to_felts),
                m_current.iter().flat_map(to_felts)
            ]
            .enumerate()
            .for_each(|(i, val)| lookup_data.round_lookups[r][i].data[vec_row] = val);

            // Permute message for next round
            m_current = blake3::MSG_SCHEDULE.map(|i| m_current[i as usize]);
        }

        chain![
            initial_v.iter().flat_map(to_felts),
            v.iter().flat_map(to_felts),
            m.iter().flat_map(to_felts)
        ]
        .enumerate()
        .for_each(|(i, val)| lookup_data.blake_lookups[i].data[vec_row] = val);

        // Index columns: set only in first row (vec_row == 0)
        let index_col_start = n_cols - 2;
        if vec_row == 0 {
            trace[index_col_start].data[vec_row] = unsafe { PackedBaseField::from_simd_unchecked(
                u32x16::splat(fibonacci_index)
            ) };
            trace[index_col_start + 1].data[vec_row] = unsafe { PackedBaseField::from_simd_unchecked(
                u32x16::splat(1)  // multiplicity = 1
            ) };
        } else {
            trace[index_col_start].data[vec_row] = PackedBaseField::zero();
            trace[index_col_start + 1].data[vec_row] = PackedBaseField::zero();
        }
    }

    // --- DEBUG / ASERCJE SANITY CHECK dla gen_trace ---
    // 1) sprawdź czy n_cols odpowiada liczbie kolumn, które rzeczywiście wypełniliśmy
    // (dodajemy to po pętli vec_row)
    {
        // col_index jest lokalne w pętli, więc musimy policzyć ponownie w szybkiej symulacji:
        let mut col_index_check = 0usize;
        // message array -> m (STATE_SIZE u32x16) -> each expands to to_felts() length
        // compute felts per u32x16 using to_felts on a dummy value:
        let sample_u = inputs.get(0).map(|bi| bi.m).unwrap_or([u32x16::splat(0); STATE_SIZE]);
        // take first element and measure len
        let felts_per_lane = to_felts(&sample_u[0]).len();
        // felts written by write_u32_array for one array of STATE_SIZE:
        let felts_per_array = STATE_SIZE * felts_per_lane;

        // columns layout in row: m (felts_per_array) + v (felts_per_array) + N_ROUNDS * (v_after_round (felts_per_array))
        let computed_n_cols = felts_per_array + felts_per_array + (N_ROUNDS as usize) * felts_per_array;
        if computed_n_cols != n_cols as usize {
            eprintln!("GEN_TRACE SANITY: computed_n_cols={} but n_cols={} -- MISMATCH!", computed_n_cols, n_cols);
        } else {
            eprintln!("GEN_TRACE SANITY: computed_n_cols == n_cols == {}", n_cols);
        }

        // 2) sprawdź, czy dla każdego round r, liczba wartości zapisywanych do lookup_data.round_lookups[r] odpowiada N_ROUND_INPUT_FELTS
        // policz liczbę felts generowanych przez chain![prev_v, v, m_current]
        let felts_per_round_triplet = (STATE_SIZE * felts_per_lane) * 3; // prev_v + v + m_current
        eprintln!("GEN_TRACE SANITY: felts_per_lane = {}, felts_per_round_triplet = {}", felts_per_lane, felts_per_round_triplet);
        eprintln!("GEN_TRACE SANITY: N_ROUND_INPUT_FELTS = {}", N_ROUND_INPUT_FELTS);

        if felts_per_round_triplet != N_ROUND_INPUT_FELTS as usize {
            eprintln!("GEN_TRACE SANITY: WARNING: felts_per_round_triplet ({}) != N_ROUND_INPUT_FELTS ({})",
                      felts_per_round_triplet, N_ROUND_INPUT_FELTS);
        } else {
            eprintln!("GEN_TRACE SANITY: round triplet size matches N_ROUND_INPUT_FELTS");
        }

        // 3) check round_inputs length
        let expected_round_inputs = inputs.len() * (N_ROUNDS as usize);
        eprintln!("GEN_TRACE SANITY: round_inputs.len() = {}, expected = {}", round_inputs.len(), expected_round_inputs);
        if round_inputs.len() != expected_round_inputs {
            eprintln!("GEN_TRACE SANITY: round_inputs length mismatch!");
        }
    }

    let domain = CanonicCoset::new(log_size).circle_domain();
    let trace = trace
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval))
        .collect();

    (trace, lookup_data, round_inputs)
}

pub fn gen_interaction_trace(
    log_size: u32,
    lookup_data: BlakeSchedulerLookupData,
    round_lookup_elements: &RoundElements,
    blake_lookup_elements: &BlakeElements,
    index_trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    index_relation: &crate::bridge::IndexRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let _span = span!(Level::INFO, "Generate scheduler interaction trace").entered();

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // First, generate round pair columns (will be at beginning to match evaluate order)
    for [l0, l1] in lookup_data.round_lookups.array_chunks::<2>() {
        let mut col_gen = logup_gen.new_col();

        #[allow(clippy::needless_range_loop)]
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let p0: PackedSecureField =
                round_lookup_elements.combine(&l0.each_ref().map(|l| l.data[vec_row]));
            let p1: PackedSecureField =
                round_lookup_elements.combine(&l1.each_ref().map(|l| l.data[vec_row]));
            #[allow(clippy::eq_op)]
            col_gen.write_frac(vec_row, p0 + p1, p0 * p1);
        }

        col_gen.finalize_col();
    }

    // Last pair (round6 + blake) - this matches the pairing in eval_blake_scheduler_constraints
    {
        let mut col_gen = logup_gen.new_col();
        #[allow(clippy::needless_range_loop)]
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let p_blake: PackedSecureField = blake_lookup_elements.combine(
                &lookup_data
                    .blake_lookups
                    .each_ref()
                    .map(|l| l.data[vec_row]),
            );
            if N_ROUNDS % 2 == 1 {
                let p_round: PackedSecureField = round_lookup_elements.combine(
                    &lookup_data.round_lookups[N_ROUNDS - 1]
                        .each_ref()
                        .map(|l| l.data[vec_row]),
                );
                col_gen.write_frac(vec_row, p_blake, p_round * p_blake);
            } else {
                col_gen.write_frac(vec_row, PackedSecureField::zero(), p_blake);
            }
        }
        col_gen.finalize_col();
    }

    // Index consumption logup (similar to fibonacci)
    {
        let mut col_gen = logup_gen.new_col();

        let n_cols = index_trace.len();
        let index_used_col = &index_trace[n_cols - 2];
        let multiplicity_col = &index_trace[n_cols - 1];

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let index_packed = index_used_col.values.data[vec_row];
            let multiplicity_packed = multiplicity_col.values.data[vec_row];

            let denom = index_relation.combine(&[PackedSecureField::from(index_packed)]);
            let numerator = PackedSecureField::from(multiplicity_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}
