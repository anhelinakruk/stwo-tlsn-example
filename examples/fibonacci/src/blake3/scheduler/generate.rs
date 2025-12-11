use std::simd::u32x16;

use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
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
    input: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BlakeSchedulerLookupData,
    Vec<BlakeRoundInput>,
) {
    let _span = span!(Level::INFO, "Scheduler Generation").entered();
    let mut lookup_data = BlakeSchedulerLookupData::new(log_size);
    let mut round_inputs = Vec::with_capacity(inputs.len() * N_ROUNDS);

    // Calculate number of columns:
    // 16*2 (messages) + 16*2 (initial_v) + 7*16*2 (v after each round)
    // = 32 + 32 + 224 + 2 = 290 columns
    let n_cols = STATE_SIZE * 2 + STATE_SIZE * 2 + N_ROUNDS * STATE_SIZE * 2;

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


        let mut col_input = Col::<SimdBackend, BaseField>::zeros(1 << log_size);
        let mut col_multiplicity = Col::<SimdBackend, BaseField>::zeros(1 << log_size);

        col_input.set(0, BaseField::from_u32_unchecked(input));
        col_multiplicity.set(0, BaseField::one());

        trace.push(col_input);
        trace.push(col_multiplicity);

        // let input_col_start = n_cols - 2;
        // if vec_row == 0 {
        //     trace[input_col_start].data[vec_row] = unsafe {
        //         PackedBaseField::from_simd_unchecked(u32x16::splat(input))  // Use parameter!
        //     };
        //     trace[input_col_start + 1].data[vec_row] = unsafe {
        //         PackedBaseField::from_simd_unchecked(u32x16::splat(1))
        //     };
        // } else {
        //     trace[input_col_start].data[vec_row] = PackedBaseField::zero();
        //     trace[input_col_start + 1].data[vec_row] = PackedBaseField::zero();
        // }

        // DEBUG: Print first few vec_rows
        if vec_row < 3 {
            println!("Blake scheduler vec_row {}: input packed = {:?}", vec_row, trace[n_cols].data[vec_row]);
            println!("Blake scheduler vec_row {}: multiplicity packed = {:?}", vec_row, trace[n_cols+1].data[vec_row]);
        }
    }

    println!("Blake scheduler total vec_rows: {}", 1 << (log_size - LOG_N_LANES));

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
    input_trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    input_relation: &crate::bridge::InputRelation,
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

    {
        let mut col_gen = logup_gen.new_col();

        let n_cols = input_trace.len();
        let input_col = &input_trace[n_cols - 2];
        let multiplicity_col = &input_trace[n_cols - 1];

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let input_packed = input_col.values.data[vec_row];
            let multiplicity_packed = multiplicity_col.values.data[vec_row];

            let denom = input_relation.combine(&[PackedSecureField::from(input_packed)]);
            let numerator = PackedSecureField::from(multiplicity_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}
