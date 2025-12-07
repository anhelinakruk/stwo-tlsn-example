use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo_constraint_framework::Relation;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::LogupTraceGenerator;

use crate::bridge::IndexRelation;

pub fn gen_bridge_trace(
    log_size: u32,
    fibonacci_index: usize,
    num_consumers: usize, 
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let n_rows = 1 << log_size;
    let index_value = BaseField::from_u32_unchecked(fibonacci_index as u32);
    let multiplicity_value = BaseField::from_u32_unchecked(num_consumers as u32);

    let mut col_index = Col::<SimdBackend, BaseField>::zeros(n_rows);
    col_index.set(0, index_value);
    bit_reverse_coset_to_circle_domain_order(col_index.as_mut_slice());

    let mut col_multiplicity = Col::<SimdBackend, BaseField>::zeros(n_rows);
    col_multiplicity.set(0, multiplicity_value);  
    bit_reverse_coset_to_circle_domain_order(col_multiplicity.as_mut_slice());

    let domain = CanonicCoset::new(log_size).circle_domain();
    vec![
        CircleEvaluation::new(domain.clone(), col_index),
        CircleEvaluation::new(domain, col_multiplicity),
    ]
}

pub fn gen_bridge_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    index_relation: &IndexRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let index_packed = trace[0].values.data[vec_row];
            let multiplicity_packed = trace[1].values.data[vec_row];

            let denom = index_relation.combine(&[PackedSecureField::from(index_packed)]);

            let numerator = -PackedSecureField::from(multiplicity_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}