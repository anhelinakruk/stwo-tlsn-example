use num_traits::One;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use crate::bridge::InputRelation;

pub fn gen_double_trace(
    log_size: u32,
    input: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    u32,
) {
    let n_rows = 1 << log_size;

    let mut col_input = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_output = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_multiplicity = Col::<SimdBackend, BaseField>::zeros(n_rows);

    let input = BaseField::from_u32_unchecked(input);
    let output = input + input;

    for row in 0..n_rows {
        if row == 0 {
            col_input.set(row, input);
            col_output.set(row, output);
            col_multiplicity.set(row, BaseField::one());
        }
    }

    println!("COL IPUT: {:?}", col_input);
    println!("COL OPUT: {:?}", col_output);
    println!("COL MUL: {:?}", col_multiplicity);

    bit_reverse_coset_to_circle_domain_order(col_input.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_input.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_multiplicity.as_mut_slice());

    let domain = CanonicCoset::new(log_size).circle_domain();

    (
        vec![
            CircleEvaluation::new(domain.clone(), col_input.clone()),
            CircleEvaluation::new(domain.clone(), col_output.clone()),
            CircleEvaluation::new(domain.clone(), col_multiplicity.clone()),
        ],
        output.0,
    )
}

pub fn gen_double_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    input_relation: &InputRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        let input_col = &trace[0];
        let multiplicity_col = &trace[2];

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

pub fn gen_is_first_column(
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;
    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);

    col.set(0, BaseField::from_u32_unchecked(1));

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_first_column_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_first_{}", log_size),
    }
}
