use num_traits::{One, Zero};
use stwo::core::fields::m31::BaseField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;

pub fn gen_fib_trace(
    log_size: u32,
    fibonacci_index: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    u32,
) {
    let n_rows = 1 << log_size;

    assert!(
        fibonacci_index < n_rows,
        "fibonacci_index ({}) must be less than n_rows ({})",
        fibonacci_index, n_rows
    );

    let mut col_a = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_b = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_c = Col::<SimdBackend, BaseField>::zeros(n_rows);

    let mut a = BaseField::zero();
    let mut b = BaseField::one();
    let mut target_value = 0u32; 

    for row in 0..n_rows {
        let c = a + b;

        col_a.set(row, a);
        col_b.set(row, b);
        col_c.set(row, c);

        if row == fibonacci_index {
            target_value = a.0;
        }

        a = b;
        b = c;
    }

    bit_reverse_coset_to_circle_domain_order(col_a.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_b.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_c.as_mut_slice());

    let domain = CanonicCoset::new(log_size).circle_domain();

    (
        vec![
            CircleEvaluation::new(domain.clone(), col_a),
            CircleEvaluation::new(domain.clone(), col_b),
            CircleEvaluation::new(domain.clone(), col_c),
        ],
        target_value,
    )
}

// pub fn gen_fib_interaction_trace(
//     trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
//     index_relation: &IndexRelation,
// ) -> (
//     ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
//     SecureField,
// ) {
//     let log_size = trace[0].domain.log_size();
//     let mut logup_gen = LogupTraceGenerator::new(log_size);

//     {
//         let mut col_gen = logup_gen.new_col();

//         let index_used_col = &trace[4];
//         let multiplicity_col = &trace[5];

//         for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
//             let index_packed = index_used_col.values.data[vec_row];
//             let multiplicity_packed = multiplicity_col.values.data[vec_row];

//             let denom = index_relation.combine(&[PackedSecureField::from(index_packed)]);

//             let numerator = PackedSecureField::from(multiplicity_packed);

//             col_gen.write_frac(vec_row, numerator, denom);
//         }

//         col_gen.finalize_col();
//     }

//     logup_gen.finalize_last()
// }
