mod computing;
mod trace_gen;

pub use computing::{FibEval, SimpleFibComponent};
pub use trace_gen::{gen_fib_interaction_trace, gen_fib_trace};

use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::pcs::{ TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

pub const LOG_CONSTRAINT_DEGREE: u32 = 1;

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

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct FibStatement {
    pub log_size: u32,
    pub fibonacci_value: u32,
}

impl FibStatement {
    pub fn mix_into(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.fibonacci_value as u64);
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec(vec![vec![self.log_size; 1], vec![self.log_size; 4]])
    }
}
