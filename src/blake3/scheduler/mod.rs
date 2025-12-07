mod constraints;
mod generate;

use constraints::eval_blake_scheduler_constraints;
pub use generate::{gen_interaction_trace, gen_trace, BlakeInput};
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval,
};


use super::round::RoundElements;
use super::N_ROUND_INPUT_FELTS;

pub type BlakeSchedulerComponent = FrameworkComponent<BlakeSchedulerEval>;

relation!(BlakeElements, N_ROUND_INPUT_FELTS);

#[allow(dead_code)]
pub struct BlakeSchedulerEval {
    pub log_size: u32,
    pub blake_lookup_elements: BlakeElements,
    pub round_lookup_elements: RoundElements,
    pub claimed_sum: SecureField,
}
impl FrameworkEval for BlakeSchedulerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        eval_blake_scheduler_constraints(
            &mut eval,
            &self.blake_lookup_elements,
            &self.round_lookup_elements,
        );

        eval
    }
}

pub fn blake_scheduler_info() -> stwo_constraint_framework::InfoEvaluator {
    // Use constraints module directly to avoid the full evaluate flow
    use stwo_constraint_framework::InfoEvaluator;

    let mut eval = InfoEvaluator::empty();

    // Simulate the structure: messages + states columns
    use crate::blake3::{STATE_SIZE, N_ROUNDS};
    // messages: 16 u32 = 32 columns (each u32 = 2 felts)
    for _ in 0..(STATE_SIZE * 2) {
        eval.next_trace_mask();
    }
    // states: (N_ROUNDS+1) * 16 u32 = (N_ROUNDS+1) * 32 columns
    for _ in 0..(((N_ROUNDS + 1) * STATE_SIZE * 2)) {
        eval.next_trace_mask();
    }

    eval
}

#[cfg(test)]
mod tests {
    use std::simd::Simd;

    use itertools::Itertools;
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::FrameworkEval;

    use crate::blake3::round::RoundElements;
    use crate::blake3::scheduler::r#generate::{gen_interaction_trace, gen_trace, BlakeInput};
    use crate::blake3::scheduler::{BlakeElements, BlakeSchedulerEval};

    #[test]
    fn test_blake_scheduler() {
        use stwo::core::pcs::TreeVec;

        const LOG_SIZE: u32 = 10;

        let (trace, lookup_data, _round_inputs) = gen_trace(
            LOG_SIZE,
            &(0..(1 << LOG_SIZE))
                .map(|_| BlakeInput {
                    v: std::array::from_fn(|i| Simd::splat(i as u32)),
                    m: std::array::from_fn(|i| Simd::splat((i + 1) as u32)),
                })
                .collect_vec()
        );

        let round_lookup_elements = RoundElements::dummy();
        let blake_lookup_elements = BlakeElements::dummy();

        let (interaction_trace, claimed_sum) = gen_interaction_trace(
            LOG_SIZE,
            lookup_data,
            &round_lookup_elements,
            &blake_lookup_elements,
        );

        let trace = TreeVec::new(vec![
            vec![],
            trace.into_iter().map(|x| x.values.to_cpu()).collect(),
            interaction_trace
                .into_iter()
                .map(|x| x.values.to_cpu())
                .collect(),
        ]);
        let trace = &trace.as_ref();
        let trace = trace.into();

        let component = BlakeSchedulerEval {
            log_size: LOG_SIZE,
            blake_lookup_elements,
            round_lookup_elements,
            claimed_sum,
        };
        stwo_constraint_framework::assert_constraints_on_trace(
            &trace,
            LOG_SIZE,
            |eval| {
                component.evaluate(eval);
            },
            claimed_sum,
        )
    }
}
