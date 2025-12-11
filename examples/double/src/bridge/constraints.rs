use stwo_constraint_framework::{FrameworkComponent, FrameworkEval, RelationEntry};

use crate::bridge::{InputRelation, LOG_CONSTRAINT_DEGREE};

pub struct InputBridgeEval {
    pub log_n_rows: u32,
    pub input_value: u32,
    pub input_relation: InputRelation,
}

impl FrameworkEval for InputBridgeEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_CONSTRAINT_DEGREE
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let input = eval.next_trace_mask();
        let multiplicity = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.input_relation,
            -E::EF::from(multiplicity),
            &[input],
        ));

        eval.finalize_logup();
        eval
    }
}

pub type InputBridgeComponent = FrameworkComponent<InputBridgeEval>;
