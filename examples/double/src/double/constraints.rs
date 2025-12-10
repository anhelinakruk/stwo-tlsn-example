use stwo::core::{fields::m31::BaseField};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry, preprocessed_columns::PreProcessedColumnId};

use crate::bridge::InputRelation;

use super::LOG_CONSTRAINT_DEGREE;

#[derive(Clone)]
pub struct DoubleEval {
    pub log_n_rows: u32,
    pub output: u32,
    pub is_first_id: PreProcessedColumnId,
    pub input_relation: InputRelation
}

impl FrameworkEval for DoubleEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_CONSTRAINT_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let is_first = eval.get_preprocessed_column(self.is_first_id.clone());

        let input = eval.next_trace_mask();
        let output = eval.next_trace_mask();
        let multiplicity = eval.next_trace_mask();

        eval.add_constraint(is_first.clone() * (output.clone() - (input.clone() + input.clone())));

        let expected_output = E::F::from(BaseField::from_u32_unchecked(self.output));
        eval.add_constraint(is_first * (output - expected_output));

        eval.add_to_relation(RelationEntry::new(
            &self.input_relation,
            E::EF::from(multiplicity), 
            &[input]
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type DoubleComponent = FrameworkComponent<DoubleEval>;
