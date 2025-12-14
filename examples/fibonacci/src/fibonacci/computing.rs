use num_traits::One;
use stwo::core::fields::m31::BaseField;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, ORIGINAL_TRACE_IDX, RelationEntry,
};

use super::{LOG_CONSTRAINT_DEGREE, ValueRelation};

#[derive(Clone)]
pub struct FibEval {
    pub log_n_rows: u32,
    pub is_first_id: PreProcessedColumnId,
    pub is_target_id: PreProcessedColumnId,
    pub value_relation: ValueRelation,
}

impl FrameworkEval for FibEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_CONSTRAINT_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let is_first = eval.get_preprocessed_column(self.is_first_id.clone());
        let is_target = eval.get_preprocessed_column(self.is_target_id.clone());

        let [a_curr, _a_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [b_curr, b_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [c_curr, c_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);

        // CONSTRAINT 1: Fibonacci relation c = a + b
        eval.add_constraint(c_curr.clone() - (a_curr.clone() + b_curr.clone()));

        // CONSTRAINT 2: Transition a_curr = b_prev (disabled for first row)
        let not_first = E::F::one() - is_first.clone();
        eval.add_constraint(not_first.clone() * (a_curr.clone() - b_prev));

        // CONSTRAINT 3: Transition b_curr = c_prev (disabled for first row)
        eval.add_constraint(not_first.clone() * (b_curr.clone() - c_prev));

        // CONSTRAINT 4: Initial value a = 0 at first row
        eval.add_constraint(is_first.clone() * a_curr.clone());

        // CONSTRAINT 5: Initial value b = 1 at first row
        eval.add_constraint(is_first.clone() * (b_curr.clone() - E::F::one()));

        eval.add_to_relation(RelationEntry::new(
            &self.value_relation,
            -E::EF::from(is_target),
            &[a_curr],
        ));

        eval.finalize_logup();
        eval
    }
}

pub type FibComponent = FrameworkComponent<FibEval>;