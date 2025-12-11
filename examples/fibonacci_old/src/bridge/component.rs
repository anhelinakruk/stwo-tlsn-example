use stwo_constraint_framework::{FrameworkComponent, FrameworkEval, RelationEntry};

use crate::bridge::{IndexRelation, LOG_CONSTRAINT_DEGREE};

pub struct IndexBridgeEval {
    pub log_n_rows: u32,
    pub index_value: usize,
    pub index_relation: IndexRelation,
}

impl FrameworkEval for IndexBridgeEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_CONSTRAINT_DEGREE
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let index_curr = eval.next_trace_mask();
        let multiplicity_curr = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.index_relation,
            -E::EF::from(multiplicity_curr),
            &[index_curr],
        ));

        eval.finalize_logup();
        eval
    }
}

pub type IndexBridgeComponent = FrameworkComponent<IndexBridgeEval>;
