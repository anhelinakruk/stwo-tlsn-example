use stwo_constraint_framework::relation;

pub mod constraints;
pub mod trace_gen;

pub const LOG_CONSTRAINT_DEGREE: u32 = 1;
pub const INPUT_RELATION_SIZE: usize = 2; 

relation!(InputRelation, INPUT_RELATION_SIZE);