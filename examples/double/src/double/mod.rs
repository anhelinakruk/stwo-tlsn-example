pub mod constraints;
pub mod trace_gen;

pub const LOG_CONSTRAINT_DEGREE: u32 = 1;

// #[cfg(test)]
// mod tests {
//     use num_traits::Zero;
//     use stwo::core::{fields::qm31::SecureField, poly::circle::CanonicCoset};

//     use crate::double::{constraints::{DoubleComponent, DoubleEval}, trace_gen::gen_double_trace};

//     #[test]
//     fn test_prove_verify() {
//         use stwo::core::air::Component;
//         use stwo::core::channel::Blake2sChannel;
//         use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
//         use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
//         use stwo::core::verifier::verify;
//         use stwo::prover::backend::simd::SimdBackend;
//         use stwo::prover::poly::circle::PolyOps;
//         use stwo::prover::{prove, CommitmentSchemeProver};
//         use stwo_constraint_framework::TraceLocationAllocator;

//         let log_size = 4;
//         let input = 5 as u32;

//         let trace = gen_double_trace(log_size, input);

//         let config = PcsConfig::default();
//         let twiddles = SimdBackend::precompute_twiddles(
//             CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
//                 .circle_domain()
//                 .half_coset,
//         );

//         let prover_channel = &mut Blake2sChannel::default();
//         let mut commitment_scheme =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         let mut tree_builder = commitment_scheme.tree_builder();
//         tree_builder.extend_evals([]);
//         tree_builder.commit(prover_channel);
//         println!("Preprocessed trace");

//         let mut tree_builder = commitment_scheme.tree_builder();
//         tree_builder.extend_evals(trace.0.clone());
//         tree_builder.commit(prover_channel);
//         println!("Base trace");

//         let double_component = DoubleComponent::new(
//             &mut TraceLocationAllocator::default(),
//             DoubleEval {
//                 log_n_rows: log_size,
//                 output: input * 2
//             },
//             SecureField::zero(),
//         );
//         println!("Component created");

//         let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
//             &[&double_component],
//             prover_channel,
//             commitment_scheme,
//         )
//         .expect("Failed");

//         println!("proof generated");

//         let verifier_channel = &mut Blake2sChannel::default();
//         let commitment_scheme_verifier =
//             &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

//         let sizes = double_component.trace_log_degree_bounds();
//         commitment_scheme_verifier.commit(proof.commitments[0], &sizes[0], verifier_channel);
//         commitment_scheme_verifier.commit(proof.commitments[1], &sizes[1], verifier_channel);

//         verify(
//             &[&double_component],
//             verifier_channel,
//             commitment_scheme_verifier,
//             proof,
//         )
//         .expect("verification failed");

//         println!("Success");
//     }
// }
