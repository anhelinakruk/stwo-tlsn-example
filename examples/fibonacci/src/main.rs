#![feature(portable_simd)]
#![feature(array_chunks)]
#![feature(iter_array_chunks)]

pub mod fibonacci;
// pub mod blake3;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use stwo::core::{fields::qm31::SecureField, poly::circle::CanonicCoset};

    use crate::fibonacci::{FibComponent, FibEval, gen_fib_trace, gen_is_first_column, gen_is_target_column, is_first_column_id, is_target_column_id};

    #[test]
    fn test_bridge_only_prove_verify() {
        use stwo::core::air::Component;
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
        use stwo::core::verifier::verify;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::{prove, CommitmentSchemeProver};
        use stwo_constraint_framework::TraceLocationAllocator;

        let log_size = 4;
        let fibonacci_index = 8;

         let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Trace generated: {} columns", fib_trace.len());
        println!("Value: {}", fibonacci_value);
        let is_first_col = gen_is_first_column(log_size);
        let is_target_col = gen_is_target_column(log_size, fibonacci_index);

        let config = PcsConfig::default();
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([is_first_col, is_target_col]);
        tree_builder.commit(prover_channel);
        println!("Preprocessed trace committed");

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.commit(prover_channel);
        println!("Base trace committed");

        let fib_component = FibComponent::new(
            &mut TraceLocationAllocator::default(),
            FibEval {
                log_n_rows: log_size,
                fibonacci_value: fibonacci_value,
                is_first_id: is_first_column_id(log_size),
                is_target_id: is_target_column_id(log_size)
            },
            SecureField::zero(),
        );
        println!("Component created");

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &[&fib_component],
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let sizes = fib_component.trace_log_degree_bounds();
        commitment_scheme_verifier.commit(proof.commitments[0], &sizes[0], verifier_channel);
        commitment_scheme_verifier.commit(proof.commitments[1], &sizes[1], verifier_channel);

        verify(
            &[&fib_component],
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("PROOF VERIFIED SUCCESSFULLY!");
    }
}
