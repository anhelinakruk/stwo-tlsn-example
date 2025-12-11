//! Test Bridge + Fibonacci integration with multiplicity=1
//! This test verifies that Bridge can produce an index with multiplicity=1
//! and Fibonacci can consume it via LogUp arguments.

#[cfg(test)]
mod tests {
    use stwo::core::poly::circle::CanonicCoset;

    use crate::bridge::{
        IndexBridgeComponent, IndexBridgeEval, IndexRelation, gen_bridge_interaction_trace,
        gen_bridge_trace,
    };
    use crate::fibonacci::{
        FibEval, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, is_first_column_id,
    };

    #[test]
    fn test_bridge_only_prove_verify() {
        use stwo::core::air::Component;
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
        use stwo::core::verifier::verify;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::{CommitmentSchemeProver, prove};
        use stwo_constraint_framework::TraceLocationAllocator;

        let log_size = 10;
        let fibonacci_index = 100;

        println!("\n=== Testing ONLY Bridge component ===");

        println!("\n=== Step 1: Generate Bridge trace ===");
        let bridge_trace = gen_bridge_trace(log_size, fibonacci_index, 1);
        println!("✓ Bridge trace generated: {} columns", bridge_trace.len());

        println!("\n=== Step 2: Setup prover ===");
        let config = PcsConfig::default();
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        println!("\n=== Step 3: Commit preprocessed trace (empty) ===");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([]);
        tree_builder.commit(prover_channel);
        println!("✓ Preprocessed trace committed");

        println!("\n=== Step 4: Commit Bridge base trace ===");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_trace.clone());
        tree_builder.commit(prover_channel);
        println!("✓ Bridge base trace committed");

        println!("\n=== Step 5: Draw interaction elements ===");
        let index_elements = IndexRelation::draw(prover_channel);

        println!("\n=== Step 6: Generate Bridge interaction trace ===");
        let (bridge_interaction_trace, bridge_claimed_sum) =
            gen_bridge_interaction_trace(&bridge_trace, &index_elements);
        println!(
            "✓ Bridge interaction trace: {} columns",
            bridge_interaction_trace.len()
        );
        println!("  Bridge claimed sum: {:?}", bridge_claimed_sum);

        println!("\n=== Step 7: Commit interaction trace ===");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_interaction_trace);
        tree_builder.commit(prover_channel);
        println!("✓ Interaction trace committed");

        println!("\n=== Step 8: Create Bridge component ===");
        let bridge_component = IndexBridgeComponent::new(
            &mut TraceLocationAllocator::default(),
            IndexBridgeEval {
                log_n_rows: log_size,
                index_value: fibonacci_index,
                index_relation: index_elements.clone(),
            },
            bridge_claimed_sum,
        );
        println!("✓ Bridge component created");

        println!("\n=== Step 9: Generate proof ===");
        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &[&bridge_component],
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("✅ PROOF GENERATED!");
        println!("  Proof size: {} commitments", proof.commitments.len());

        println!("\n=== Step 10: Verify proof ===");
        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let sizes = bridge_component.trace_log_degree_bounds();
        commitment_scheme_verifier.commit(proof.commitments[0], &sizes[0], verifier_channel);
        commitment_scheme_verifier.commit(proof.commitments[1], &sizes[1], verifier_channel);
        commitment_scheme_verifier.commit(proof.commitments[2], &sizes[2], verifier_channel);

        verify(
            &[&bridge_component],
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("✅ PROOF VERIFIED SUCCESSFULLY!");
        println!("\n=== Bridge-only test passed! ===");
    }

    #[test]
    fn test_bridge_fibonacci_prove_verify() {
        use stwo::core::air::Component;
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
        use stwo::core::verifier::verify;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::{CommitmentSchemeProver, prove};
        use stwo_constraint_framework::TraceLocationAllocator;

        let log_size = 10;
        let fibonacci_index = 100;

        let bridge_trace = gen_bridge_trace(log_size, fibonacci_index, 1);
        println!("Bridge trace generated: {} columns", bridge_trace.len());

        let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Fibonacci trace generated: {} columns", fib_trace.len());
        println!("Fibonacci({}) = {}", fibonacci_index, fibonacci_value);

        let is_first_col = gen_is_first_column(log_size);

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
        tree_builder.extend_evals([]);
        tree_builder.extend_evals(vec![is_first_col]);
        tree_builder.commit(prover_channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_trace.clone());
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.commit(prover_channel);

        let index_elements = IndexRelation::draw(prover_channel);

        let (bridge_interaction_trace, bridge_claimed_sum) =
            gen_bridge_interaction_trace(&bridge_trace, &index_elements);
        println!(
            "Bridge interaction trace: {} columns",
            bridge_interaction_trace.len()
        );
        println!("Bridge claimed sum: {:?}", bridge_claimed_sum);

        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(&fib_trace, &index_elements);
        println!(
            "Fibonacci interaction trace: {} columns",
            fib_interaction_trace.len()
        );
        println!("Fibonacci claimed sum: {:?}", fib_claimed_sum);

        let total_sum = bridge_claimed_sum + fib_claimed_sum;
        println!("Total LogUp sum (should be ~0): {:?}", total_sum);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_interaction_trace);
        tree_builder.extend_evals(fib_interaction_trace);
        tree_builder.commit(prover_channel);

        let mut tree_span_provider = TraceLocationAllocator::default();

        let bridge_component = IndexBridgeComponent::new(
            &mut tree_span_provider,
            IndexBridgeEval {
                log_n_rows: log_size,
                index_value: fibonacci_index,
                index_relation: index_elements.clone(),
            },
            bridge_claimed_sum,
        );
        println!("Bridge component created");
        println!(
            "Bridge trace_log_degree_bounds: {:?}",
            bridge_component.trace_log_degree_bounds()
        );

        let fib_component = crate::fibonacci::SimpleFibComponent::new(
            &mut tree_span_provider,
            FibEval {
                log_n_rows: log_size,
                fibonacci_value,
                is_first_id: is_first_column_id(log_size),
                index_relation: index_elements.clone(),
            },
            fib_claimed_sum,
        );
        println!("Fibonacci component created");
        println!(
            "Fibonacci trace_log_degree_bounds: {:?}",
            fib_component.trace_log_degree_bounds()
        );

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &[&bridge_component, &fib_component],
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");
        println!("Proof size: {} commitments", proof.commitments.len());

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let bridge_sizes = bridge_component.trace_log_degree_bounds();
        let fib_sizes = fib_component.trace_log_degree_bounds();

        let combined_preprocessed_sizes: Vec<u32> = bridge_sizes[0]
            .iter()
            .chain(fib_sizes[0].iter())
            .copied()
            .collect();
        let combined_base_sizes: Vec<u32> = bridge_sizes[1]
            .iter()
            .chain(fib_sizes[1].iter())
            .copied()
            .collect();
        let combined_interaction_sizes: Vec<u32> = bridge_sizes[2]
            .iter()
            .chain(fib_sizes[2].iter())
            .copied()
            .collect();

        commitment_scheme_verifier.commit(
            proof.commitments[0],
            &combined_preprocessed_sizes,
            verifier_channel,
        );
        commitment_scheme_verifier.commit(
            proof.commitments[1],
            &combined_base_sizes,
            verifier_channel,
        );
        commitment_scheme_verifier.commit(
            proof.commitments[2],
            &combined_interaction_sizes,
            verifier_channel,
        );

        verify(
            &[&bridge_component, &fib_component],
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("PROOF VERIFIED SUCCESSFULLY!");
    }
}
