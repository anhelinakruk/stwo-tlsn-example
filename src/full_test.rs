use std::simd::u32x16;

use crate::blake33::scheduler::BlakeInput;

#[cfg(test)]
mod tests {
    use stwo::{core::{channel::Blake2sChannel, pcs::{CommitmentSchemeVerifier, PcsConfig}, poly::circle::CanonicCoset, vcs::blake2_merkle::Blake2sMerkleChannel, verifier::verify}, prover::{CommitmentSchemeProver, backend::simd::SimdBackend, poly::{circle::PolyOps}, prove}};
    use stwo_constraint_framework::TraceLocationAllocator;
    use stwo::core::air::Component;

    use crate::{blake3::{round::RoundElements, scheduler::{BlakeElements, BlakeSchedulerComponent, BlakeSchedulerEval, gen_interaction_trace as gen_blake_interaction_trace, gen_trace as gen_blake_trace}}, bridge::{IndexBridgeComponent, IndexBridgeEval, IndexRelation, gen_bridge_interaction_trace, gen_bridge_trace}, fibonacci::{FibEval, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, is_first_column_id}, full_test::prepare_blake_inputs};

    #[test]
    fn test_full_flow() {
        let log_size = 4;
        let fibonacci_index = 5;

        println!("Test FULL FLOW");
        println!("Step 1: Generate traces");
        let bridge_trace = gen_bridge_trace(log_size, fibonacci_index, 2);
        println!("Bridge trace generated: {} columns", bridge_trace.len());

        let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Fibonacci trace generated: {} columns", fib_trace.len());
        println!("Fibonacci({}) = {}", fibonacci_index, fibonacci_value);

        let is_first_col = gen_is_first_column(log_size);

        let blake_inputs = prepare_blake_inputs(log_size, fibonacci_index);
        let (blake_trace, blake_lookup_data, _blake_round_inputs) =
          gen_blake_trace(log_size, &blake_inputs, fibonacci_index);
        println!("Blake trace generated: {} columns", blake_trace.len());

        println!("Step 2: Setup Prover");
        let config = PcsConfig::default();
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        println!("Step 3: Commit preprocessed trace");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([]);
        tree_builder.extend_evals(vec![is_first_col]);
        tree_builder.extend_evals([]);
        tree_builder.commit(prover_channel);

        println!("Prepocessed trace commited");

        println!("Step 4: Commit main traces");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_trace.clone());
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.extend_evals(blake_trace.clone());
        tree_builder.commit(prover_channel);
        println!("✓ Base traces committed");

        println!("Step 5: Draw interaction elements");
        let index_elements = IndexRelation::draw(prover_channel);
        let round_elements = RoundElements::draw(prover_channel);
        let blake_elements = BlakeElements::draw(prover_channel);


        println!("Step 6: Generate interaction traces");
        let (bridge_interaction_trace, bridge_claimed_sum) =
            gen_bridge_interaction_trace(&bridge_trace, &index_elements);
        println!("✓ Bridge interaction trace: {} columns", bridge_interaction_trace.len());
        println!("  Bridge claimed sum: {:?}", bridge_claimed_sum);

        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(&fib_trace, &index_elements);
        println!("✓ Fibonacci interaction trace: {} columns", fib_interaction_trace.len());
        println!("  Fibonacci claimed sum: {:?}", fib_claimed_sum);

        let (blake_interaction_trace, blake_claimed_sum) = gen_blake_interaction_trace(log_size, &blake_trace, blake_lookup_data, &round_elements, &blake_elements, &index_elements);
        println!("✓ Blake interaction: {} cols, sum: {:?}", blake_interaction_trace.len(), blake_claimed_sum);

        let total_sum = bridge_claimed_sum + fib_claimed_sum + blake_claimed_sum;
        println!("  Total LogUp sum (should be ~0): {:?}", total_sum);

        println!("Step 7: Commit interaction traces");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(bridge_interaction_trace);  
        tree_builder.extend_evals(fib_interaction_trace); 
        tree_builder.extend_evals(blake_interaction_trace);
        tree_builder.commit(prover_channel);
        println!("Interaction traces committed");

        
        println!("Step 8: Create components");
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
        println!("Bridge trace_log_degree_bounds: {:?}", bridge_component.trace_log_degree_bounds());

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
        println!("Fibonacci trace_log_degree_bounds: {:?}", fib_component.trace_log_degree_bounds());

        let blake_component = BlakeSchedulerComponent::new(
            &mut tree_span_provider, 
            BlakeSchedulerEval { log_size, blake_lookup_elements: blake_elements, round_lookup_elements: round_elements, index_relation: index_elements, claimed_sum: blake_claimed_sum },
            blake_claimed_sum
        );

        println!("Step 9: Generate proof");
        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &[&bridge_component, &fib_component, &blake_component],
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");
        println!("Proof size: {} commitments", proof.commitments.len());
        
        println!("Step 10: Verify proof");
        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let bridge_sizes = bridge_component.trace_log_degree_bounds();
        let fib_sizes = fib_component.trace_log_degree_bounds();
        let blake_sizes = blake_component.trace_log_degree_bounds();

        let combined_preprocessed_sizes: Vec<u32> = bridge_sizes[0]
            .iter()
            .chain(fib_sizes[0].iter())
            .chain(blake_sizes[0].iter())
            .copied()
            .collect();

        let combined_base_sizes: Vec<u32> = bridge_sizes[1]
            .iter()
            .chain(fib_sizes[1].iter())
            .chain(blake_sizes[1].iter())
            .copied()
            .collect();

        let combined_interaction_sizes: Vec<u32> = bridge_sizes[2]
            .iter()
            .chain(fib_sizes[2].iter())
            .chain(blake_sizes[2].iter())
            .copied()
            .collect();
        
        commitment_scheme_verifier.commit(proof.commitments[0], &combined_preprocessed_sizes, verifier_channel);
        commitment_scheme_verifier.commit(proof.commitments[1], &combined_base_sizes, verifier_channel);
        commitment_scheme_verifier.commit(proof.commitments[2], &combined_interaction_sizes, verifier_channel);
        
        verify(
            &[&bridge_component, &fib_component, &blake_component],
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("PROOF VERIFIED SUCCESSFULLY!");
    }
    
}

pub fn prepare_blake_inputs(log_size: u32, index: usize) -> Vec<BlakeInput> {
    const STATE_SIZE: usize = 16;
    let n_rows = 1 << log_size;

    // Initialize all rows with default (zero) inputs
    let mut inputs = vec![BlakeInput::default(); n_rows];

    // Blake3 Initial Vector (IV)
    // These are the standard Blake3 IV values
    let blake3_iv: [u32; STATE_SIZE] = [
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
    ];

    // Message to hash: put fibonacci_index in first word, rest zeros
    let mut message = [0u32; STATE_SIZE];
    message[0] = index as u32;

    // Set input for row 0 (we'll hash the index at the first row)
    inputs[0] = BlakeInput {
        v: blake3_iv.map(|val| u32x16::splat(val)),
        m: message.map(|val| u32x16::splat(val)),
    };

    inputs
}