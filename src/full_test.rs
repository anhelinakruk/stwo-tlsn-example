use std::simd::u32x16;
use crate::blake3::scheduler::BlakeInput;

#[cfg(test)]
mod tests {
    use stwo::{core::{channel::Blake2sChannel, pcs::{ PcsConfig}, poly::circle::CanonicCoset, vcs::blake2_merkle::Blake2sMerkleChannel, verifier::verify}, prover::{CommitmentSchemeProver, ComponentProver, backend::simd::SimdBackend, poly::circle::PolyOps, prove}};
    use stwo_constraint_framework::TraceLocationAllocator;
    use itertools::{multiunzip, Itertools};

    use crate::{
        blake3::{
            BlakeComponentsForIntegration, BlakeXorElements, ROUND_LOG_SPLIT, XorAccums, round::{self, RoundElements}, scheduler::{self, BlakeElements}, xor_table
        },
        bridge::{IndexBridgeComponent, IndexBridgeEval, IndexRelation, gen_bridge_interaction_trace, gen_bridge_trace},
        fibonacci::{FibEval, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, is_first_column_id},
        full_test::prepare_blake_inputs
    };

    #[test]
    fn test_full_flow() {
        use stwo::prover::backend::simd::m31::LOG_N_LANES;

        let log_size = 4;
        let fibonacci_index = 5;

        let bridge_trace = gen_bridge_trace(log_size, fibonacci_index, 2);
        println!("Bridge trace: {} columns", bridge_trace.len());

        let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Fibonacci trace: {} columns", fib_trace.len());
        println!("Fibonacci({}) = {}", fibonacci_index, fibonacci_value);

        let is_first_col_fib = gen_is_first_column(log_size);

        let blake_inputs = prepare_blake_inputs(log_size, fibonacci_index);

        let fibonacci_index = 100;
        let (scheduler_trace, scheduler_lookup_data, round_inputs) =
            scheduler::gen_trace(log_size, &blake_inputs, fibonacci_index);
        println!("Blake scheduler trace: {} columns", scheduler_trace.len());

        let mut xor_accums = XorAccums::default();
        let mut rest = &round_inputs[..];
        let (round_traces, round_lookup_data): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.map(|l| {
                let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
                rest = r;
                round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
            }));
        println!("Blake round traces: {} components", round_traces.len());

        let (xor_trace12, xor_lookup_data12) = xor_table::xor12::generate_trace(xor_accums.xor12);
        let (xor_trace9, xor_lookup_data9) = xor_table::xor9::generate_trace(xor_accums.xor9);
        let (xor_trace8, xor_lookup_data8) = xor_table::xor8::generate_trace(xor_accums.xor8);
        let (xor_trace7, xor_lookup_data7) = xor_table::xor7::generate_trace(xor_accums.xor7);
        let (xor_trace4, xor_lookup_data4) = xor_table::xor4::generate_trace(xor_accums.xor4);
        println!("Blake XOR tables: 5 tables generated");

        let config = PcsConfig::default();

        const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
        let log_max_rows = (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
  
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([]); 
        tree_builder.extend_evals(vec![is_first_col_fib.clone()]);  
        tree_builder.extend_evals(
            vec![
                XorTable::new(12, 4, 0).generate_constant_trace(),
                XorTable::new(12, 4, 1).generate_constant_trace(),
                XorTable::new(12, 4, 2).generate_constant_trace(),
                XorTable::new(9, 2, 0).generate_constant_trace(),
                XorTable::new(9, 2, 1).generate_constant_trace(),
                XorTable::new(9, 2, 2).generate_constant_trace(),
                XorTable::new(8, 2, 0).generate_constant_trace(),
                XorTable::new(8, 2, 1).generate_constant_trace(),
                XorTable::new(8, 2, 2).generate_constant_trace(),
                XorTable::new(7, 2, 0).generate_constant_trace(),
                XorTable::new(7, 2, 1).generate_constant_trace(),
                XorTable::new(7, 2, 2).generate_constant_trace(),
                XorTable::new(4, 0, 0).generate_constant_trace(),
                XorTable::new(4, 0, 1).generate_constant_trace(),
                XorTable::new(4, 0, 2).generate_constant_trace(),
            ].into_iter().flatten().collect_vec()
        );
        tree_builder.commit(prover_channel);
        println!("✓ Preprocessed traces committed");

        let mut tree_builder = commitment_scheme.tree_builder();

        let scheduler_trace_for_interaction = scheduler_trace.clone();

        tree_builder.extend_evals(bridge_trace.clone()); 
        tree_builder.extend_evals(fib_trace.clone()); 
        tree_builder.extend_evals(
            vec![scheduler_trace]
                .into_iter()
                .chain(round_traces.into_iter())
                .chain(vec![
                    xor_trace12.clone(),
                    xor_trace9.clone(),
                    xor_trace8.clone(),
                    xor_trace7.clone(),
                    xor_trace4.clone(),
                ])
                .flatten()
                .collect_vec()
        );

        tree_builder.commit(prover_channel);
        println!("Base traces committed");

        let index_elements = IndexRelation::draw(prover_channel);
        let round_elements = RoundElements::draw(prover_channel);
        let blake_elements = BlakeElements::draw(prover_channel);
        let xor_elements = BlakeXorElements::draw(prover_channel);
        println!("All lookup elements drawn");

        let (bridge_interaction_trace, bridge_claimed_sum) =
            gen_bridge_interaction_trace(&bridge_trace, &index_elements);
        println!("Bridge: {} columns, sum = {:?}", bridge_interaction_trace.len(), bridge_claimed_sum);
        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(&fib_trace, &index_elements);
        println!("Fibonacci: {} columns, sum = {:?}", fib_interaction_trace.len(), fib_claimed_sum);
        let (scheduler_interaction_trace, scheduler_claimed_sum) = scheduler::gen_interaction_trace(
            log_size,
            scheduler_lookup_data,
            &round_elements,
            &blake_elements,
            &scheduler_trace_for_interaction,
            &index_elements,
        );
        println!("Blake scheduler: {} columns, sum = {:?}", scheduler_interaction_trace.len(), scheduler_claimed_sum);

        let (round_interaction_traces, round_claimed_sums): (Vec<_>, Vec<_>) = multiunzip(
            ROUND_LOG_SPLIT
                .iter()
                .zip(round_lookup_data)
                .map(|(l, lookup_data)| {
                    round::generate_interaction_trace(
                        log_size + l,
                        lookup_data,
                        &xor_elements,
                        &round_elements,
                    )
                }),
        );
        println!("Blake rounds: {} components", round_interaction_traces.len());

        let (xor_interaction12, xor12_claimed_sum) = xor_table::xor12::generate_interaction_trace(
            xor_lookup_data12,
            &xor_elements.xor12,
        );
        let (xor_interaction9, xor9_claimed_sum) = xor_table::xor9::generate_interaction_trace(
            xor_lookup_data9,
            &xor_elements.xor9,
        );
        let (xor_interaction8, xor8_claimed_sum) = xor_table::xor8::generate_interaction_trace(
            xor_lookup_data8,
            &xor_elements.xor8,
        );
        let (xor_interaction7, xor7_claimed_sum) = xor_table::xor7::generate_interaction_trace(
            xor_lookup_data7,
            &xor_elements.xor7,
        );
        let (xor_interaction4, xor4_claimed_sum) = xor_table::xor4::generate_interaction_trace(
            xor_lookup_data4,
            &xor_elements.xor4,
        );
        println!("Blake XOR tables: 5 interaction traces");

        println!("\n=== CLAIMED SUM BREAKDOWN ===");
        println!("Scheduler:     {:?}", scheduler_claimed_sum);
        for (i, sum) in round_claimed_sums.iter().enumerate() {
            println!("Round {}:        {:?}", i, sum);
        }
        let rounds_total = round_claimed_sums.iter().sum::<stwo::core::fields::qm31::SecureField>();
        println!("Rounds total:  {:?}", rounds_total);
        println!("XOR12:         {:?}", xor12_claimed_sum);
        println!("XOR9:          {:?}", xor9_claimed_sum);
        println!("XOR8:          {:?}", xor8_claimed_sum);
        println!("XOR7:          {:?}", xor7_claimed_sum);
        println!("XOR4:          {:?}", xor4_claimed_sum);

        let blake_total_sum = scheduler_claimed_sum
            + rounds_total
            + xor12_claimed_sum
            + xor9_claimed_sum
            + xor8_claimed_sum
            + xor7_claimed_sum
            + xor4_claimed_sum;

        println!("\n=== COMPONENT TOTALS ===");
        println!("Bridge:        {:?}", bridge_claimed_sum);
        println!("Fibonacci:     {:?}", fib_claimed_sum);
        println!("Blake3 total:  {:?}", blake_total_sum);

        let total_sum = bridge_claimed_sum + fib_claimed_sum + blake_total_sum;
        println!("\n=== FINAL ===");
        println!("TOTAL sum:     {:?}", total_sum);
        println!("Expected:      0 (for valid proof)");

        println!("Step 8: Commit interaction traces");
        let mut tree_builder = commitment_scheme.tree_builder();

        tree_builder.extend_evals(bridge_interaction_trace); 
        tree_builder.extend_evals(fib_interaction_trace); 
        tree_builder.extend_evals(
            vec![scheduler_interaction_trace]
                .into_iter()
                .chain(round_interaction_traces.into_iter())
                .chain(vec![
                    xor_interaction12,
                    xor_interaction9,
                    xor_interaction8,
                    xor_interaction7,
                    xor_interaction4,
                ])
                .flatten()
                .collect_vec()
        );

        tree_builder.commit(prover_channel);
        println!("✓ Interaction traces committed");

        println!("\n========== STEP 9: Create components ==========");

        use crate::blake3::preprocessed_columns::XorTable;
        let mut all_preprocessed_ids = vec![];

        all_preprocessed_ids.push(is_first_column_id(log_size));

        all_preprocessed_ids.push(XorTable::new(12, 4, 0).id());
        all_preprocessed_ids.push(XorTable::new(12, 4, 1).id());
        all_preprocessed_ids.push(XorTable::new(12, 4, 2).id());
        all_preprocessed_ids.push(XorTable::new(9, 2, 0).id());
        all_preprocessed_ids.push(XorTable::new(9, 2, 1).id());
        all_preprocessed_ids.push(XorTable::new(9, 2, 2).id());
        all_preprocessed_ids.push(XorTable::new(8, 2, 0).id());
        all_preprocessed_ids.push(XorTable::new(8, 2, 1).id());
        all_preprocessed_ids.push(XorTable::new(8, 2, 2).id());
        all_preprocessed_ids.push(XorTable::new(7, 2, 0).id());
        all_preprocessed_ids.push(XorTable::new(7, 2, 1).id());
        all_preprocessed_ids.push(XorTable::new(7, 2, 2).id());
        all_preprocessed_ids.push(XorTable::new(4, 0, 0).id());
        all_preprocessed_ids.push(XorTable::new(4, 0, 1).id());
        all_preprocessed_ids.push(XorTable::new(4, 0, 2).id());

        let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_ids);

        let bridge_component = IndexBridgeComponent::new(
            &mut tree_span_provider,
            IndexBridgeEval {
                log_n_rows: log_size,
                index_value: fibonacci_index as usize,
                index_relation: index_elements.clone(),
            },
            bridge_claimed_sum,
        );
        println!("Bridge component");

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
        println!("Fibonacci component");
        let blake_components = BlakeComponentsForIntegration::new(
            log_size,
            &mut tree_span_provider,
            &blake_elements,
            &round_elements,
            &xor_elements,
            &index_elements,
            fibonacci_index as u32,
            is_first_column_id(log_size),  
            scheduler_claimed_sum,
            &round_claimed_sums,
            xor12_claimed_sum,
            xor9_claimed_sum,
            xor8_claimed_sum,
            xor7_claimed_sum,
            xor4_claimed_sum,
        );
        println!("Blake3 components (scheduler + {} rounds + 5 XOR tables)", ROUND_LOG_SPLIT.len());

        println!("Step 10: Generate proof");
        let mut all_components: Vec<&dyn ComponentProver<SimdBackend>> = vec![&bridge_component, &fib_component];
        all_components.push(&blake_components.scheduler_component);
        for comp in &blake_components.round_components {
            all_components.push(comp);
        }
        all_components.push(&blake_components.xor12);
        all_components.push(&blake_components.xor9);
        all_components.push(&blake_components.xor8);
        all_components.push(&blake_components.xor7);
        all_components.push(&blake_components.xor4);

        println!("Total components: {}", all_components.len());

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &all_components,
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");
        println!("Proof size: {} commitments", proof.commitments.len());

        println!("Proof generation passed");
    }
    
}

pub fn prepare_blake_inputs(log_size: u32, index: usize) -> Vec<BlakeInput> {
    const STATE_SIZE: usize = 16;
    let n_rows = 1 << log_size;

    // Initialize all rows with default (zero) inputs
    let mut inputs = vec![BlakeInput::default(); n_rows];

    // Blake3 Initial Vector (IV) - standard 8 values
    const BLAKE3_IV: [u32; 8] = [
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
    ];

    // Build initial state for Blake3 compression:
    // state[0..8]   = chaining value (CV) = IV for first block
    // state[8..12]  = IV[0..4] (used as constants)
    // state[12]     = counter_low = 0
    // state[13]     = counter_high = 0
    // state[14]     = block_len = 4 (we're hashing 4 bytes: the u32 index)
    // state[15]     = flags = 0b1011 (CHUNK_START | CHUNK_END | ROOT)
    let mut initial_state = [0u32; STATE_SIZE];
    initial_state[0..8].copy_from_slice(&BLAKE3_IV);
    initial_state[8..12].copy_from_slice(&BLAKE3_IV[0..4]);
    initial_state[12] = 0;  // counter_low
    initial_state[13] = 0;  // counter_high
    initial_state[14] = 4;  // block_len (4 bytes for u32)
    initial_state[15] = 0b1011;  // flags: CHUNK_START | CHUNK_END | ROOT

    // Message to hash: put index in first word, rest zeros (padding)
    let mut message = [0u32; STATE_SIZE];
    message[0] = index as u32;

    // Set input for row 0 (we'll hash the index at the first row)
    inputs[0] = BlakeInput {
        v: initial_state.map(|val| u32x16::splat(val)),
        m: message.map(|val| u32x16::splat(val)),
    };

    inputs
}