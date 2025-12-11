#![feature(portable_simd)]
#![feature(array_chunks)]
#![feature(iter_array_chunks)]

pub mod blake3;
pub mod fibonacci;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use stwo::core::poly::circle::CanonicCoset;

    use crate::fibonacci::{
        FibComponent, FibEval, ValueRelation, gen_fib_interaction_trace, gen_fib_trace,
        gen_is_first_column, gen_is_target_column, is_first_column_id, is_target_column_id,
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
        tree_builder.extend_evals([is_first_col.clone(), is_target_col.clone()]);
        tree_builder.commit(prover_channel);
        println!("Preprocessed trace committed");

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.commit(prover_channel);
        println!("Base trace committed");

        let value_elements = ValueRelation::draw(prover_channel);
        println!("Challenge drawn for ValueRelation");

        let preprocessed = vec![is_first_col.clone(), is_target_col.clone()];
        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(&fib_trace, &preprocessed, &value_elements);
        println!("Fibonacci claimed_sum: {:?}", fib_claimed_sum);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_interaction_trace);
        tree_builder.commit(prover_channel);
        println!("Interaction trace committed");

        let fib_component = FibComponent::new(
            &mut TraceLocationAllocator::default(),
            FibEval {
                log_n_rows: log_size,
                is_first_id: is_first_column_id(log_size),
                is_target_id: is_target_column_id(log_size),
                value_relation: value_elements,
            },
            fib_claimed_sum,
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
        commitment_scheme_verifier.commit(proof.commitments[2], &sizes[2], verifier_channel);

        verify(
            &[&fib_component],
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("PROOF VERIFIED SUCCESSFULLY!");
    }

    #[test]
    fn test_fibonacci_blake_prove_verify() {
        use itertools::{Itertools, chain, multiunzip};
        use num_traits::Zero;
        use stwo::core::air::Component;
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::fields::qm31::SecureField;
        use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
        use stwo::core::verifier::verify;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::backend::simd::m31::LOG_N_LANES;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::{CommitmentSchemeProver, prove};
        use stwo_constraint_framework::TraceLocationAllocator;

        use crate::blake3::air::{AllElements, BlakeStatement0};
        use crate::blake3::preprocessed_columns::XorTable;
        use crate::blake3::{ROUND_LOG_SPLIT, XorAccums, round, scheduler, xor_table};

        let log_size = 4;
        let fibonacci_index = 8;

        let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Fibonacci trace generated: {} columns", fib_trace.len());
        println!(
            "Fibonacci value at index {}: {}",
            fibonacci_index, fibonacci_value
        );

        let fib_is_first_col = gen_is_first_column(log_size);
        let fib_is_target_col = gen_is_target_column(log_size, fibonacci_index);

        let blake_is_first_col = scheduler::gen_is_first_column(log_size);

        let (blake_scheduler_trace, blake_scheduler_lookup_data, blake_round_inputs) =
            scheduler::gen_trace(log_size, fibonacci_value);
        println!(
            "Blake scheduler trace generated: {} columns",
            blake_scheduler_trace.len()
        );

        let mut xor_accums = XorAccums::default();
        let mut rest = &blake_round_inputs[..];
        let (blake_round_traces, blake_round_lookup_data): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.map(|l| {
                let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
                rest = r;
                round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
            }));

        let (blake_xor_trace12, blake_xor_lookup_data12) =
            xor_table::xor12::generate_trace(xor_accums.xor12);
        let (blake_xor_trace9, blake_xor_lookup_data9) =
            xor_table::xor9::generate_trace(xor_accums.xor9);
        let (blake_xor_trace8, blake_xor_lookup_data8) =
            xor_table::xor8::generate_trace(xor_accums.xor8);
        let (blake_xor_trace7, blake_xor_lookup_data7) =
            xor_table::xor7::generate_trace(xor_accums.xor7);
        let (blake_xor_trace4, blake_xor_lookup_data4) =
            xor_table::xor4::generate_trace(xor_accums.xor4);

        let config = PcsConfig::default();
        const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
        let log_max_rows =
            (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([fib_is_first_col.clone(), fib_is_target_col.clone()]);
        tree_builder.extend_evals([blake_is_first_col.clone()]);
        tree_builder.extend_evals(
            chain![
                XorTable::new(12, 4, 0).generate_constant_trace(),
                XorTable::new(9, 2, 0).generate_constant_trace(),
                XorTable::new(8, 2, 0).generate_constant_trace(),
                XorTable::new(7, 2, 0).generate_constant_trace(),
                XorTable::new(4, 0, 0).generate_constant_trace(),
            ]
            .collect_vec(),
        );
        tree_builder.commit(prover_channel);
        println!("Preprocessed trace committed");

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.extend_evals(blake_scheduler_trace.clone());
        for round_trace in &blake_round_traces {
            tree_builder.extend_evals(round_trace.clone());
        }
        tree_builder.extend_evals(blake_xor_trace12.clone());
        tree_builder.extend_evals(blake_xor_trace9.clone());
        tree_builder.extend_evals(blake_xor_trace8.clone());
        tree_builder.extend_evals(blake_xor_trace7.clone());
        tree_builder.extend_evals(blake_xor_trace4.clone());
        tree_builder.commit(prover_channel);
        println!("Base trace committed");

        let all_elements = AllElements::draw(prover_channel);
        let value_relation = ValueRelation::draw(prover_channel);
        println!("Challenges drawn");

        let fib_preprocessed = vec![fib_is_first_col.clone(), fib_is_target_col.clone()];
        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(&fib_trace, &fib_preprocessed, &value_relation);
        println!("Fibonacci claimed sum: {:?}", fib_claimed_sum);

        let blake_preprocessed = vec![blake_is_first_col.clone()];
        let (blake_scheduler_interaction_trace, blake_scheduler_claimed_sum) =
            scheduler::gen_interaction_trace(
                log_size,
                blake_scheduler_lookup_data,
                &all_elements.round_elements,
                &all_elements.blake_elements,
                &blake_scheduler_trace,
                &blake_preprocessed,
                &value_relation,
            );
        println!(
            "Blake scheduler claimed sum: {:?}",
            blake_scheduler_claimed_sum
        );

        let (blake_round_interaction_traces, blake_round_claimed_sums): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.iter().zip(blake_round_lookup_data).map(
                |(l, lookup_data)| {
                    round::generate_interaction_trace(
                        log_size + l,
                        lookup_data,
                        &all_elements.xor_elements,
                        &all_elements.round_elements,
                    )
                },
            ));

        let (blake_xor_interaction_trace12, blake_xor_claimed_sum12) =
            xor_table::xor12::generate_interaction_trace(
                blake_xor_lookup_data12,
                &all_elements.xor_elements.xor12,
            );
        let (blake_xor_interaction_trace9, blake_xor_claimed_sum9) =
            xor_table::xor9::generate_interaction_trace(
                blake_xor_lookup_data9,
                &all_elements.xor_elements.xor9,
            );
        let (blake_xor_interaction_trace8, blake_xor_claimed_sum8) =
            xor_table::xor8::generate_interaction_trace(
                blake_xor_lookup_data8,
                &all_elements.xor_elements.xor8,
            );
        let (blake_xor_interaction_trace7, blake_xor_claimed_sum7) =
            xor_table::xor7::generate_interaction_trace(
                blake_xor_lookup_data7,
                &all_elements.xor_elements.xor7,
            );
        let (blake_xor_interaction_trace4, blake_xor_claimed_sum4) =
            xor_table::xor4::generate_interaction_trace(
                blake_xor_lookup_data4,
                &all_elements.xor_elements.xor4,
            );

        println!("Fibonacci claimed sum:        {:?}", fib_claimed_sum);
        println!(
            "Blake scheduler claimed sum:  {:?}",
            blake_scheduler_claimed_sum
        );

        let rounds_sum = blake_round_claimed_sums.iter().sum::<SecureField>();
        println!("Blake rounds total:           {:?}", rounds_sum);

        println!(
            "Blake XOR12 claimed:          {:?}",
            blake_xor_claimed_sum12
        );
        println!("Blake XOR9 claimed:           {:?}", blake_xor_claimed_sum9);
        println!("Blake XOR8 claimed:           {:?}", blake_xor_claimed_sum8);
        println!("Blake XOR7 claimed:           {:?}", blake_xor_claimed_sum7);
        println!("Blake XOR4 claimed:           {:?}", blake_xor_claimed_sum4);

        let total_sum = fib_claimed_sum
            + blake_scheduler_claimed_sum
            + rounds_sum
            + blake_xor_claimed_sum12
            + blake_xor_claimed_sum9
            + blake_xor_claimed_sum8
            + blake_xor_claimed_sum7
            + blake_xor_claimed_sum4;
        println!("\nTOTAL LogUp sum: {:?}", total_sum);

        assert_eq!(
            total_sum,
            SecureField::zero(),
            "LogUp sum must be zero! Got: {:?}",
            total_sum
        );
        println!("LogUp sum verified to be zero\n");

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_interaction_trace);
        tree_builder.extend_evals(blake_scheduler_interaction_trace);
        for round_interaction_trace in &blake_round_interaction_traces {
            tree_builder.extend_evals(round_interaction_trace.clone());
        }
        tree_builder.extend_evals(blake_xor_interaction_trace12);
        tree_builder.extend_evals(blake_xor_interaction_trace9);
        tree_builder.extend_evals(blake_xor_interaction_trace8);
        tree_builder.extend_evals(blake_xor_interaction_trace7);
        tree_builder.extend_evals(blake_xor_interaction_trace4);
        tree_builder.commit(prover_channel);
        println!("Interaction trace committed");

        let mut tree_span_provider = TraceLocationAllocator::default();

        let fib_component = FibComponent::new(
            &mut tree_span_provider,
            FibEval {
                log_n_rows: log_size,
                is_first_id: is_first_column_id(log_size),
                is_target_id: is_target_column_id(log_size),
                value_relation: value_relation.clone(),
            },
            fib_claimed_sum,
        );

        use crate::blake3::air::BlakeComponentsForIntegration;
        let blake_components = BlakeComponentsForIntegration::new(
            log_size,
            &mut tree_span_provider,
            &all_elements.blake_elements,
            &all_elements.round_elements,
            &all_elements.xor_elements,
            &value_relation,
            blake_scheduler_claimed_sum,
            &blake_round_claimed_sums,
            blake_xor_claimed_sum12,
            blake_xor_claimed_sum9,
            blake_xor_claimed_sum8,
            blake_xor_claimed_sum7,
            blake_xor_claimed_sum4,
        );
        println!("Components created");

        // Prove
        let all_component_provers = chain![
            [&fib_component as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.scheduler_component
                as &dyn stwo::prover::ComponentProver<SimdBackend>],
            blake_components
                .round_components
                .iter()
                .map(|c| c as &dyn stwo::prover::ComponentProver<SimdBackend>),
            [&blake_components.xor12 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor9 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor8 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor7 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor4 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        ]
        .collect_vec();

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &all_component_provers,
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");

        // Verify
        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let fib_sizes = fib_component.trace_log_degree_bounds();
        let blake_stmt0_for_sizes = BlakeStatement0 { log_size };
        let blake_sizes = blake_stmt0_for_sizes.log_sizes();

        let combined_preprocessed_sizes: Vec<u32> = fib_sizes[0]
            .iter()
            .chain(blake_sizes[0].iter())
            .copied()
            .collect();
        let combined_base_sizes: Vec<u32> = fib_sizes[1]
            .iter()
            .chain(blake_sizes[1].iter())
            .copied()
            .collect();
        let combined_interaction_sizes: Vec<u32> = fib_sizes[2]
            .iter()
            .chain(blake_sizes[2].iter())
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

        let all_components_for_verify = chain![
            [&fib_component as &dyn Component],
            blake_components.as_components_vec()
        ]
        .collect_vec();

        verify(
            &all_components_for_verify,
            verifier_channel,
            commitment_scheme_verifier,
            proof,
        )
        .expect("Verification failed");

        println!("PROOF VERIFIED SUCCESSFULLY!");
    }
}
