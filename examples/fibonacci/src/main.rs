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
    use itertools::{Itertools, chain};
    use num_traits::Zero;
    use stwo::core::{air::Component, channel::MerkleChannel, fields::qm31::SecureField, pcs::CommitmentSchemeVerifier, poly::circle::CanonicCoset, proof::StarkProof, vcs::{MerkleHasher, blake2_merkle::Blake2sMerkleChannel}, verifier::{VerificationError, verify}};
    use stwo_constraint_framework::{TraceLocationAllocator, Relation};

    use crate::{blake3::{AllElements, BlakeComponentsForIntegration, BlakeStatement0, BlakeStatement1}, fibonacci::{
        FibComponent, FibEval, FibStatement0, FibStatement1, ValueRelation, FibPublicInputRelation, FibPublicOutputRelation, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, gen_is_target_column, is_first_column_id, is_target_column_id
    }};

    #[test]
    fn test_fibonacci_blake_prove_verify() {
        use itertools::{Itertools, chain, multiunzip};
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::pcs::PcsConfig;
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
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

        let fib_statement = FibStatement0 {
            log_size,
            fibonacci_index,
            initial_a: 0,
            initial_b: 1,
            expected_value: fibonacci_value,
        };
        fib_statement.mix_into(prover_channel);

        let blake_stmt0 = BlakeStatement0 { log_size };
        blake_stmt0.mix_into(prover_channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.extend_evals(
            chain![
                blake_scheduler_trace.clone(),
                blake_round_traces.into_iter().flatten(),
                blake_xor_trace12,
                blake_xor_trace9,
                blake_xor_trace8,
                blake_xor_trace7,
                blake_xor_trace4,
            ]
            .collect_vec(),
        );
        tree_builder.commit(prover_channel);
        println!("Base trace committed");

        let all_elements = AllElements::draw(prover_channel);
        let value_relation = ValueRelation::draw(prover_channel);
        let public_input_relation = FibPublicInputRelation::draw(prover_channel);
        let public_output_relation = FibPublicOutputRelation::draw(prover_channel);
        println!("Challenges drawn");

        let fib_preprocessed = vec![fib_is_first_col.clone(), fib_is_target_col.clone()];
        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(
                &fib_trace,
                &fib_preprocessed,
                &value_relation,
                &public_input_relation,
                &public_output_relation,
            );
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

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(
            chain![
                fib_interaction_trace,
                blake_scheduler_interaction_trace,
                blake_round_interaction_traces.into_iter().flatten(),
                blake_xor_interaction_trace12,
                blake_xor_interaction_trace9,
                blake_xor_interaction_trace8,
                blake_xor_interaction_trace7,
                blake_xor_interaction_trace4
            ]
            .collect_vec(),
        );

        let fibonacci_stmt1 = FibStatement1 {
            fib_claimed_sum: fib_claimed_sum,
        };
        fibonacci_stmt1.mix_into(prover_channel);

        let stmt1 = BlakeStatement1 {
            scheduler_claimed_sum: blake_scheduler_claimed_sum,
            round_claimed_sums: blake_round_claimed_sums.clone(),
            xor12_claimed_sum: blake_xor_claimed_sum12,
            xor9_claimed_sum: blake_xor_claimed_sum9,
            xor8_claimed_sum: blake_xor_claimed_sum8,
            xor7_claimed_sum: blake_xor_claimed_sum7,
            xor4_claimed_sum: blake_xor_claimed_sum4
        };
        stmt1.mix_into(prover_channel);
        tree_builder.commit(prover_channel);
        println!("Interaction trace committed");

        let all_preprocessed_columns: Vec<_> = chain![
            [is_first_column_id(log_size), is_target_column_id(log_size)],
            [
                scheduler::is_first_column_id(log_size),
                XorTable::new(12, 4, 0).id(),
                XorTable::new(12, 4, 1).id(),
                XorTable::new(12, 4, 2).id(),
                XorTable::new(9, 2, 0).id(),
                XorTable::new(9, 2, 1).id(),
                XorTable::new(9, 2, 2).id(),
                XorTable::new(8, 2, 0).id(),
                XorTable::new(8, 2, 1).id(),
                XorTable::new(8, 2, 2).id(),
                XorTable::new(7, 2, 0).id(),
                XorTable::new(7, 2, 1).id(),
                XorTable::new(7, 2, 2).id(),
                XorTable::new(4, 0, 0).id(),
                XorTable::new(4, 0, 1).id(),
                XorTable::new(4, 0, 2).id(),
            ]
        ]
        .collect();

        let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);

        let fib_component = FibComponent::new(
            &mut tree_span_provider,
            FibEval {
                log_n_rows: log_size,
                is_first_id: is_first_column_id(log_size),
                is_target_id: is_target_column_id(log_size),
                value_relation: value_relation.clone(),
                public_input_relation: public_input_relation.clone(),
                public_output_relation: public_output_relation.clone(),
            },
            fib_claimed_sum,
        );

        let blake_components = BlakeComponentsForIntegration::new(
            &mut tree_span_provider,
            &all_elements,
            &value_relation,
            &blake_stmt0,
            &stmt1,
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

        let proof_data = Proof {
            fib_stmt0: fib_statement.clone(),
            fib_stmt1: fibonacci_stmt1.clone(),
            blake_stmt0: blake_stmt0.clone(),
            blake_stmt1: stmt1.clone(),
            stark_proof: proof.clone(),
        };

        let proof_json = serde_json::to_string_pretty(&proof_data)
            .expect("Failed to serialize proof");
        std::fs::write("fibonacci_blake_proof.json", &proof_json)
            .expect("Failed to write proof to file");
        println!("Proof saved to fibonacci_blake_proof.json");

        let proof_binary = bincode::serialize(&proof_data)
            .expect("Failed to serialize proof to binary");
        std::fs::write("fibonacci_blake_proof.bin", &proof_binary)
            .expect("Failed to write binary proof to file");
        println!("Binary proof saved to fibonacci_blake_proof.bin ({} bytes)", proof_binary.len());

        // Verify
        let verify = verify_proof::<Blake2sMerkleChannel>(Proof { fib_stmt0: fib_statement, fib_stmt1: fibonacci_stmt1, blake_stmt0, blake_stmt1: stmt1, stark_proof: proof });
        verify.unwrap()
    }

    #[derive(Clone, serde::Serialize, serde::Deserialize)]
    pub struct Proof<H: MerkleHasher> {
        fib_stmt0: FibStatement0,
        fib_stmt1: FibStatement1,
        blake_stmt0: BlakeStatement0,
        blake_stmt1: BlakeStatement1,
        stark_proof: StarkProof<H>,
    }

    fn verify_proof<MC: MerkleChannel>(Proof {
        fib_stmt0,
        fib_stmt1,
        blake_stmt0,
        blake_stmt1,
        stark_proof,
    }: Proof<MC::H>,) -> Result<(), VerificationError> {
        let channel = &mut MC::C::default();
        const REQUIRED_SECURITY_BITS: u32 = 5;
        assert!(stark_proof.config.security_bits() >= REQUIRED_SECURITY_BITS);
        let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);

        let fib_log_sizes = fib_stmt0.log_sizes();
        let blake_log_sizes = blake_stmt0.log_sizes();

        let combined_preprocessed_sizes: Vec<u32> = fib_log_sizes[0]
            .iter()
            .chain(blake_log_sizes[0].iter())
            .copied()
            .collect();

        let combined_base_sizes: Vec<u32> = fib_log_sizes[1]
            .iter()
            .chain(blake_log_sizes[1].iter())
            .copied()
            .collect();

        let combined_interaction_sizes: Vec<u32> = fib_log_sizes[2]
            .iter()
            .chain(blake_log_sizes[2].iter())
            .copied()
            .collect();

        commitment_scheme.commit(stark_proof.commitments[0], &combined_preprocessed_sizes, channel);

        fib_stmt0.mix_into(channel);
        blake_stmt0.mix_into(channel);
        commitment_scheme.commit(stark_proof.commitments[1], &combined_base_sizes, channel);

        let all_elements = AllElements::draw(channel);
        let value_relation = ValueRelation::draw(channel);
        let public_input_relation = FibPublicInputRelation::draw(channel);
        let public_output_relation = FibPublicOutputRelation::draw(channel);

        fib_stmt1.mix_into(channel);
        blake_stmt1.mix_into(channel);
        commitment_scheme.commit(stark_proof.commitments[2], &combined_interaction_sizes, channel);

        use crate::blake3::preprocessed_columns::XorTable as XorT;
        let all_preprocessed_columns: Vec<_> = chain![
            [is_first_column_id(fib_stmt0.log_size), is_target_column_id(fib_stmt0.log_size)],
            [
                crate::blake3::scheduler::is_first_column_id(fib_stmt0.log_size),
                XorT::new(12, 4, 0).id(),
                XorT::new(12, 4, 1).id(),
                XorT::new(12, 4, 2).id(),
                XorT::new(9, 2, 0).id(),
                XorT::new(9, 2, 1).id(),
                XorT::new(9, 2, 2).id(),
                XorT::new(8, 2, 0).id(),
                XorT::new(8, 2, 1).id(),
                XorT::new(8, 2, 2).id(),
                XorT::new(7, 2, 0).id(),
                XorT::new(7, 2, 1).id(),
                XorT::new(7, 2, 2).id(),
                XorT::new(4, 0, 0).id(),
                XorT::new(4, 0, 1).id(),
                XorT::new(4, 0, 2).id(),
            ]
        ]
        .collect();

        let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);
        let fib_component = FibComponent::new(
            &mut tree_span_provider,
            FibEval {
                log_n_rows: fib_stmt0.log_size,
                is_first_id: is_first_column_id(fib_stmt0.log_size),
                is_target_id: is_target_column_id(fib_stmt0.log_size),
                value_relation: value_relation.clone(),
                public_input_relation: public_input_relation.clone(),
                public_output_relation: public_output_relation.clone(),
            },
            fib_stmt1.fib_claimed_sum,
        );
        let blake_components = BlakeComponentsForIntegration::new(
            &mut tree_span_provider,
            &all_elements,
            &value_relation,
            &blake_stmt0,
            &blake_stmt1
        );
        println!("Components created");

        let mut claimed_sum = fib_stmt1.fib_claimed_sum
            + blake_stmt1.scheduler_claimed_sum
            + blake_stmt1.round_claimed_sums.iter().sum::<SecureField>()
            + blake_stmt1.xor12_claimed_sum
            + blake_stmt1.xor9_claimed_sum
            + blake_stmt1.xor8_claimed_sum
            + blake_stmt1.xor7_claimed_sum
            + blake_stmt1.xor4_claimed_sum;

        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::FieldExpOps;

        let initial_denom: SecureField = public_input_relation.combine(&[
            SecureField::from(BaseField::from(fib_stmt0.initial_a)),
            SecureField::from(BaseField::from(fib_stmt0.initial_b)),
        ]);
        claimed_sum += initial_denom.inverse();

        let expected_denom: SecureField = public_output_relation.combine(&[
            SecureField::from(BaseField::from(fib_stmt0.expected_value)),
        ]);
        claimed_sum += expected_denom.inverse();

        assert_eq!(claimed_sum, SecureField::zero());

        let all_components_for_verify = chain![
            [&fib_component as &dyn Component],
            blake_components.as_components_vec()
        ]
        .collect_vec();

        verify(
            &all_components_for_verify,
            channel,
            commitment_scheme,
            stark_proof,
        )
    }

    #[test]
    fn test_load_and_verify_proof_from_file() {
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleHasher;

        // Load proof from binary file
        let proof_bytes = std::fs::read("fibonacci_blake_proof.bin")
            .expect("Failed to read proof file. Run test_fibonacci_blake_prove_verify first to generate it.");

        let proof: Proof<Blake2sMerkleHasher> = bincode::deserialize(&proof_bytes)
            .expect("Failed to deserialize proof");

        println!("✅ Proof loaded from file");
        println!("   Fibonacci index (from proof): {}", proof.fib_stmt0.fibonacci_index);
        println!("   Log size: {}", proof.fib_stmt0.log_size);

        // Verify the proof
        let result = verify_proof::<Blake2sMerkleChannel>(proof);

        match result {
            Ok(_) => println!("✅ Proof verification PASSED"),
            Err(e) => {
                println!("❌ Proof verification FAILED: {:?}", e);
                panic!("Verification failed: {:?}", e);
            }
        }
    }
}
