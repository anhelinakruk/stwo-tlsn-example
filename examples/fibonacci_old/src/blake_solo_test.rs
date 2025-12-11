#[cfg(test)]
mod tests {
    use itertools::{Itertools, chain, multiunzip};
    use num_traits::Zero;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::{CommitmentSchemeProver, backend::simd::SimdBackend, prove};

    use crate::blake3::{
        BlakeXorElements, ROUND_LOG_SPLIT, XorAccums,
        preprocessed_columns::XorTable,
        round::{self, RoundElements},
        scheduler::{self, BlakeElements},
        xor_table,
    };
    use crate::bridge::IndexRelation;

    const LOG_N_LANES: u32 = 4;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn preprocessed_columns(
        _log_size: u32,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        vec![
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
    }

    #[test]
    fn test_blake3_solo_exact_copy_from_air() {
        let log_size = 10u32;
        let config = PcsConfig::default();

        assert!(log_size >= LOG_N_LANES);

        // Precompute twiddles
        const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
        let log_max_rows =
            (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        use std::simd::u32x16;
        let blake_inputs = (0..(1 << (log_size - LOG_N_LANES)))
            .map(|i| {
                let v = [u32x16::from_array(std::array::from_fn(|j| (i + 2 * j) as u32)); 16];
                let m = [u32x16::from_array(std::array::from_fn(|j| (i + 2 * j + 1) as u32)); 16];
                crate::blake3::scheduler::BlakeInput { v, m }
            })
            .collect_vec();

        // Setup protocol
        let channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        // Preprocessed columns
        let mut tree_builder = commitment_scheme.tree_builder();
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
        tree_builder.commit(channel);

        // Scheduler
        let fibonacci_index = 100;
        let (scheduler_trace, scheduler_lookup_data, round_inputs) =
            scheduler::gen_trace(log_size, &blake_inputs, fibonacci_index);

        // Rounds
        let mut xor_accums = XorAccums::default();
        let mut rest = &round_inputs[..];
        let (round_traces, round_lookup_data): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.map(|l| {
                let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
                rest = r;
                round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
            }));

        // XOR tables
        let (xor_trace12, xor_lookup_data12) = xor_table::xor12::generate_trace(xor_accums.xor12);
        let (xor_trace9, xor_lookup_data9) = xor_table::xor9::generate_trace(xor_accums.xor9);
        let (xor_trace8, xor_lookup_data8) = xor_table::xor8::generate_trace(xor_accums.xor8);
        let (xor_trace7, xor_lookup_data7) = xor_table::xor7::generate_trace(xor_accums.xor7);
        let (xor_trace4, xor_lookup_data4) = xor_table::xor4::generate_trace(xor_accums.xor4);

        // Clone scheduler_trace for interaction generation
        let scheduler_trace_for_interaction = scheduler_trace.clone();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(
            chain![
                scheduler_trace,
                round_traces.into_iter().flatten(),
                xor_trace12,
                xor_trace9,
                xor_trace8,
                xor_trace7,
                xor_trace4,
            ]
            .collect_vec(),
        );
        tree_builder.commit(channel);

        // Draw interaction elements
        let index_relation = IndexRelation::draw(channel); // Draw from channel, not dummy
        let round_elements = RoundElements::draw(channel);
        let blake_elements = BlakeElements::draw(channel);
        let xor_elements = BlakeXorElements::draw(channel);

        let (scheduler_interaction_trace, scheduler_claimed_sum) = scheduler::gen_interaction_trace(
            log_size,
            scheduler_lookup_data,
            &round_elements,
            &blake_elements,
            &scheduler_trace_for_interaction,
            &index_relation,
        );

        println!("DEBUG: scheduler_claimed_sum = {:?}", scheduler_claimed_sum);

        let (round_traces, round_claimed_sums): (Vec<_>, Vec<_>) = multiunzip(
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

        let (xor_interaction12, xor12_claimed_sum) =
            xor_table::xor12::generate_interaction_trace(xor_lookup_data12, &xor_elements.xor12);
        let (xor_interaction9, xor9_claimed_sum) =
            xor_table::xor9::generate_interaction_trace(xor_lookup_data9, &xor_elements.xor9);
        let (xor_interaction8, xor8_claimed_sum) =
            xor_table::xor8::generate_interaction_trace(xor_lookup_data8, &xor_elements.xor8);
        let (xor_interaction7, xor7_claimed_sum) =
            xor_table::xor7::generate_interaction_trace(xor_lookup_data7, &xor_elements.xor7);
        let (xor_interaction4, xor4_claimed_sum) =
            xor_table::xor4::generate_interaction_trace(xor_lookup_data4, &xor_elements.xor4);

        println!("DEBUG: round_claimed_sums = {:?}", round_claimed_sums);
        println!("DEBUG: xor12_claimed_sum = {:?}", xor12_claimed_sum);
        println!("DEBUG: xor9_claimed_sum = {:?}", xor9_claimed_sum);
        println!("DEBUG: xor8_claimed_sum = {:?}", xor8_claimed_sum);
        println!("DEBUG: xor7_claimed_sum = {:?}", xor7_claimed_sum);
        println!("DEBUG: xor4_claimed_sum = {:?}", xor4_claimed_sum);

        // Calculate total sum
        use stwo::core::fields::qm31::QM31;
        let total_sum = scheduler_claimed_sum
            + round_claimed_sums
                .iter()
                .fold(QM31::zero(), |acc, &x| acc + x)
            + xor12_claimed_sum
            + xor9_claimed_sum
            + xor8_claimed_sum
            + xor7_claimed_sum
            + xor4_claimed_sum;
        println!("DEBUG: TOTAL claimed sum = {:?}", total_sum);
        println!("DEBUG: Should be ZERO for valid proof!");

        // Interaction trace commitment - EXACTLY like air.rs
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(
            chain![
                scheduler_interaction_trace,
                round_traces.into_iter().flatten(),
                xor_interaction12,
                xor_interaction9,
                xor_interaction8,
                xor_interaction7,
                xor_interaction4,
            ]
            .collect_vec(),
        );
        tree_builder.commit(channel);

        // Prove - using BlakeComponentsForIntegration
        let tree_span_provider = &mut TraceLocationAllocator::new_with_preprocessed_columns(
            &preprocessed_columns(log_size),
        );

        // Try using regular BlakeComponents instead
        use crate::blake3::{AllElements, BlakeComponents, BlakeStatement0, BlakeStatement1};
        let components = BlakeComponents::new(
            &BlakeStatement0 { log_size },
            &AllElements {
                blake_elements: blake_elements.clone(),
                round_elements: round_elements.clone(),
                xor_elements: xor_elements.clone(),
            },
            &BlakeStatement1 {
                scheduler_claimed_sum,
                round_claimed_sums: round_claimed_sums.to_vec(),
                xor12_claimed_sum,
                xor9_claimed_sum,
                xor8_claimed_sum,
                xor7_claimed_sum,
                xor4_claimed_sum,
            },
            &index_relation,
            fibonacci_index,
        );

        let component_provers = components.component_provers();

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &component_provers,
            channel,
            commitment_scheme,
        )
        .unwrap();

        println!("BLAKE3 SOLO PROOF GENERATED!");
        println!("Proof commitments: {}", proof.commitments.len());
    }
}
