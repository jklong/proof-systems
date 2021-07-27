use algebra::{
    pasta::{
        fp::Fp,
        pallas::Affine as Other,
        vesta::{Affine, VestaParameters},
    },
    UniformRand, Zero,
};
use array_init::array_init;
use colored::Colorize;
use commitment_dlog::{
    commitment::{b_poly_coefficients, ceil_log2, CommitmentCurve},
    srs::{endos, SRS},
};
use ff_fft::DensePolynomial;
use groupmap::GroupMap;
use oracle::{
    poseidon::{ArithmeticSponge, Plonk15SpongeConstants, Sponge, SpongeConstants},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use plonk_15_wires_circuits::wires::{Wire, COLUMNS};
use plonk_15_wires_circuits::{
    gate::CircuitGate,
    gates::poseidon::{round_range, ROUNDS_PER_ROW, SPONGE_WIDTH},
    nolookup::constraints::ConstraintSystem,
};
use plonk_15_wires_protocol_dlog::{
    index::{Index, SRSSpec},
    prover::ProverProof,
};
use rand::{rngs::StdRng, SeedableRng};
use std::time::Instant;
use std::{io, io::Write};

// const PERIOD: usize = Plonk15SpongeConstants::ROUNDS_FULL + 1;
// const M: usize = PERIOD * (NUM_POS-1);
// const MAX_SIZE: usize = N; // max size of poly chunks
const PUBLIC: usize = 0;

const NUM_POS: usize = 1; // 1360; // number of Poseidon hashes in the circuit
const ROUNDS_PER_HASH: usize = Plonk15SpongeConstants::ROUNDS_FULL;
const POS_ROWS_PER_HASH: usize = ROUNDS_PER_HASH / ROUNDS_PER_ROW;
const N_LOWER_BOUND: usize = (POS_ROWS_PER_HASH + 1) * NUM_POS; // Plonk domain size

#[test]
fn poseidon_vesta_15_wires() {
    let max_size = 1 << ceil_log2(N_LOWER_BOUND);
    println!("max_size = {}", max_size);
    println!("rounds per hash = {}", ROUNDS_PER_HASH);
    println!("rounds per row = {}", ROUNDS_PER_ROW);
    assert_eq!(ROUNDS_PER_HASH % ROUNDS_PER_ROW, 0);

    let round_constants = &oracle::pasta::fp::params().round_constants;

    // we keep track of an absolute row, and relative row within a gadget
    let mut abs_row = 0;

    // circuit gates
    let mut gates: Vec<CircuitGate<Fp>> = Vec::with_capacity(max_size);

    // custom constraints for Poseidon hash function permutation
    // ROUNDS_FULL full rounds constraint gates
    for _ in 0..NUM_POS {
        // create a poseidon gadget manully
        for rel_row in 0..POS_ROWS_PER_HASH {
            // the 15 wires for this row
            let wires = array_init(|col| Wire { col, row: abs_row });

            // round constant for this row
            let coeffs = array_init(|offset| {
                let round = rel_row * ROUNDS_PER_ROW + offset + 1;
                array_init(|field_el| round_constants[round][field_el])
            });

            // create poseidon gate for this row
            gates.push(CircuitGate::<Fp>::create_poseidon(abs_row, wires, coeffs));
            abs_row += 1;
        }

        // final (zero) gate that contains the output of poseidon
        let wires = array_init(|col| Wire { col, row: abs_row });
        gates.push(CircuitGate::<Fp>::zero(abs_row, wires));
        abs_row += 1;
    }

    /*
    for j in 0..Plonk15SpongeConstants::ROUNDS_FULL-2
    {
        gates.push(CircuitGate::<Fp>::create_poseidon(i, [Wire{col:0, row:i}, Wire{col:1, row:i}, Wire{col:2, row:i}, Wire{col:3, row:i}, Wire{col:4, row:i}], round_constants[j].clone()));
        i+=1;
    }
    gates.push(CircuitGate::<Fp>::zero(i, [Wire{col:0, row:i}, Wire{col:1, row:i}, Wire{col:2, row:i}, Wire{col:3, row:i}, Wire{col:4, row:i}]));
    i+=1;
    gates.push(CircuitGate::<Fp>::zero(i, [Wire{col:0, row:i}, Wire{col:1, row:i}, Wire{col:2, row:i}, Wire{col:3, row:i}, Wire{col:4, row:i}]));
    i+=1;
    gates.push(CircuitGate::<Fp>::zero(i, [Wire{col:0, row:i}, Wire{col:1, row:i}, Wire{col:2, row:i}, Wire{col:3, row:i}, Wire{col:4, row:i}]));
    */

    // create the index
    let fp_sponge_params = oracle::pasta::fp::params();
    let cs = ConstraintSystem::<Fp>::create(gates, fp_sponge_params, PUBLIC).unwrap();
    let fq_sponge_params = oracle::pasta::fq::params();
    let (endo_q, _endo_r) = endos::<Other>();
    let srs = SRS::create(max_size);
    let srs = SRSSpec::Use(&srs);

    let index = Index::<Affine>::create(cs, fq_sponge_params, endo_q, srs);

    positive(&index);
}

// creates a proof and verifies it
fn positive(index: &Index<Affine>) {
    // constant
    let max_size = 1 << ceil_log2(N_LOWER_BOUND);

    // set up
    let rng = &mut StdRng::from_seed([0u8; 32]);
    let params = oracle::pasta::fp::params();
    let mut sponge = ArithmeticSponge::<Fp, Plonk15SpongeConstants>::new();
    let group_map = <Affine as CommitmentCurve>::Map::setup();

    // batching what?
    let mut batch = Vec::new();

    // debug
    println!("{}{:?}", "Circuit size: ".yellow(), max_size);
    println!("{}{:?}", "Polycommitment chunk size: ".yellow(), max_size);
    println!(
        "{}{:?}",
        "Number oh Poseidon hashes in the circuit: ".yellow(),
        NUM_POS
    );
    println!(
        "{}{:?}",
        "Full rounds: ".yellow(),
        Plonk15SpongeConstants::ROUNDS_FULL
    );
    println!(
        "{}{:?}",
        "Sbox alpha: ".yellow(),
        Plonk15SpongeConstants::SPONGE_BOX
    );
    println!("{}", "Base curve: vesta\n".green());
    println!("{}", "Prover zk-proof computation".green());

    let mut start = Instant::now();

    // why would there be several tests?
    for test in 0..1 {
        // witness for Poseidon permutation custom constraints
        // (15 columns of vectors, each vector is of size n)
        let mut witness: [Vec<Fp>; COLUMNS] = array_init(|_| vec![Fp::zero(); max_size]);
        println!("witness: {:?}", witness);

        // creates a random initial state
        let init = vec![
            Fp::rand(rng),
            Fp::rand(rng),
            Fp::rand(rng),
            Fp::rand(rng),
            Fp::rand(rng),
        ];

        // number of poseidon instances in the circuit
        for h in 0..NUM_POS {
            // index
            // TODO: is the `+ 1` correct?
            let first_row = h * (POS_ROWS_PER_HASH + 1);

            // initialize the sponge in the circuit with our random state
            let first_state_cols = &mut witness[round_range(0)];
            for state_idx in 0..SPONGE_WIDTH {
                first_state_cols[state_idx][first_row] = init[state_idx];
            }

            // set the sponge state
            sponge.state = init.clone();

            // for the poseidon rows
            for row_idx in 0..POS_ROWS_PER_HASH {
                let row = row_idx + first_row;
                for round in 0..ROUNDS_PER_ROW {
                    // the last round makes use of the next row
                    let maybe_next_row = if round == ROUNDS_PER_ROW - 1 {
                        row + 1
                    } else {
                        row
                    };

                    //
                    let abs_round = round + row_idx * ROUNDS_PER_ROW;

                    // TODO: this won't work if the circuit has an INITIAL_ARK
                    sponge.full_round(abs_round, &params);

                    // apply the sponge and record the result in the witness
                    let cols_to_update = round_range((round + 1) % ROUNDS_PER_ROW);
                    witness[cols_to_update]
                        .iter_mut()
                        .zip(sponge.state.iter())
                        // update the state (last update is on the next row)
                        .for_each(|(w, s)| w[maybe_next_row] = *s);
                }
            }
        }

        /*
        sponge.state = init.clone();
        w.iter_mut().zip(sponge.state.iter()).for_each(|(w, s)| w.push(*s));

        // ROUNDS_FULL full rounds
        for j in 0..Plonk15SpongeConstants::ROUNDS_FULL-2
        {
            sponge.full_round(j, &params);
            w.iter_mut().zip(sponge.state.iter()).for_each(|(w, s)| w.push(*s));
        }

        w.iter_mut().for_each(|w| {w.push(Fp::rand(rng)); w.push(Fp::rand(rng))}); */

        // verify the circuit satisfiability by the computed witness
        assert_eq!(index.cs.verify(&witness), true);

        // ?
        let prev = {
            // ?
            let k = ceil_log2(index.srs.get_ref().g.len());

            // random challenges
            let chals: Vec<_> = (0..k).map(|_| Fp::rand(rng)).collect();

            // commitments of ?
            let comm = {
                let coeffs = b_poly_coefficients(&chals);
                let b = DensePolynomial::from_coefficients_vec(coeffs);
                index.srs.get_ref().commit_non_hiding(&b, None)
            };

            (chals, comm)
        };

        println!("n vs domain{} {}", max_size, index.cs.domain.d1.size);

        // add the proof to the batch
        batch.push(
            ProverProof::create::<
                DefaultFqSponge<VestaParameters, Plonk15SpongeConstants>,
                DefaultFrSponge<Fp, Plonk15SpongeConstants>,
            >(&group_map, &witness, &index, vec![prev])
            .unwrap(),
        );

        print!("{:?}\r", test);
        io::stdout().flush().unwrap();
    }
    println!("{}{:?}", "Execution time: ".yellow(), start.elapsed());

    let verifier_index = index.verifier_index();

    let lgr_comms = vec![];
    let batch: Vec<_> = batch
        .iter()
        .map(|p| (&verifier_index, &lgr_comms, p))
        .collect();

    // verify the proofs in batch
    println!("{}", "Verifier zk-proofs verification".green());
    start = Instant::now();
    match ProverProof::verify::<
        DefaultFqSponge<VestaParameters, Plonk15SpongeConstants>,
        DefaultFrSponge<Fp, Plonk15SpongeConstants>,
    >(&group_map, &batch)
    {
        Err(error) => {
            println!("wait what?");
            panic!("Failure verifying the prover's proofs in batch: {}", error)
        }
        Ok(_) => {
            println!("{}{:?}", "Execution time: ".yellow(), start.elapsed());
        }
    }
}