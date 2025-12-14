use std::marker::PhantomData;
use ff::PrimeField;
use std::fmt::Debug;
use halo2_proofs::{
    circuit::{AssignedCell, Region, Chip, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Fixed, Circuit, Column, ConstraintSystem, Error, Instance, Selector, Expression},
    poly::Rotation,
};

/*
* Poseidon vs. Rescue-Prime permutation benchmarking over BLS12-381
* Shared parameters: state_size = 3, rate = 2, capacity = 1, MDS, p = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
* Poseidon specific parameters: N = 195, full_rounds = 8, partial_rounds = 57, alpha = 5
* Rescue-Prime specific parameters: rounds = 4, alpha = 3, alpha_inv = 12297829382473034371
* NOTE: Round constants also differ for both permutations, not pasted here
* NOTE: MDS matrix is the same for both permutations, not pasted here
* -------------------------------------------------------------------------------------------
* Shared Circuit Construction:
*  - 3 advice columns, one per state element
*  - 1 instance column, holding the final state values after the permutation
*  - 3 fixed columns, one per constant to be added to the state elements
*  - MDS Multiply Gate: multiplies the vector representing the state by the MDS matrix
*       - Selector: s_mds_mul
*  - Add Round Constants Gate: injects/adds 3 round constants to the state elements
*       - Selector: s_add_rcs
*  - S-Box Gate: raises the state elements to a given power
*       - Selector: s_sub_bytes
* -------------------------------------------------------------------------------------------
* Benchmarks
*  - Number of rows
*  - Number of gates enabled (also reveals number of constraints minus copy constraints)
*  - MockProver runtime
*  - Number of round constants
*  - Number of rounds
*  - Runtime for one round
*  - Advice cell count
*  - Total cell count
*  - Maximum degree
*/


// structure for shared parameters
#[derive(Clone, Debug)]
struct Parameters {
    state_size: usize,
    rate: usize,
    capacity: usize,
    mds: [[String; 3]; 3]
}

// structure for Poseidon specific parameters
#[derive(Clone, Debug)]
struct Poseidon<F: PrimeField> {
    common_params: Parameters,
    partial_rounds: usize,
    full_rounds: usize,
    n: usize,
    alpha: F
}

// structure for Rescue-Prime specific parameters
#[derive(Clone, Debug)]
struct RescuePrime<F: PrimeField> {
    common_params: Parameters,
    rounds: usize,
    alpha: F,
    alpha_inv: F
}

// trait for shared parameters that RescuePrime and Poseidon structs implement
trait PermutationParams: Clone + Debug {
    fn common(&self) -> &Parameters;
}

// implementations for the PermutationParams trait
impl<F: PrimeField> PermutationParams for Poseidon<F> {
    fn common(&self) -> &Parameters {
        &self.common_params
    }
}

impl<F: PrimeField> PermutationParams for RescuePrime<F> {
    fn common(&self) -> &Parameters {
        &self.common_params
    }
}

// common structure for chip configuration, referencing permutation specific param structure
#[derive(Clone, Debug)]
struct PermutationChipConfig<P: PermutationParams> {
    advice: [Column<Advice>; 3],
    fixed: [Column<Fixed>; 3],
    instance: Column<Instance>,
    params: P,
    s_mds_mul: Selector,
    s_add_rcs: Selector,
    s_sub_bytes: Selector // TODO: figure out how to capture the selector for Poseidon's partial rounds, combine in 1 gate?
}

// structure for the permutation chip
struct PermutationChip<F: PrimeField, P: PermutationParams> {
    config: PermutationChipConfig<P>,
    _marker: PhantomData<F>,
}

// structure to store numbers in cells
struct Number<F: PrimeField>(AssignedCell<F, F>);

// implement the Chip trait for the PermutationChip
impl<F: PrimeField, P: PermutationParams> Chip<F> for PermutationChip<F, P> {
    type Config = PermutationChipConfig<P>;
    type Loaded = ();

    // getter for the chip config type
    fn config(&self) -> &Self::Config {
        &self.config
    }

    // getter for the loaded type
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// implement gates, additional functions, etc. for PermutationChip
impl<F: PrimeField, P: PermutationParams> PermutationChip<F, P> {
    // constructor
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        PermutationChip {config, _marker: PhantomData}
    }

    // configure the chip including all gates, constraints, and selectors
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        fixed: [Column<Fixed>; 3],
        instance: Column<Instance>, 
        params: P
    ) -> <Self as Chip<F>>::Config {
        // define the necessary selectors
        let s_mds_mul = meta.selector();
        let s_add_rcs = meta.selector();
        let s_sub_bytes = meta.selector();

        // enable equality on the instance and advice columns
        meta.enable_equality(instance);
        for column in &advice {
            meta.enable_equality(*column);
        }

        // enable constant on the fixed columns
        for column in &fixed {
            meta.enable_constant(*column);
        }

        // AddRoundConstants / InjectRoundConstants gate
        meta.create_gate("ARC_Gate", |meta| {
            let s_add_rcs = meta.query_selector(s_add_rcs);
            let a0 = meta.query_advice(advice[0], Rotation::cur());
            let a1 = meta.query_advice(advice[1], Rotation::cur());
            let a2 = meta.query_advice(advice[2], Rotation::cur());
            let a0_next = meta.query_advice(advice[0], Rotation::next());
            let a1_next = meta.query_advice(advice[1], Rotation::next());
            let a2_next = meta.query_advice(advice[2], Rotation::next());
            let rc0 = meta.query_fixed(fixed[0]); // query_fixed reads from current row when gate is active
            let rc1 = meta.query_fixed(fixed[1]);
            let rc2 = meta.query_fixed(fixed[2]);

            // constraint should be vec![0, 0, 0]
            vec![
                s_add_rcs.clone() * (a0_next - (a0 + rc0)), 
                s_add_rcs.clone() * (a1_next - (a1 + rc1)), 
                s_add_rcs * (a2_next - (a2 + rc2))
            ]
        });

        // return a complete PermutationChipConfig
        PermutationChipConfig {
            advice,
            fixed, 
            instance, 
            params,
            s_mds_mul,
            s_add_rcs,
            s_sub_bytes
        }
    }
}


// main function
fn main() {
    println!("Hello, world!");
}
