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


// structure for shared parameters for permutation functions
#[derive(Clone, Debug)]
struct PermutationParameters {
    state_size: usize,
    rate: usize,
    capacity: usize,
    mds: [[String; 3]; 3] // TODO: change this to a field element
}

// structure for Poseidon specific permutation parameters
#[derive(Clone, Debug)]
struct Poseidon<F: PrimeField> {
    common_params: PermutationParameters,
    partial_rounds: usize,
    full_rounds: usize,
    n: usize,
    alpha: F
}

// structure for Rescue-Prime specific permutation parameters
#[derive(Clone, Debug)]
struct RescuePrime<F: PrimeField> {
    common_params: PermutationParameters,
    rounds: usize,
    alpha: F,
    alpha_inv: F
}

// trait for shared parameters that RescuePrime and Poseidon structs implement
trait PermutationParams: Clone + Debug {
    fn common(&self) -> &PermutationParameters;
}

// implementations for the PermutationParams trait
impl<F: PrimeField> PermutationParams for Poseidon<F> {
    fn common(&self) -> &PermutationParameters {
        &self.common_params
    }
}

impl<F: PrimeField> PermutationParams for RescuePrime<F> {
    fn common(&self) -> &PermutationParameters {
        &self.common_params
    }
}

// struture for common circuit parameters
#[derive(Clone, Debug)]
struct CircuitParameters {
    advice: [Column<Advice>; 3],
    fixed: [Column<Fixed>; 3],
    instance: Column<Instance>,
    s_mds_mul: Selector,
    s_add_rcs: Selector
}

// Poseidon chip configuration
#[derive(Clone, Debug)]
struct PoseidonChipConfig<P: PermutationParams> {
    permutation_params: P,
    circuit_params: CircuitParameters,
    // the below selectors are specific to Poseidon (Hades construction)
    s_sub_bytes_full: Selector,
    s_sub_bytes_partial: Selector
}

// Rescue-Prime chip configuration
#[derive(Clone, Debug)]
struct RescuePrimeChipConfig<P: PermutationParams> {
    permutation_params: P,
    circuit_params: CircuitParameters,
    // the selector below is specific to Rescue-Prime
    s_sub_bytes: Selector,
    s_sub_bytes_inv: Selector
}

// structure to store numbers in cells
struct Number<F: PrimeField>(AssignedCell<F, F>);




// main function
fn main() {
    println!("Hello, world!");
}
