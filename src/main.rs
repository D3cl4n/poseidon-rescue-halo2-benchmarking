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


// structure to store numbers in cells
struct Number<F: PrimeField>(AssignedCell<F, F>);

// structure for shared parameters for permutation functions
#[derive(Clone, Debug)]
struct PermutationParameters<F: PrimeField> {
    state_size: usize,
    rate: usize,
    capacity: usize,
    mds: [[F; 3]; 3] // TODO: change this to a field element
}

// structure for Poseidon specific permutation parameters
#[derive(Clone, Debug)]
struct Poseidon<F: PrimeField> {
    common_params: PermutationParameters<F>,
    partial_rounds: usize,
    full_rounds: usize,
    n: usize,
    alpha: F
}

// structure for Rescue-Prime specific permutation parameters
#[derive(Clone, Debug)]
struct RescuePrime<F: PrimeField> {
    common_params: PermutationParameters<F>,
    rounds: usize,
    alpha: F,
    alpha_inv: F
}

// trait for shared parameters that RescuePrime and Poseidon structs implement
trait PermutationParams<F: PrimeField>: Clone + Debug {
    fn common(&self) -> &PermutationParameters<F>;
}

// implementations for the PermutationParams trait
impl<F: PrimeField> PermutationParams<F> for Poseidon<F> {
    fn common(&self) -> &PermutationParameters<F> {
        &self.common_params
    }
}

impl<F: PrimeField> PermutationParams<F> for RescuePrime<F> {
    fn common(&self) -> &PermutationParameters<F> {
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
struct PoseidonChipConfig<F: PrimeField, P: PermutationParams<F>> {
    permutation_params: P,
    circuit_params: CircuitParameters,
    _marker: PhantomData<F>,
    // the below selectors are specific to Poseidon (Hades construction)
    s_sub_bytes_full: Selector,
    s_sub_bytes_partial: Selector
}

// Rescue-Prime chip configuration
#[derive(Clone, Debug)]
struct RescueChipConfig<F: PrimeField, P: PermutationParams<F>> {
    permutation_params: P,
    circuit_params: CircuitParameters,
    _marker: PhantomData<F>,
    // the selector below is specific to Rescue-Prime
    s_sub_bytes: Selector,
    s_sub_bytes_inv: Selector
}

// structure for the poseidon permutation chip
struct PoseidonChip<F: PrimeField, P: PermutationParams<F>> {
    config: PoseidonChipConfig<F, P>,
    _marker: PhantomData<F>,
}

// structure for the poseidon permutation chip
struct RescueChip<F: PrimeField, P: PermutationParams<F>> {
    config: RescueChipConfig<F, P>,
    _marker: PhantomData<F>,
}

// implement the Chip trait for PoseidonChip
impl<F: PrimeField, P: PermutationParams<F>> Chip<F> for PoseidonChip<F, P> {
    type Config = PoseidonChipConfig<F, P>;
    type Loaded = ();

    // getter for the chip config
    fn config(&self) -> &Self::Config {
        &self.config
    }

    // getter for the loaded field
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// implement the Chip trait for RescueChip
impl<F: PrimeField, P: PermutationParams<F>> Chip<F> for RescueChip<F, P> {
    type Config = RescueChipConfig<F, P>;
    type Loaded = ();

    // getter for the chip config
    fn config(&self) -> &Self::Config {
        &self.config
    }

    // getter for the loaded field
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// helper methods that both chips call when configuring (gate construction, column configurations, etc.)
// gates created are stored in the ConstraintSystem instance
fn create_arc_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3], 
    fixed: [Column<Fixed>; 3], 
    s_add_rcs: Selector
) {
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
}

fn create_mds_mul_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3], 
    s_mds_mul: Selector,
    mds: &[[F; 3]; 3]
) {
    meta.create_gate("ML_gate", |meta| {
        let s_mds_mul = meta.query_selector(s_mds_mul);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur());
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        // MDS matrix elements from row in column 0 -> column 2 order, use Expression:Constant to embed into polynomial
        let mds_0_0 = Expression::Constant(mds[0][0]);
        let mds_0_1 = Expression::Constant(mds[0][1]);
        let mds_0_2 = Expression::Constant(mds[0][2]);
        let mds_1_0 = Expression::Constant(mds[1][0]);
        let mds_1_1 = Expression::Constant(mds[1][1]);
        let mds_1_2 = Expression::Constant(mds[1][2]);
        let mds_2_0 = Expression::Constant(mds[2][0]);
        let mds_2_1 = Expression::Constant(mds[2][1]);
        let mds_2_2 = Expression::Constant(mds[2][2]);
        
        // constraint - computes vector matrix product
        vec![
            s_mds_mul.clone() * (a0_next - (a0.clone()*mds_0_0 + a1.clone()*mds_0_1 + a2.clone()*mds_0_2)),
            s_mds_mul.clone() * (a1_next - (a0.clone()*mds_1_0 + a1.clone()*mds_1_1 + a2.clone()*mds_1_2)),
            s_mds_mul * (a2_next - (a0*mds_2_0 + a1*mds_2_1 + a2*mds_2_2))
        ]
    });
}

// helper functions for creating Poseidon specific gates
fn create_partial_sbox_gate_ps<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: Column<Advice>,
    s_sub_bytes_partial: Selector, 
) {
    meta.create_gate("PS_partial_sbox_gate", |meta| {
        let s_sub_bytes_partial = meta.query_selector(s_sub_bytes_partial);
        let a0 = meta.query_advice(advice, Rotation::cur()); // state[0] = state[0]**5, alpha = 5
        let a0_next = meta.query_advice(advice, Rotation::next());

        vec![s_sub_bytes_partial* (a0_next - (a0.clone()*a0.clone()*a0.clone()*a0.clone()*a0))]
    });
}

fn create_full_sbox_gate_ps<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: [Column<Advice>; 3],
    s_sub_bytes_full: Selector, 
) {
    meta.create_gate("PS_full_sbox_gate", |meta| {
        let s_sub_bytes_full = meta.query_selector(s_sub_bytes_full);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next()); 

        vec![
            s_sub_bytes_full.clone() * (a0_next - (a0.clone()*a0.clone()*a0.clone()*a0.clone()*a0)),
            s_sub_bytes_full.clone() * (a1_next - (a1.clone()*a1.clone()*a1.clone()*a1.clone()*a1)),
            s_sub_bytes_full * (a2_next - (a2.clone()*a2.clone()*a2.clone()*a2.clone()*a2))
        ]
    });
}

// helper functions for creating Rescue-Prime specific gates
// alpha = 3
// alpha_inv = 12297829382473034371 = inverse(3, p-1)
fn create_sbox_gate_rs<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3],
    s_sub_bytes: Selector
) {
    meta.create_gate("RS_sbox_gate", |meta| {
        let s_sub_bytes = meta.query_selector(s_sub_bytes);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        vec![
            s_sub_bytes.clone() * (a0_next - (a0.clone()*a0.clone()*a0)),
            s_sub_bytes.clone() * (a1_next - (a1.clone()*a1.clone()*a1)),
            s_sub_bytes * (a2_next - (a2.clone()*a2.clone()*a2))
        ]
    });
}

fn create_sbox_inv_gate_rs<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: [Column<Advice>; 3],
    s_sub_bytes_inv: Selector
) {
    meta.create_gate("RS_sbox_inv_gate", |meta| {
        let s_sub_bytes_inv = meta.query_selector(s_sub_bytes_inv);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        // TODO: figure out constraint for a' = a^alpha_inv which is huge
    });
}

// main function
fn main() {
    println!("Hello, world!");
}
