use ark_bls12_381::Fr;
use ark_std::{log2, One, Zero};

use std::ops::Neg;

// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;

use super::util::vec::*;

/// A sparse representation of constraint matrices.
pub type Matrix = Vec<Vec<Fr>>;

#[derive(Error, Debug)]
pub enum CCSError {
    #[error("Relation not satisfied")]
    NotSatisfied,
}

/// A CCS structure
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CCS {
    // m: number of columns in M_i (such that M_i \in F^{m, n})
    pub m: usize,
    // n = |z|, number of rows in M_i
    pub n: usize,
    // l = |io|
    pub l: usize,
    // t = |M|
    pub t: usize,
    // q = |c| = |S|
    pub q: usize,
    // d: max degree in each variable
    pub d: usize,
    // s = log(m)
    pub s: usize,
    // s_prime = log(n)
    pub s_prime: usize,

    pub M: Vec<Matrix>,
    pub S: Vec<Vec<usize>>,
    pub c: Vec<Fr>,
}

impl CCS {
    /// Check that a CCS structure is satisfied by a z vector.
    /// This works with matrices. It doesn't do any polynomial stuff
    /// Only for testing
    pub fn check_relation(&self, z: &[Fr]) -> Result<(), CCSError> {
        let mut result = vec![Fr::zero(); self.m];

        for i in 0..self.q {
            // XXX This can be done more neatly with a .fold() or .reduce()

            // Extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&Matrix> = self.S[i].iter().map(|j| &self.M[*j]).collect();

            // Complete the hadamard chain
            let mut hadamard_result = vec![Fr::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(M_j, z));
            }

            // Multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.c[i]);

            // Add it to the final vector
            result = vec_add(&result, &c_M_j_z);
        }

        // Make sure the final vector is all zeroes
        for e in result {
            if !e.is_zero() {
                return Err(CCSError::NotSatisfied);
            }
        }

        Ok(())
    }

    /// Converts the R1CS structure to the CCS structure
    fn from_r1cs(A: Vec<Vec<Fr>>, B: Vec<Vec<Fr>>, C: Vec<Vec<Fr>>, io_len: usize) -> Self {
        let m = A.len();
        let n = A[0].len();
        Self {
            m,
            n,
            l: io_len,
            s: log2(m) as usize,
            s_prime: log2(n) as usize,
            t: 3,
            q: 2,
            d: 2,

            S: vec![vec![0, 1], vec![2]],
            c: vec![Fr::one(), Fr::one().neg()],
            M: vec![A, B, C],
        }
    }
}

/// Return a CCS circuit that implements the Vitalik `x^3 + x + 5 == 35` (from
/// https://www.vitalik.ca/general/2016/12/10/qap.html )
#[cfg(test)]
pub fn get_test_ccs() -> CCS {
    let A = to_F_matrix(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 1, 0, 0, 1, 0],
        vec![5, 0, 0, 0, 0, 1],
    ]);
    let B = to_F_matrix(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 1, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
    ]);
    let C = to_F_matrix(vec![
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 0, 0, 0, 1, 0],
        vec![0, 0, 0, 0, 0, 1],
        vec![0, 0, 1, 0, 0, 0],
    ]);
    CCS::from_r1cs(A, B, C, 1)
}

/// Computes the z vector for the given input for Vitalik's equation.
#[cfg(test)]
pub fn get_test_z(input: usize) -> Vec<Fr> {
    // z = (1, io, w)
    to_F_vec(vec![
        1,
        input,
        input * input * input + input + 5, // x^3 + x + 5
        input * input,                     // x^2
        input * input * input,             // x^2 * x
        input * input * input + input,     // x^3 + x
    ])
}

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    /// Test that a basic CCS relation can be satisfied
    fn test_ccs_relation() -> () {
        let ccs = get_test_ccs();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }
}
