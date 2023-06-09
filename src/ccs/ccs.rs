use ark_ec::CurveGroup;
use ark_std::{One, Zero};

// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;

use crate::util::vec::*;

#[derive(Error, Debug)]
pub enum CCSError {
    #[error("Relation not satisfied")]
    NotSatisfied,
}

/// A CCS structure
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CCS<C: CurveGroup> {
    // m: number of columns in M_i (such that M_i \in F^{m, n})
    pub m: usize,
    // n = |z|, number of rows in M_i
    pub n: usize,
    // l = |io|, size of public input/output
    pub l: usize,
    // t = |M|, number of matrices
    pub t: usize,
    // q = |c| = |S|, number of multisets
    pub q: usize,
    // d: max degree in each variable
    pub d: usize,
    // s = log(m), dimension of x
    pub s: usize,
    // s_prime = log(n), dimension of y
    pub s_prime: usize,

    // Vector of matrices
    pub M: Vec<Matrix<C::ScalarField>>,
    // Vector of multisets
    pub S: Vec<Vec<usize>>,
    // Vector of coefficients
    pub c: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    /// Check that a CCS structure is satisfied by a z vector.
    /// This works with matrices. It doesn't do any polynomial stuff
    /// Only for testing
    pub fn check_relation(&self, z: &[C::ScalarField]) -> Result<(), CCSError> {
        let mut result = vec![C::ScalarField::zero(); self.m];

        for i in 0..self.q {
            // XXX This can be done more neatly with a .fold() or .reduce()

            // Extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&Matrix<C::ScalarField>> =
                self.S[i].iter().map(|j| &self.M[*j]).collect();

            // Complete the hadamard chain
            let mut hadamard_result = vec![C::ScalarField::one(); self.m];
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
}

#[cfg(test)]
pub mod test {
    use super::*;
    use ark_bls12_381::G1Projective;
    use ark_std::log2;
    use std::ops::Neg;
    use ark_ff::PrimeField;

    /// Converts the R1CS structure to the CCS structure
    fn CCS_from_r1cs<C: CurveGroup>(
        A: Vec<Vec<C::ScalarField>>,
        B: Vec<Vec<C::ScalarField>>,
        C: Vec<Vec<C::ScalarField>>,
        io_len: usize,
    ) -> CCS<C> {
        let m = A.len();
        let n = A[0].len();
        CCS {
            m,
            n,
            l: io_len,
            s: log2(m) as usize,
            s_prime: log2(n) as usize,
            t: 3,
            q: 2,
            d: 2,

            S: vec![vec![0, 1], vec![2]],
            c: vec![C::ScalarField::one(), C::ScalarField::one().neg()],
            M: vec![A, B, C],
        }
    }

    /// Return a CCS circuit that implements the Vitalik `x^3 + x + 5 == 35` (from
    /// https://www.vitalik.ca/general/2016/12/10/qap.html )
    #[cfg(test)]
    pub fn get_test_ccs<C: CurveGroup>() -> CCS<C> {
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
        CCS_from_r1cs(A, B, C, 1)
    }

    /// Computes the z vector for the given input for Vitalik's equation.
    #[cfg(test)]
    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
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

    /// Test that a basic CCS relation can be satisfied
    #[test]
    fn test_ccs_relation() -> () {
        let ccs = get_test_ccs::<G1Projective>();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }
}
