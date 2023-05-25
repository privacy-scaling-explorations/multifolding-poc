use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::{log2, One, Zero};

use std::ops::Neg;

// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;

use crate::espresso::virtual_polynomial::VirtualPolynomial;

use super::hypercube::*;
use super::mle::*;
use super::util::*;

/// A sparse representation of constraint matrices.
pub type Matrix = Vec<Vec<Fr>>;

#[derive(Error, Debug)]
pub enum CCSError {
    #[error("Relation not satisfied")]
    NotSatisfied,
}

/// A CCS circuit
// XXX should probably put the params in a CCSParams and create similar structs for committed CCS and linearized CCS
#[derive(Debug, Clone)]
pub struct CCS {
    m: usize,
    n: usize,
    t: usize,
    q: usize,
    d: usize,
    s: usize,
    s_prime: usize,

    M: Vec<Matrix>,
    S: Vec<Vec<usize>>,
    c: Vec<Fr>,
}

impl CCS {
    // Compute v_i values of the linearized committed CCS form
    fn compute_linearized_form(self: &Self, z: Vec<Fr>, r: &Vec<Fr>) -> Vec<Fr> {
        // Convert z to MLE
        let z_y_mle = vec_to_mle(self.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<Fr>> = self
            .M
            .clone()
            .into_iter()
            .map(|m| matrix_to_mle(m))
            .collect();

        // For each M_i matrix, fix the first s variables to `r`
        let M_r_y_mle: Vec<DenseMultilinearExtension<Fr>> =
            M_x_y_mle.into_iter().map(|m| m.fix_variables(&r)).collect();

        let mut v = Vec::with_capacity(self.t);

        assert_eq!(self.t, M_r_y_mle.len());
        for M_i in M_r_y_mle {
            // Let's build the summand polynomial: M_i(r,y)*z(y)
            let mut M_i_z = VirtualPolynomial::new_from_mle(&Arc::new(M_i.clone()), Fr::one());
            M_i_z
                .mul_by_mle(Arc::new(z_y_mle.clone()), Fr::one())
                .unwrap();

            // Calculate the sum
            let v_i = BooleanHypercube::new(self.s_prime)
                .into_iter()
                .map(|y| M_i_z.evaluate(&y).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            v.push(v_i);
        }

        v
    }

    /// Check that a CCS structure is satisfied by a z vector.
    /// This works with matrices. It doesn't do any polynomial stuff
    /// Only for testing
    fn check_relation(self: &Self, z: Vec<Fr>) -> Result<(), CCSError> {
        let mut result = vec![Fr::zero(); self.m];

        for i in 0..self.q {
            // XXX This can be done more neatly with a .fold() or .reduce()

            // Extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&Matrix> = self.S[i].iter().map(|j| &self.M[*j]).collect();

            // Complete the hadamard chain
            let mut hadamard_result = vec![Fr::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(&M_j, &z));
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
    fn from_r1cs(A: Vec<Vec<Fr>>, B: Vec<Vec<Fr>>, C: Vec<Vec<Fr>>) -> Self {
        let m = A.len();
        let n = A[0].len();
        Self {
            m,
            n,
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

#[cfg(test)]
pub mod test {
    use super::*;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    // Return a CCS circuit that implements the Vitalik `x^3 + x + 5 == 35` (from
    // https://www.vitalik.ca/general/2016/12/10/qap.html )
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
        CCS::from_r1cs(A, B, C)
    }
    // computes the z vector for the given input for Vitalik's equation
    pub fn gen_z(input: usize) -> Vec<Fr> {
        to_F_vec(vec![
            1,
            input,
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
        ])
    }

    #[test]
    // Test that a basic CCS circuit can be satisfied
    fn test_ccs() -> () {
        let ccs = get_test_ccs();
        let z = gen_z(3);

        ccs.check_relation(z).unwrap();
    }

    #[test]
    fn test_linearized_ccs() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = gen_z(3);
        // Get a variable of dimension s
        // let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let bhc = BooleanHypercube::new(ccs.s);
        let r: Vec<Fr> = bhc.at_i(0);
        println!("r {:?}", r);
        let v = ccs.compute_linearized_form(z, &r);
        // XXX actually test something
        println!("v: {:?}", v);

        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(v.len(), 3);

        // TODO: this should match: v_0 * v_1 == v_2. Seems that compute_linearized_form is not
        // returning correct values.
        assert_eq!(v[0] * v[1], v[2]);
    }
}
