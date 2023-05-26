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

        let mut v = Vec::with_capacity(self.t);
        for M_i in M_x_y_mle {
            let mut v_i = Fr::zero();
            for (i, y) in BooleanHypercube::new(self.s_prime).enumerate() {
                // Let's evaluate M_i(r,y)
                let mut r_y_point = y.clone();
                r_y_point.append(&mut r.clone());
                let M_eval = M_i.evaluate(&r_y_point).unwrap();
                let z_eval = z_y_mle.evaluate(&y).unwrap();

                // Calculate the sum
                v_i += M_eval*z_eval;
            }
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
        ccs.check_relation(z.clone()).unwrap();

        // First check that it's satisfied inside the boolean hypercube
        let bhc = BooleanHypercube::new(ccs.s);
        for r in bhc {
            println!("r {:?}", r);
            let v = ccs.compute_linearized_form(z.clone(), &r);

            // with our test vector comming from R1CS, v should have length 3
            assert_eq!(v.len(), 3);

            // TODO: this should match: v_0 * v_1 == v_2. Seems that compute_linearized_form is not
            // returning correct values.
            assert_eq!(v[0] * v[1], v[2]);
        }

        // Now test outside the hypercube
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        println!("r {:?}", r);
        let v = ccs.compute_linearized_form(z.clone(), &r);

        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(v.len(), 3);

        // TODO: this should match: v_0 * v_1 == v_2. Seems that compute_linearized_form is not
        // returning correct values.
        assert_eq!(v[0] * v[1], v[2]);
    }
}
