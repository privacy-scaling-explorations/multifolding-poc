use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::{One, Zero};

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
struct CCSCircuit {
    m: usize,
    n: usize,
    t: usize,
    q: usize,
    d: usize,
    s: usize,
    s_prime: usize,

    vec_M_i: Vec<Matrix>,
    vec_S_i: Vec<Vec<usize>>,
    vec_c_i: Vec<Fr>,
}

impl CCSCircuit {
    // Compute v_i values of the linearized committed CCS form
    fn compute_linearized_form(self: &Self, z: Vec<Fr>, r: Vec<Fr>) -> Vec<Fr> {
        // Convert z to MLE
        let z_y_mle = vec_to_mle(self.s_prime, z);
        // Convert all matrices to MLE
        let vec_M_i_x_y_mle: Vec<DenseMultilinearExtension<Fr>> = self
            .vec_M_i
            .clone()
            .into_iter()
            .map(|m| matrix_to_mle(self.s + self.s_prime, m))
            .collect();

        // For each M_i matrix, fix the first half of its variables to `r`
        let vec_M_i_r_y_mle: Vec<DenseMultilinearExtension<Fr>> = vec_M_i_x_y_mle
            .into_iter()
            .map(|m| m.fix_variables(&r))
            .collect();

        let mut vec_v_i = Vec::with_capacity(self.t);

        assert_eq!(self.t, vec_M_i_r_y_mle.len());
        for M_i in vec_M_i_r_y_mle {
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
            vec_v_i.push(v_i);
        }

        vec_v_i
    }

    /// Check that a CCS circuit is satisfied by a z vector
    /// This works with matrices. It doen't do any polynomial stuff
    /// Only for testing
    fn check_ccs_matrix_form(self: &Self, z: Vec<Fr>) -> Result<(), CCSError> {
        let mut result = vec![Fr::zero(); self.m];

        for i in 0..self.q {
            // XXX This can be done more neatly with a .fold() or .reduce()

            // Extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&Matrix> = self.vec_S_i[i].iter().map(|j| &self.vec_M_i[*j]).collect();

            // Complete the hadamard chain
            let mut hadamard_result = vec![Fr::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(&M_j, &z));
            }

            // Multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.vec_c_i[i]);

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
mod test {
    use super::*;
    use ark_std::log2;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    /// Return a CCS circuit that implements the Vitalik `x**3 + x + 5 == 35`
    /// only for testing
    fn get_test_ccs_circuit() -> CCSCircuit {
        // A = matrix([
        //     [0, 1, 0, 0, 0, 0],
        //     [0, 0, 0, 1, 0, 0],
        //     [0, 1, 0, 0, 1, 0],
        //     [5, 0, 0, 0, 0, 1],
        //     ])

        let A = vec![
            vec![
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(5u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
            ],
        ];

        // B = matrix([
        //     [0, 1, 0, 0, 0, 0],
        //     [0, 1, 0, 0, 0, 0],
        //     [1, 0, 0, 0, 0, 0],
        //     [1, 0, 0, 0, 0, 0],
        //     ])
        let B = vec![
            vec![
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
        ];

        // C = matrix([
        //     [0, 0, 0, 1, 0, 0],
        //     [0, 0, 0, 0, 1, 0],
        //     [0, 0, 0, 0, 0, 1],
        //     [0, 0, 1, 0, 0, 0],
        //     ])
        let C = vec![
            vec![
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
            ],
            vec![
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(1u64),
                Fr::from(0u64),
                Fr::from(0u64),
                Fr::from(0u64),
            ],
        ];

        let vec_M_i = vec![A.clone(), B.clone(), C.clone()];

        // S1=[0,1]
        // S2=[2]
        // S = [S1, S2]
        let vec_S_i = vec![vec![0, 1], vec![2]];
        // c0=1
        // c1=-1
        // c = [c0, c1]
        let vec_c_i = vec![Fr::one(), -Fr::one()];

        let m = A.len();
        let n = A[0].len();

        CCSCircuit {
            m: m,
            n: n,
            t: 3,
            q: 2,
            d: 2,
            s: log2(m) as usize,
            s_prime: log2(n) as usize,
            vec_M_i,
            vec_S_i,
            vec_c_i,
        }
    }

    #[test]
    /// Test that a basic CCS circuit can be satisfied
    fn test_ccs() -> () {
        let ccs_circuit = get_test_ccs_circuit();
        let z = vec![
            Fr::from(1u64),
            Fr::from(3u64),
            Fr::from(35u64),
            Fr::from(9u64),
            Fr::from(27u64),
            Fr::from(30u64),
        ];

        ccs_circuit.check_ccs_matrix_form(z).unwrap();
    }

    #[test]
    fn test_linearized_ccs_mle() -> () {
        let mut rng = test_rng();

        let ccs_circuit = get_test_ccs_circuit();
        let z = vec![
            Fr::from(1u64),
            Fr::from(3u64),
            Fr::from(35u64),
            Fr::from(9u64),
            Fr::from(27u64),
            Fr::from(30u64),
            Fr::from(27u64),
            Fr::from(30u64),
        ];
        // Get a variable of dimension s
        let r: Vec<Fr> = (0..ccs_circuit.s).map(|_| Fr::rand(&mut rng)).collect();
        let _vec_v_i = ccs_circuit.compute_linearized_form(z, r);
        // XXX actually test something
    }
}
