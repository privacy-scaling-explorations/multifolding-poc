use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::{log2, One, Zero};

use std::ops::Neg;

// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;

use std::sync::Arc;

use crate::espresso::multilinear_polynomial::*;
// use crate::espresso::virtual_polynomial::{build_eq_x_r, VirtualPolynomial};
use crate::espresso::virtual_polynomial::*;
use std::ops::Add;

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
    // Compute v_j values of the linearized committed CCS form
    fn compute_vj(self: &Self, z: Vec<Fr>, r: &Vec<Fr>) -> Vec<Fr> {
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
            let mut v_j = Fr::zero();
            for y in BooleanHypercube::new(self.s_prime) {
                // Let's evaluate M_i(r,y)
                let mut r_y_point = y.clone();
                r_y_point.append(&mut r.clone());
                let M_eval = M_i.evaluate(&r_y_point).unwrap();
                let z_eval = z_y_mle.evaluate(&y).unwrap();

                // Calculate the sum
                v_j += M_eval * z_eval;
            }
            v.push(v_j);
        }
        v
    }

    /// computes \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) ) concrete
    /// value by evaluating x \in {0,1}^s
    fn compute_q_value(self: &Self, z: Vec<Fr>, beta: &Vec<Fr>) -> Fr {
        let z_mle = vec_to_mle(self.s_prime, z);
        let mut q = Fr::zero();

        for i in 0..self.q {
            let mut Sj_prod: Fr = Fr::one();
            for j in self.S[i].clone() {
                let M_j = matrix_to_mle(self.M[j].clone());
                // let M_j = fix_variables(&M_j, &beta);
                let M_j = fix_last_variables(&M_j, &beta);
                let mut M_j_z = VirtualPolynomial::new_from_mle(&Arc::new(M_j.clone()), Fr::one());
                M_j_z
                    .mul_by_mle(Arc::new(z_mle.clone()), Fr::one())
                    .unwrap();

                let v_j = BooleanHypercube::new(self.s_prime)
                    .into_iter()
                    .map(|y| M_j_z.evaluate(&y).unwrap())
                    .fold(Fr::zero(), |acc, result| acc + result);

                Sj_prod *= v_j;
            }
            q += Sj_prod * self.c[i];
        }
        q
    }

    /// Return the multilinear polynomial p(x) = \sum_{y \in {0,1}^s'} M_j(x, y) * z(y)
    fn compute_sum_Mz(
        &self,
        M_j: DenseMultilinearExtension<Fr>,
        z: DenseMultilinearExtension<Fr>,
    ) -> DenseMultilinearExtension<Fr> {
        let mut sum_Mz = DenseMultilinearExtension {
            evaluations: vec![Fr::zero(); self.m],
            num_vars: self.s,
        };

        let bhc = BooleanHypercube::new(self.s_prime);
        for y in bhc.into_iter() {
            // let M_j_y = fix_variables(&M_j, &y); // espresso fix_variables
            let M_j_y = M_j.fix_variables(&y); // arkworks fix_variables

            let z_y = z.evaluate(&y).unwrap();
            let M_j_z = scalar_mul(&M_j_y, &z_y);
            sum_Mz = sum_Mz.add(M_j_z);
        }
        sum_Mz
    }

    /// computes \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    fn compute_q(self: &Self, z: Vec<Fr>) -> VirtualPolynomial<Fr> {
        let z_mle = vec_to_mle(self.s_prime, z);
        let mut q = VirtualPolynomial::<Fr>::new(self.s);
        for i in 0..self.q {
            let mut Sj_prod: VirtualPolynomial<Fr> = VirtualPolynomial::<Fr>::new(self.s);
            for j in self.S[i].clone() {
                let M_j = matrix_to_mle(self.M[j].clone());
                let sum_Mz = self.compute_sum_Mz(M_j, z_mle.clone());
                // TODO Sj_prod = Sj_prod * sum_Mz
            }
            // TODO q = q + c_i * Sj_prod
        }
        // TODO
        unimplemented!();
    }

    /// computes Q(x) = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    fn compute_Qx(self, z: Vec<Fr>, beta: &Vec<Fr>) -> VirtualPolynomial<Fr> {
        let q = self.compute_q(z);
        let Q = q.build_f_hat(beta).unwrap();
        Q
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
    // Test that a basic CCS relation can be satisfied
    fn test_ccs_relation() -> () {
        let ccs = get_test_ccs();
        let z = gen_z(3);

        ccs.check_relation(z).unwrap();
    }

    #[test]
    fn test_linearized_ccs_vj() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = gen_z(3);
        ccs.check_relation(z.clone()).unwrap();

        // Compute the v_i claims from the LCCCS for random r
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let v = ccs.compute_vj(z.clone(), &r);
        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(v.len(), 3);

        // TODO: Test that v_j == \sum_x L_j(x) as demonstrated in the completeness proof
    }

    #[test]
    fn test_compute_q_value() -> () {
        let ccs = get_test_ccs();
        let z = gen_z(3);
        ccs.check_relation(z.clone()).unwrap();

        // check that q(x) evaluated to any value of the boolean hypercube is equal to 0
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            let q = ccs.compute_q_value(z.clone(), &x);
            assert_eq!(q, Fr::zero());
        }
    }

    #[test]
    fn test_compute_sum_Mz_over_boolean_hypercube() -> () {
        let ccs = get_test_ccs();
        let z = gen_z(3);
        ccs.check_relation(z.clone()).unwrap();
        let z_mle = vec_to_mle(ccs.s_prime, z);

        // check that evaluating over all the values x over the boolean hypercube, the result of
        // the next for loop is equal to 0
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            // println!("x {:?}", x);
            let mut r = Fr::zero();
            for i in 0..ccs.q {
                let mut Sj_prod = Fr::one();
                for j in ccs.S[i].clone() {
                    let M_j = matrix_to_mle(ccs.M[j].clone());
                    let sum_Mz = ccs.compute_sum_Mz(M_j, z_mle.clone());
                    // println!("sum_Mz {:?}", sum_Mz);
                    let sum_Mz_x = sum_Mz.evaluate(&x).unwrap();
                    // println!("sum_Mz_x {:?}", sum_Mz_x);
                    Sj_prod *= sum_Mz_x;
                }
                // println!("Sj_prod {:?}\n", Sj_prod);
                r += Sj_prod * ccs.c[i];
            }
            assert_eq!(r, Fr::zero());
        }
    }
}
