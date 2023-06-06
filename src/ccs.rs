use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::{log2, One, Zero};

use std::ops::Neg;

// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;

use crate::espresso::multilinear_polynomial::*;
use std::ops::Add;

use super::util::hypercube::*;
use super::util::mle::*;
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
    /// Return the multilinear polynomial p(x) = \sum_{y \in {0,1}^s'} M_j(x, y) * z(y)
    pub fn compute_sum_Mz(
        &self,
        M_j: DenseMultilinearExtension<Fr>,
        z: &DenseMultilinearExtension<Fr>,
    ) -> DenseMultilinearExtension<Fr> {
        let mut sum_Mz = DenseMultilinearExtension {
            evaluations: vec![Fr::zero(); self.m],
            num_vars: self.s,
        };

        let bhc = BooleanHypercube::new(self.s_prime);
        for y in bhc.into_iter() {
            // XXX should this be fix_last_variables() ?
            let M_j_y = fix_variables(&M_j, &y);
            let z_y = z.evaluate(&y).unwrap();
            let M_j_z = scalar_mul(&M_j_y, &z_y);
            sum_Mz = sum_Mz.add(M_j_z);
        }
        sum_Mz
    }

    /// Return a vector of evaluations p_j(r) = \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    /// for all j values in 0..self.t
    pub fn compute_all_sum_Mz_evals(&self, z: &Vec<Fr>, r: &[Fr]) -> Vec<Fr> {
        // Convert z to MLE
        let z_y_mle = vec_to_mle(self.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<Fr>> =
            self.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut v = Vec::with_capacity(self.t);
        for M_i in M_x_y_mle {
            let sum_Mz = self.compute_sum_Mz(M_i, &z_y_mle);
            let v_i = sum_Mz.evaluate(r).unwrap();
            v.push(v_i);
        }
        v
    }
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
    use crate::espresso::virtual_polynomial::eq_eval;

    use super::*;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    #[test]
    /// Test that a basic CCS relation can be satisfied
    fn test_ccs_relation() -> () {
        let ccs = get_test_ccs();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_compute_sum_Mz_over_boolean_hypercube() -> () {
        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();
        let z_mle = vec_to_mle(ccs.s_prime, &z);

        // check that evaluating over all the values x over the boolean hypercube, the result of
        // the next for loop is equal to 0
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            // println!("x {:?}", x);
            let mut r = Fr::zero();
            for i in 0..ccs.q {
                let mut Sj_prod = Fr::one();
                for j in ccs.S[i].clone() {
                    let M_j = matrix_to_mle(ccs.M[j].clone());
                    let sum_Mz = ccs.compute_sum_Mz(M_j, &z_mle);
                    let sum_Mz_x = sum_Mz.evaluate(&x).unwrap();
                    Sj_prod *= sum_Mz_x;
                }
                r += Sj_prod * ccs.c[i];
            }
            assert_eq!(r, Fr::zero());
        }
    }

    /// Given M(x,y) matrix and a random field element `r`, test that ~M(r,y) is is an s'-variable polynomial which
    /// compresses every column j of the M(x,y) matrix by performing a random linear combination between the elements
    /// of the column and the values eq_i(r) where i is the row of that element
    ///
    /// For example, for matrix M:
    ///
    /// [2, 3, 4, 4
    ///  4, 4, 3, 2
    ///  2, 8, 9, 2
    ///  9, 4, 2, 0]
    ///
    /// The polynomial ~M(r,y) is a polynomial in F^2 which evaluates to the following values in the hypercube:
    /// - M(00) = 2*eq_00(r) + 4*eq_10(r) + 2*eq_01(r) + 9*eq_11(r)
    /// - M(10) = 3*eq_00(r) + 4*eq_10(r) + 8*eq_01(r) + 4*eq_11(r)
    /// - M(01) = 4*eq_00(r) + 3*eq_10(r) + 9*eq_01(r) + 2*eq_11(r)
    /// - M(11) = 4*eq_00(r) + 2*eq_10(r) + 2*eq_01(r) + 0*eq_11(r)
    ///
    /// This is used by Hypernova in LCCCS to perform a verifier-chosen random linear combination between the columns
    /// of the matrix and the z vector. This technique is also used extensively in "An Algebraic Framework for
    /// Universal and Updatable SNARKs".
    #[test]
    fn test_compute_M_r_y_compression() -> () {
        let mut rng = test_rng();

        // s = 2, s' = 3
        let ccs = get_test_ccs();

        let M = ccs.M[0].clone();
        let M_mle = matrix_to_mle(M.clone());

        // Fix the polynomial ~M(r,y)
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let M_r_y = fix_last_variables(&M_mle, &r);

        // Now let's compute M_r_y the other way around
        for j in 0..M[0].len() {
            // Go over every column of M
            let column_j: Vec<Fr> = M.clone().iter().map(|x| x[j]).collect();

            // and perform the random lincomb between the elements of the column and eq_i(r)
            let rlc = BooleanHypercube::new(ccs.s)
                .enumerate()
                .into_iter()
                .map(|(i, x)| column_j[i] * eq_eval(&x, &r).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);

            assert_eq!(M_r_y.evaluations[j], rlc);
        }
    }
}
