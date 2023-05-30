use ark_bls12_381::Fr;
use ark_ff::Field;
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
    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
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
            let sum_Mz = self.compute_sum_Mz(M_i, z_y_mle.clone());
            let v_i = sum_Mz.evaluate(r).unwrap();
            v.push(v_i);
        }
        v
    }
    pub fn compute_g(
        &self,
        z1: Vec<Fr>,
        z2: Vec<Fr>,
        gamma: Fr,
        beta: &Vec<Fr>,
        r_x: &Vec<Fr>,
    ) -> VirtualPolynomial<Fr> {
        let mut vec_L = self.compute_L_j_x(z1, r_x);
        let mut Q = self.compute_Qx(z2, beta);
        let mut g = vec_L[0].clone();
        for j in 1..self.t {
            let gamma_j = gamma.pow([j as u64]);
            vec_L[j].scalar_mul(&gamma_j);
            g = g.add(&vec_L[j]);
        }
        let gamma_t1 = gamma.pow([(self.t + 1) as u64]);
        Q.scalar_mul(&gamma_t1);
        g = g.add(&Q);
        g
    }

    /// Compute all L_j(x) polynomials
    fn compute_L_j_x(self: &Self, z: Vec<Fr>, r_x: &Vec<Fr>) -> Vec<VirtualPolynomial<Fr>> {
        let z_mle = vec_to_mle(self.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<Fr>> = self
            .M
            .clone()
            .into_iter()
            .map(|m| matrix_to_mle(m))
            .collect();

        let mut vec_L_j_x = Vec::with_capacity(self.t);
        for M_j in M_x_y_mle {
            let sum_Mz = self.compute_sum_Mz(M_j, z_mle.clone()); // XXX stop the cloning. take a ref.
            let sum_Mz_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), Fr::one());
            let L_j_x = sum_Mz_virtual.build_f_hat(r_x).unwrap();
            vec_L_j_x.push(L_j_x);
        }

        vec_L_j_x
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

    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    fn compute_q(self: &Self, z: Vec<Fr>) -> VirtualPolynomial<Fr> {
        let z_mle = vec_to_mle(self.s_prime, z);
        let mut q = VirtualPolynomial::<Fr>::new(self.s);

        for i in 0..self.q {
            let mut prod: VirtualPolynomial<Fr> = VirtualPolynomial::<Fr>::new(self.s);
            for j in self.S[i].clone() {
                let M_j = matrix_to_mle(self.M[j].clone());

                let sum_Mz = self.compute_sum_Mz(M_j, z_mle.clone());

                // Fold this sum into the running product
                if prod.products.len() == 0 {
                    // If this is the first time we are adding something to this virtual polynomial, we need to
                    // explicitly add the products using add_mle_list()
                    // XXX is this true? improve API
                    prod.add_mle_list([Arc::new(sum_Mz)], Fr::one()).unwrap();
                } else {
                    prod.mul_by_mle(Arc::new(sum_Mz), Fr::one()).unwrap();
                }
            }
            // Multiply by the product by the coefficient c_i
            prod.scalar_mul(&self.c[i]);
            // Add it to the running sum
            q = q.add(&prod);
        }
        q
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    fn compute_Qx(self: &Self, z: Vec<Fr>, beta: &Vec<Fr>) -> VirtualPolynomial<Fr> {
        let q = self.compute_q(z);
        let Qx = q.build_f_hat(beta).unwrap();
        Qx
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
    /// Test that a basic CCS relation can be satisfied
    fn test_ccs_relation() -> () {
        let ccs = get_test_ccs();
        let z = gen_z(3);

        ccs.check_relation(z).unwrap();
    }

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_linearized_ccs_vj() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = gen_z(3);
        ccs.check_relation(z.clone()).unwrap();

        // Compute the v_i claims from the LCCCS for random r
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let vec_v = ccs.compute_vj(z.clone(), &r);
        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(vec_v.len(), 3);

        let vec_L_j_x = ccs.compute_L_j_x(z.clone(), &r);
        assert_eq!(vec_L_j_x.len(), vec_v.len());

        for (v_i, L_j_x) in vec_v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .into_iter()
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(v_i, sum_L_j_x);
        }
    }

    #[test]
    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    fn test_compute_q() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = gen_z(3);

        let q = ccs.compute_q(z);

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            assert_eq!(Fr::zero(), q.evaluate(&x).unwrap());
        }

        // Evaluate outside the hypercube
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        assert_ne!(Fr::zero(), q.evaluate(&beta).unwrap());
    }

    #[test]
    fn test_compute_Qx() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = gen_z(3);
        ccs.check_relation(z.clone()).unwrap();

        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Qx = ccs.compute_Qx(z, &beta);

        // Let's consider the multilinear polynomial G(x) = \sum_{y \in {0, 1}^s} eq(x, y) q(y)
        // which interpolates the multivariate polynomial q(x) inside the hypercube.
        //
        // Observe that summing Q(x) inside the hypercube, directly computes G(\beta).
        //
        // Now, G(x) is multilinear and agrees with q(x) inside the hypercube. Since q(x) vanishes inside the
        // hypercube, this means that G(x) also vanishes in the hypercube. Since G(x) is multilinear and vanishes
        // inside the hypercube, this makes it the zero polynomial.
        //
        // Hence, evaluating G(x) at a random beta should give zero.

        // Now sum Q(x) evaluations in the hypercube and expect it to be 0
        let r = BooleanHypercube::new(ccs.s)
            .into_iter()
            .map(|x| Qx.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_eq!(r, Fr::zero());
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
                    let sum_Mz_x = sum_Mz.evaluate(&x).unwrap();
                    Sj_prod *= sum_Mz_x;
                }
                r += Sj_prod * ccs.c[i];
            }
            assert_eq!(r, Fr::zero());
        }
    }

    #[test]
    fn test_compute_g() -> () {
        let ccs = get_test_ccs();
        let z1 = gen_z(3);
        let z2 = gen_z(4);
        ccs.check_relation(z1.clone()).unwrap();
        ccs.check_relation(z2.clone()).unwrap();
        let z1_mle = vec_to_mle(ccs.s_prime, z1.clone());
        let z2_mle = vec_to_mle(ccs.s_prime, z2.clone());

        let mut rng = test_rng(); // TMP
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // compute g(x)
        let g = ccs.compute_g(z1.clone(), z2.clone(), gamma, &beta, &r_x);

        // evaluate g(x) over x \in {0,1}^s
        let mut g_on_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            g_on_bhc += g.evaluate(&x).unwrap();
        }

        // evaluate sum_{j \in [t]} (gamma^j * Lj(x)) over x \in {0,1}^s
        let mut sum_Lj_on_bhc = Fr::zero();
        let vec_L = ccs.compute_L_j_x(z1.clone(), &r_x);
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            for j in 0..vec_L.len() {
                let gamma_j = gamma.pow([j as u64]);
                sum_Lj_on_bhc += vec_L[j].evaluate(&x).unwrap() * gamma_j;
            }
        }

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * Lj(x) over the boolean hypercube
        assert_eq!(g_on_bhc, sum_Lj_on_bhc);
    }
}
