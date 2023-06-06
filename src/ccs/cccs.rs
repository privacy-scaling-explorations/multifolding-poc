use std::ops::Add;
use ark_bls12_381::Fr;
use ark_std::One;
use ark_std::Zero;
use std::sync::Arc;

use ark_std::{rand::Rng, UniformRand};

use crate::ccs::ccs::{CCSError, CCS};
use crate::ccs::util::{compute_sum_Mz};

use crate::espresso::virtual_polynomial::VirtualPolynomial;
use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen};
use crate::util::hypercube::BooleanHypercube;
use crate::util::mle::matrix_to_mle;
use crate::util::mle::vec_to_mle;

/// Witness for the LCCCS & CCCS, containing the w vector, but also the r_w used as randomness in
/// the Pedersen commitment.
#[derive(Debug, Clone)]
pub struct Witness {
    pub w: Vec<Fr>,
    pub r_w: Fr, // randomness used in the Pedersen commitment of w
}

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS {
    pub ccs: CCS,

    pub C: Commitment,
    pub x: Vec<Fr>,
}

impl CCS {
    pub fn to_cccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams,
        z: &[Fr],
    ) -> (CCCS, Witness) {
        let w: Vec<Fr> = z[(1 + self.l)..].to_vec();
        let r_w = Fr::rand(rng);
        let C = Pedersen::commit(pedersen_params, &w, &r_w);

        (
            CCCS {
                ccs: self.clone(),
                C,
                x: z[1..(1 + self.l)].to_vec(),
            },
            Witness { w, r_w },
        )
    }
}

impl CCCS {
    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_q(&self, z: &Vec<Fr>) -> VirtualPolynomial<Fr> {
        let z_mle = vec_to_mle(self.ccs.s_prime, z);
        let mut q = VirtualPolynomial::<Fr>::new(self.ccs.s);

        for i in 0..self.ccs.q {
            let mut prod: VirtualPolynomial<Fr> = VirtualPolynomial::<Fr>::new(self.ccs.s);
            for j in self.ccs.S[i].clone() {
                let M_j = matrix_to_mle(self.ccs.M[j].clone());

                let sum_Mz = compute_sum_Mz(M_j, &z_mle, self.ccs.s_prime);

                // Fold this sum into the running product
                if prod.products.is_empty() {
                    // If this is the first time we are adding something to this virtual polynomial, we need to
                    // explicitly add the products using add_mle_list()
                    // XXX is this true? improve API
                    prod.add_mle_list([Arc::new(sum_Mz)], Fr::one()).unwrap();
                } else {
                    prod.mul_by_mle(Arc::new(sum_Mz), Fr::one()).unwrap();
                }
            }
            // Multiply by the product by the coefficient c_i
            prod.scalar_mul(&self.ccs.c[i]);
            // Add it to the running sum
            q = q.add(&prod);
        }
        q
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_Q(&self, z: &Vec<Fr>, beta: &[Fr]) -> VirtualPolynomial<Fr> {
        let q = self.compute_q(z);
        q.build_f_hat(beta).unwrap()
    }

    /// Perform the check of the CCCS instance described at section 4.1
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams,
        w: &Witness,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, Pedersen::commit(pedersen_params, &w.w, &w.r_w).0);

        // check CCCS relation
        let z: Vec<Fr> = [vec![Fr::one()], self.x.clone(), w.w.to_vec()].concat();

        // A CCCS relation is satisfied if the q(x) multivariate polynomial evaluates to zero in the hypercube
        let q_x = self.compute_q(&z);
        for x in BooleanHypercube::new(self.ccs.s) {
            if !q_x.evaluate(&x).unwrap().is_zero() {
                return Err(CCSError::NotSatisfied);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::ccs::ccs::{get_test_ccs, get_test_z};
    use ark_std::test_rng;
    use ark_std::UniformRand;


    #[test]
    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    fn test_compute_q() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (cccs, _) = ccs.to_cccs(&mut rng, &pedersen_params, &z);
        let q = cccs.compute_q(&z);

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            assert_eq!(Fr::zero(), q.evaluate(&x).unwrap());
        }

        // Evaluate outside the hypercube
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        assert_ne!(Fr::zero(), q.evaluate(&beta).unwrap());
    }

    #[test]
    fn test_compute_Q() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (cccs, _) = ccs.to_cccs(&mut rng, &pedersen_params, &z);

        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Q = cccs.compute_Q(&z, &beta);

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
            .map(|x| Q.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_eq!(r, Fr::zero());
    }
}
