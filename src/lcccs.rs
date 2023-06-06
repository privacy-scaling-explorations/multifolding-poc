use std::ops::Add;
use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_std::One;
use ark_std::Zero;
use std::ops::Mul;
use std::sync::Arc;

use ark_std::{rand::Rng, UniformRand};

use crate::ccs::{CCSError, CCS};

use crate::espresso::virtual_polynomial::VirtualPolynomial;
use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen};
use crate::util::hypercube::BooleanHypercube;
use crate::util::mle::matrix_to_mle;
use crate::util::mle::vec_to_mle;

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS {
    pub ccs: CCS,

    C: Commitment,
    pub x: Vec<Fr>,
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LCCCS {
    pub ccs: CCS,

    pub C: Commitment, // Pedersen commitment of w
    pub u: Fr,
    pub x: Vec<Fr>,
    pub r_x: Vec<Fr>,
    pub v: Vec<Fr>,
}

/// Witness for the LCCCS & CCCS, containing the w vector, but also the r_w used as randomness in
/// the Pedersen commitment.
#[derive(Debug, Clone)]
pub struct Witness {
    pub w: Vec<Fr>,
    pub r_w: Fr, // randomness used in the Pedersen commitment of w
}

impl CCS {
    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    fn compute_v_j(&self, z: &Vec<Fr>, r: &[Fr]) -> Vec<Fr> {
        self.compute_all_sum_Mz_evals(z, r)
    }

    pub fn to_lcccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams,
        z: &[Fr],
    ) -> (LCCCS, Witness) {
        let w: Vec<Fr> = z[(1 + self.l)..].to_vec();
        let r_w = Fr::rand(rng);
        let C = Pedersen::commit(pedersen_params, &w, &r_w);

        let r_x: Vec<Fr> = (0..self.s).map(|_| Fr::rand(rng)).collect();
        let v = self.compute_v_j(&z.to_vec(), &r_x);

        (
            LCCCS {
                ccs: self.clone(),
                C,
                u: Fr::one(),
                x: z[1..(1 + self.l)].to_vec(),
                r_x: r_x,
                v: v,
            },
            Witness { w, r_w },
        )
    }

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

                let sum_Mz = self.ccs.compute_sum_Mz(M_j, &z_mle);

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

impl LCCCS {
    /// Compute all L_j(x) polynomials
    pub fn compute_Ls(&self, z: &Vec<Fr>, r_x: &[Fr]) -> Vec<VirtualPolynomial<Fr>> {
        let z_mle = vec_to_mle(self.ccs.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<Fr>> =
            self.ccs.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut vec_L_j_x = Vec::with_capacity(self.ccs.t);
        for M_j in M_x_y_mle {
            let sum_Mz = self.ccs.compute_sum_Mz(M_j, &z_mle);
            let sum_Mz_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), Fr::one());
            let L_j_x = sum_Mz_virtual.build_f_hat(r_x).unwrap();
            vec_L_j_x.push(L_j_x);
        }

        vec_L_j_x
    }


    /// Perform the check of the LCCCS instance described at section 4.2
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams,
        w: &Witness,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, Pedersen::commit(pedersen_params, &w.w, &w.r_w).0);

        // check CCS relation
        let z: Vec<Fr> = [vec![self.u], self.x.clone(), w.w.to_vec()].concat();
        let computed_v = self.ccs.compute_all_sum_Mz_evals(&z, &self.r_x);
        assert_eq!(computed_v, self.v);
        Ok(())
    }

    pub fn fold(
        lcccs1: &Self,
        cccs2: &CCCS,
        sigmas: &[Fr],
        thetas: &[Fr],
        r_x_prime: Vec<Fr>,
        rho: Fr,
    ) -> Self {
        let C = Commitment(lcccs1.C.0 + cccs2.C.0.mul(rho));
        let u = lcccs1.u + rho;
        let x: Vec<Fr> = lcccs1
            .x
            .iter()
            .zip(cccs2.x.iter().map(|x_i| *x_i * rho).collect::<Vec<Fr>>())
            .map(|(a_i, b_i)| *a_i + b_i)
            .collect();
        let v: Vec<Fr> = sigmas
            .iter()
            .zip(thetas.iter().map(|x_i| *x_i * rho).collect::<Vec<Fr>>())
            .map(|(a_i, b_i)| *a_i + b_i)
            .collect();

        Self {
            C,
            ccs: lcccs1.ccs.clone(),
            u,
            x,
            r_x: r_x_prime,
            v,
        }
    }

    pub fn fold_witness(w1: Witness, w2: Witness, rho: Fr) -> Witness {
        let w: Vec<Fr> =
            w1.w.iter()
                .zip(w2.w.iter().map(|x_i| *x_i * rho).collect::<Vec<Fr>>())
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();
        let r_w = w1.r_w + rho * w2.r_w;
        Witness { w, r_w }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::ccs::{get_test_ccs, get_test_z};
    use crate::multifolding::Multifolding;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_lcccs_v_j() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z);

        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        let vec_L_j_x = lcccs.compute_Ls(&z, &lcccs.r_x);
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
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

    #[test]
    fn test_lcccs_fold() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (running_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1);
        let (new_instance, _) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);
        let multifolding = Multifolding {
            running_instance: running_instance.clone(),
            cccs_instance: new_instance.clone(),
        };

        let (sigmas, thetas) = multifolding.compute_sigmas_and_thetas(&z1, &z2, &r_x_prime);

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

        let (lcccs, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1);
        let (cccs, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);

        lcccs.check_relation(&pedersen_params, &w1).unwrap();
        cccs.check_relation(&pedersen_params, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = LCCCS::fold(&lcccs, &cccs, &sigmas, &thetas, r_x_prime, rho);

        let w_folded = LCCCS::fold_witness(w1, w2, rho);

        // check lcccs relation
        folded.check_relation(&pedersen_params, &w_folded).unwrap();
    }
}
