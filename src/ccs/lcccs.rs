use ark_ec::CurveGroup;
use ark_poly::DenseMultilinearExtension;
use ark_std::One;
use std::sync::Arc;

use ark_std::{rand::Rng, UniformRand};

use crate::ccs::cccs::Witness;
use crate::ccs::cccs::CCCS;
use crate::ccs::ccs::{CCSError, CCS};
use crate::ccs::util::{compute_all_sum_Mz_evals, compute_sum_Mz};

use crate::ccs::pedersen::{Commitment, Params as PedersenParams, Pedersen};
use crate::espresso::virtual_polynomial::VirtualPolynomial;
use crate::util::mle::matrix_to_mle;
use crate::util::mle::vec_to_mle;

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LCCCS<C: CurveGroup> {
    pub ccs: CCS<C>,

    pub C: Commitment<C>, // Pedersen commitment of w
    pub u: C::ScalarField,
    pub x: Vec<C::ScalarField>,
    pub r_x: Vec<C::ScalarField>,
    pub v: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    fn compute_v_j(&self, z: &[C::ScalarField], r: &[C::ScalarField]) -> Vec<C::ScalarField> {
        compute_all_sum_Mz_evals(&self.M, &z.to_vec(), r, self.s_prime)
    }

    pub fn to_lcccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams<C>,
        z: &[C::ScalarField],
    ) -> (LCCCS<C>, Witness<C::ScalarField>) {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();
        let r_w = C::ScalarField::rand(rng);
        let C = Pedersen::commit(pedersen_params, &w, &r_w);

        let r_x: Vec<C::ScalarField> = (0..self.s).map(|_| C::ScalarField::rand(rng)).collect();
        let v = self.compute_v_j(z, &r_x);

        (
            LCCCS::<C> {
                ccs: self.clone(),
                C,
                u: C::ScalarField::one(),
                x: z[1..(1 + self.l)].to_vec(),
                r_x,
                v,
            },
            Witness::<C::ScalarField> { w, r_w },
        )
    }
}

impl<C: CurveGroup> LCCCS<C> {
    /// Compute all L_j(x) polynomials
    pub fn compute_Ls(
        &self,
        z: &Vec<C::ScalarField>,
        r_x: &[C::ScalarField],
    ) -> Vec<VirtualPolynomial<C::ScalarField>> {
        let z_mle = vec_to_mle(self.ccs.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<C::ScalarField>> =
            self.ccs.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut vec_L_j_x = Vec::with_capacity(self.ccs.t);
        for M_j in M_x_y_mle {
            let sum_Mz = compute_sum_Mz(M_j, &z_mle, self.ccs.s_prime);
            let sum_Mz_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), C::ScalarField::one());
            let L_j_x = sum_Mz_virtual.build_f_hat(r_x).unwrap();
            vec_L_j_x.push(L_j_x);
        }

        vec_L_j_x
    }

    /// Perform the check of the LCCCS instance described at section 4.2
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams<C>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, Pedersen::commit(pedersen_params, &w.w, &w.r_w).0);

        // check CCS relation
        let z: Vec<C::ScalarField> = [vec![self.u], self.x.clone(), w.w.to_vec()].concat();
        let computed_v = compute_all_sum_Mz_evals(&self.ccs.M, &z, &self.r_x, self.ccs.s_prime);
        assert_eq!(computed_v, self.v);
        Ok(())
    }

    pub fn fold(
        lcccs1: &Self,
        cccs2: &CCCS<C>,
        sigmas: &[C::ScalarField],
        thetas: &[C::ScalarField],
        r_x_prime: Vec<C::ScalarField>,
        rho: C::ScalarField,
    ) -> Self {
        let C = Commitment(lcccs1.C.0 + cccs2.C.0.mul(rho));
        let u = lcccs1.u + rho;
        let x: Vec<C::ScalarField> = lcccs1
            .x
            .iter()
            .zip(
                cccs2
                    .x
                    .iter()
                    .map(|x_i| *x_i * rho)
                    .collect::<Vec<C::ScalarField>>(),
            )
            .map(|(a_i, b_i)| *a_i + b_i)
            .collect();
        let v: Vec<C::ScalarField> = sigmas
            .iter()
            .zip(
                thetas
                    .iter()
                    .map(|x_i| *x_i * rho)
                    .collect::<Vec<C::ScalarField>>(),
            )
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

    pub fn fold_witness(
        w1: &Witness<C::ScalarField>,
        w2: &Witness<C::ScalarField>,
        rho: C::ScalarField,
    ) -> Witness<C::ScalarField> {
        let w: Vec<C::ScalarField> =
            w1.w.iter()
                .zip(
                    w2.w.iter()
                        .map(|x_i| *x_i * rho)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();
        let r_w = w1.r_w + rho * w2.r_w;
        Witness { w, r_w }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use ark_std::Zero;

    use crate::ccs::ccs::test::{get_test_ccs, get_test_z};
    use crate::multifolding::Multifolding;
    use crate::util::hypercube::BooleanHypercube;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_lcccs_v_j() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
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

    /// Given a bad z, check that the v_j should not match with the L_j(x)
    #[test]
    fn test_bad_v_j() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        // Mutate z so that the relation does not hold
        let mut bad_z = z.clone();
        bad_z[3] = Fr::zero();
        assert!(ccs.check_relation(&bad_z.clone()).is_err());

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        // Compute v_j with the right z
        let (lcccs, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z);
        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        // Bad compute L_j(x) with the bad z
        let vec_L_j_x = lcccs.compute_Ls(&bad_z, &lcccs.r_x);
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        // Make sure that the LCCCS is not satisfied given these L_j(x)
        // i.e. summing L_j(x) over the hypercube should not give v_j for all j
        let mut satisfied = true;
        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .into_iter()
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            if v_i != sum_L_j_x {
                satisfied = false;
            }
        }

        assert_eq!(satisfied, false);
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
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (running_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1);

        let (sigmas, thetas) = Multifolding::<G1Projective>::compute_sigmas_and_thetas(
            &running_instance.ccs,
            &z1,
            &z2,
            &r_x_prime,
        );

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);

        let (lcccs, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1);
        let (cccs, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);

        lcccs.check_relation(&pedersen_params, &w1).unwrap();
        cccs.check_relation(&pedersen_params, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = LCCCS::<G1Projective>::fold(&lcccs, &cccs, &sigmas, &thetas, r_x_prime, rho);

        let w_folded = LCCCS::<G1Projective>::fold_witness(&w1, &w2, rho);

        // check lcccs relation
        folded.check_relation(&pedersen_params, &w_folded).unwrap();
    }
}
