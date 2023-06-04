use ark_bls12_381::{Fr, G1Projective};
use ark_std::{One, Zero};
use std::ops::Mul;

use ark_std::{rand::Rng, UniformRand};

use super::util::*;
use crate::ccs::ccs::{CCSError, Matrix, CCS};

use crate::ccs::{
    pedersen,
    pedersen::{Commitment, Params as PedersenParams},
};

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS {
    pub ccs: CCS,

    C: Commitment,
    pub x: Vec<Fr>,
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone)]
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
    pub fn to_lcccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams,
        z: &Vec<Fr>,
        r_x: &Vec<Fr>,
        v: &Vec<Fr>,
    ) -> (LCCCS, Witness) {
        let w: Vec<Fr> = z[(1 + self.l)..].to_vec();
        let r_w = Fr::rand(rng);
        let C = pedersen::commit(&pedersen_params, &w, &r_w);

        (
            LCCCS {
                ccs: self.clone(),
                C,
                u: Fr::one(),
                x: z[1..(1 + self.l)].to_vec(),
                r_x: r_x.clone(),
                v: v.clone(),
            },
            Witness { w, r_w },
        )
    }

    pub fn to_cccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams,
        z: &Vec<Fr>,
    ) -> (CCCS, Witness) {
        let w: Vec<Fr> = z[(1 + self.l)..].to_vec();
        let r_w = Fr::rand(rng);
        let C = pedersen::commit(&pedersen_params, &w, &r_w);

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
    /// Perform the check of the CCCS instance described at section 4.1
    pub fn check_relation(
        self: &Self,
        pedersen_params: &PedersenParams,
        ccs: &CCS,
        w: &Witness,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, pedersen::commit(&pedersen_params, &w.w, &w.r_w).0);

        // check CCS relation
        let z: Vec<Fr> = [vec![Fr::one()], self.x.clone(), w.w.to_vec()].concat();
        ccs.check_relation(&z)
    }
}

impl LCCCS {
    /// Perform the check of the LCCCS instance described at section 4.2
    pub fn check_relation(
        self: &Self,
        pedersen_params: &PedersenParams,
        ccs: &CCS,
        w: &Witness,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, pedersen::commit(&pedersen_params, &w.w, &w.r_w).0);

        // check CCS relation
        let z: Vec<Fr> = [vec![self.u], self.x.clone(), w.w.to_vec()].concat();
        let computed_v = ccs.compute_all_sum_Mz_evals(&z, &self.r_x);
        assert_eq!(computed_v, self.v);
        Ok(())
    }

    pub fn fold(
        lcccs1: &Self,
        cccs2: &CCCS,
        sigmas: Vec<Fr>,
        thetas: Vec<Fr>,
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
    use crate::ccs::ccs::{get_test_ccs, get_test_z};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    #[test]
    fn test_lcccs_fold() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng();
        let r_x: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        let (sigmas, thetas) = ccs.compute_sigmas_and_thetas(&z1, &z2, &r_x_prime);

        let v = ccs.compute_v_j(&z1, &r_x);

        let pedersen_params = pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

        let (lcccs, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1, &r_x, &v);
        let (cccs, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);

        lcccs.check_relation(&pedersen_params, &ccs, &w1).unwrap();
        cccs.check_relation(&pedersen_params, &ccs, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = LCCCS::fold(&lcccs, &cccs, sigmas, thetas, r_x_prime, rho);

        let w_folded = LCCCS::fold_witness(w1, w2, rho);

        // check lcccs relation
        folded
            .check_relation(&pedersen_params, &ccs, &w_folded)
            .unwrap();
    }
}
