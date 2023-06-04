use ark_bls12_381::Fr;
use ark_std::{One, Zero};

use super::util::*;
use crate::ccs::ccs::{CCSError, CCSParams, Matrix, CCS};

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS {
    pub params: CCSParams,

    // C: Commitment<C>,
    pub x: Vec<Fr>,
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone)]
pub struct LCCCS {
    pub params: CCSParams,

    // C: Commitment<C>,
    pub u: Fr,
    pub x: Vec<Fr>,
    pub r_x: Vec<Fr>,
    pub v: Vec<Fr>,
}

impl CCS {
    pub fn to_lcccs(&self, z: &Vec<Fr>, r_x: &Vec<Fr>, v: &Vec<Fr>) -> (LCCCS, Vec<Fr>) {
        (
            LCCCS {
                params: self.params.clone(),
                u: Fr::one(),
                x: z[1..(1 + self.params.l)].to_vec(),
                r_x: r_x.clone(),
                v: v.clone(),
            },
            z[(1 + self.params.l)..].to_vec(), // w
        )
    }

    pub fn to_cccs(&self, z: &Vec<Fr>) -> (CCCS, Vec<Fr>) {
        (
            CCCS {
                params: self.params.clone(),
                x: z[1..(1 + self.params.l)].to_vec(),
            },
            z[(1 + self.params.l)..].to_vec(), // w
        )
    }
}

impl CCCS {
    /// Perform the check of the CCCS instance described at section 4.1
    pub fn check_relation(self: &Self, ccs: &CCS, w: &Vec<Fr>) -> Result<(), CCSError> {
        let z: Vec<Fr> = [vec![Fr::one()], self.x.clone(), w.to_vec()].concat();
        ccs.check_relation(&z)
    }
}

impl LCCCS {
    /// Perform the check of the LCCCS instance described at section 4.2
    pub fn check_relation(self: &Self, ccs: &CCS, w: &Vec<Fr>) -> Result<(), CCSError> {
        let z: Vec<Fr> = [vec![self.u], self.x.clone(), w.to_vec()].concat();
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
        // let C = lcccs1.C + rho * lcccs2.C;
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
            params: lcccs1.params.clone(),
            u,
            x,
            r_x: r_x_prime,
            v,
        }
    }

    pub fn fold_witness(w1: Vec<Fr>, w2: Vec<Fr>, rho: Fr) -> Vec<Fr> {
        let w: Vec<Fr> = w1
            .iter()
            .zip(w2.iter().map(|x_i| *x_i * rho).collect::<Vec<Fr>>())
            .map(|(a_i, b_i)| *a_i + b_i)
            .collect();
        w
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
        let r_x: Vec<Fr> = (0..ccs.params.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.params.s).map(|_| Fr::rand(&mut rng)).collect();

        let (sigmas, thetas) = ccs.compute_sigmas_and_thetas(&z1, &z2, &r_x_prime);

        let v = ccs.compute_v_j(&z1, &r_x);

        let (lcccs, w1) = ccs.to_lcccs(&z1, &r_x, &v);
        let (cccs, w2) = ccs.to_cccs(&z2);

        lcccs.check_relation(&ccs, &w1).unwrap();
        cccs.check_relation(&ccs, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = LCCCS::fold(&lcccs, &cccs, sigmas, thetas, r_x_prime, rho);

        let w_folded = LCCCS::fold_witness(w1, w2, rho);

        // check lcccs relation
        folded.check_relation(&ccs, &w_folded).unwrap();
    }
}
