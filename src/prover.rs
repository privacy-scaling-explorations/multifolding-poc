use ark_bls12_381::Fr;
use ark_ff::Field;
use ark_std::Zero;

use subroutines::PolyIOP;
use transcript::IOPTranscript;

use crate::ccs::ccs::CCS;
use crate::espresso::sum_check::SumCheck;

pub struct Multifolding {}
impl Multifolding {
    // XXX should take CCS instances as input and not plain z_1/z_2
    fn prove(ccs: CCS, z_1: &Vec<Fr>, z_2: &Vec<Fr>) {
        let mut transcript = IOPTranscript::<Fr>::new(b"multifolding");
        transcript.append_message(b"TMP", b"TMP").unwrap();
        // TODO appends to transcript

        let gamma: Fr = transcript.get_and_append_challenge(b"gamma").unwrap();
        let beta: Vec<Fr> = transcript
            .get_and_append_challenge_vectors(b"beta", ccs.s)
            .unwrap();
        let r_x: Vec<Fr> = transcript
            .get_and_append_challenge_vectors(b"beta", ccs.s)
            .unwrap();
        let r_x_prime: Vec<Fr> = transcript
            .get_and_append_challenge_vectors(b"beta", ccs.s)
            .unwrap();

        // compute g(x)
        let g_x = ccs.compute_g(&z_1, &z_2, gamma, &beta, &r_x);

        let res = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&g_x, &mut transcript).unwrap(); // XXX unwrap
        let c = <PolyIOP<Fr> as SumCheck<Fr>>::extract_sum(&res);

        // XXX verifier should verify the sumcheck

        // Sanity check result of sumcheck
        let vec_v = ccs.compute_v_j(&z_1, &r_x);
        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..vec_v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += vec_v[j] * gamma_j;
        }
        assert_eq!(c, sum_v_j_gamma);

        // Compute sigmas and thetas
        let (sigmas, thetas) = ccs.compute_sigmas_and_thetas(&z_1, &z_2, &r_x_prime);

        // Verifier: Do the step 5 verification // note, maybe this will be moved to verifier side
        let c =
            ccs.compute_c_from_sigmas_and_thetas(&sigmas, &thetas, gamma, &beta, &r_x, &r_x_prime);
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::ccs::ccs::{gen_z, get_test_ccs};
    use ark_std::test_rng;
    // use ark_std::{rand::RngCore, UniformRand};

    #[test]
    pub fn test_prover() {
        let ccs = get_test_ccs();
        let z_1 = gen_z(3);
        let z_2 = gen_z(4);

        Multifolding::prove(ccs, &z_1, &z_2);
    }
}
