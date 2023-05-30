use ark_bls12_381::Fr;
use ark_ff::Field;
use ark_std::{
    Zero, rand::{RngCore}, UniformRand,
};

use subroutines::PolyIOP;
use transcript::IOPTranscript;

use crate::ccs::ccs::CCS;
use crate::espresso::sum_check::SumCheck;

// XXX should take CCS instances as input and not plain z_1/z_2
fn prove<R: RngCore>(ccs: CCS, z_1: Vec<Fr>, z_2: Vec<Fr>, rng: &mut R) {
    let mut transcript = IOPTranscript::<Fr>::new(b"multifolding");

    // XXX these actually come from the verifier -- pass them to the func
    let gamma: Fr = Fr::rand(rng);
    let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(rng)).collect();
    let r_x: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(rng)).collect();
    let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(rng)).collect();

    // compute g(x)
    let g_x = ccs.compute_g(z_1.clone(), z_2.clone(), gamma, &beta, &r_x);

    let res = <PolyIOP<Fr> as SumCheck::<Fr>>::prove(&g_x, &mut transcript).unwrap(); // XXX unwrap
    let c = <PolyIOP<Fr> as SumCheck::<Fr>>::extract_sum(&res);

    // XXX verifier should verify the sumcheck

    // Sanity check result of sumcheck
    // XXX stupid clone(). make func take references
    let vec_v = ccs.compute_v_j(z_1.clone(), &r_x);
    let mut sum_v_j_gamma = Fr::zero();
    for j in 0..vec_v.len() {
        let gamma_j = gamma.pow([j as u64]);
        sum_v_j_gamma += vec_v[j] * gamma_j;
    }
    assert_eq!(c, sum_v_j_gamma);

    // Compute sigmas and thetas
    let (sigmas, thetas) = ccs.compute_sigmas_and_thetas(z_1, z_2, r_x_prime);

    // Verifier: Do the step 5 verification
}


#[cfg(test)]
pub mod test {
    use super::*;
    use ark_std::test_rng;
    use crate::ccs::ccs::{get_test_ccs, gen_z};

    #[test]
    pub fn test_prover() {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z_1 = gen_z(3);
        let z_2 = gen_z(4);

        prove(ccs, z_1, z_2, &mut rng);
    }
}


