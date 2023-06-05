use ark_bls12_381::Fr;
use ark_ff::Field;
use ark_std::{One, Zero};

use subroutines::PolyIOP;
use transcript::IOPTranscript;

use crate::espresso::sum_check::structs::IOPProof as SumCheckProof;
use crate::espresso::sum_check::{verifier::interpolate_uni_poly, SumCheck};
use crate::espresso::virtual_polynomial::VPAuxInfo;
use crate::lcccs::{Witness, CCCS, LCCCS};
use crate::util::hypercube::BooleanHypercube;

use std::marker::PhantomData;

#[derive(Debug)]
pub struct Multifolding {
    // currently an empty struct, but leaving it with this structure and its impl as in a near
    // future we will move it to use generics.
}

impl Multifolding {
    /// Perform the multifolding prover side, compute its proof, compute the folded LCCCS and the
    /// folded witness.
    fn prove(
        running_instance: &LCCCS,
        new_instance: &CCCS,
        w_1: Witness,
        w_2: Witness,
    ) -> (SumCheckProof<Fr>, Vec<Fr>, Vec<Fr>, LCCCS, Witness) {
        let mut transcript = IOPTranscript::<Fr>::new(b"multifolding");
        transcript.append_message(b"init", b"init").unwrap();
        // TODO appends to transcript

        // construct the z vectors from witness and LCCCS & CCCS x vector
        let z_1: Vec<Fr> = [vec![Fr::one()], running_instance.x.clone(), w_1.w.to_vec()].concat();
        let z_2: Vec<Fr> = [vec![Fr::one()], new_instance.x.clone(), w_2.w.to_vec()].concat();

        let ccs = &running_instance.ccs;

        let gamma: Fr = transcript.get_and_append_challenge(b"gamma").unwrap();
        let beta: Vec<Fr> = transcript
            .get_and_append_challenge_vectors(b"beta", ccs.s)
            .unwrap();

        // compute g(x)
        let g = ccs.compute_g(&z_1, &z_2, gamma, &beta, &running_instance.r_x);

        let sc_proof = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&g, &mut transcript).unwrap(); // XXX unwrap

        // Note: The following two "sanity checks" are done for this prototype, in a final version
        // can be removed for efficiency.
        //
        // Sanity check 1: evaluate g(x) over x \in {0,1} (the boolean hypercube), and check that
        // its sum is equal to the extracted_sum from the SumCheck.
        //////////////////////////////////////////////////////////////////////
        let mut g_over_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s) {
            g_over_bhc += g.evaluate(&x).unwrap();
        }

        // note: this is the sum of g(x) over the whole boolean hypercube, not g(r_x_prime)
        let extracted_sum = <PolyIOP<Fr> as SumCheck<Fr>>::extract_sum(&sc_proof);
        assert_eq!(extracted_sum, g_over_bhc);
        // Sanity check 2: expect \sum v_j * gamma^j to be equal to the sum of g(x) over the
        // boolean hypercube (and also equal to the extracted_sum from the SumCheck).
        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..running_instance.v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += running_instance.v[j] * gamma_j;
        }
        assert_eq!(g_over_bhc, sum_v_j_gamma);
        assert_eq!(extracted_sum, sum_v_j_gamma);
        //////////////////////////////////////////////////////////////////////

        // get r_x' from the SumCheck used challenge (which inside the SC it comes from the transcript)
        let r_x_prime = sc_proof.point.clone();

        // Compute sigmas and thetas
        let (sigmas, thetas) = ccs.compute_sigmas_and_thetas(&z_1, &z_2, &r_x_prime);

        let rho: Fr = transcript.get_and_append_challenge(b"rho").unwrap();

        // fold instance
        let folded_lcccs = LCCCS::fold(
            running_instance,
            new_instance,
            &sigmas,
            &thetas,
            r_x_prime,
            rho,
        );
        // fold witness
        let folded_witness = LCCCS::fold_witness(w_1, w_2, rho);

        (sc_proof, sigmas, thetas, folded_lcccs, folded_witness)
    }

    /// Perform the multifolding verifier side and compute the folded LCCCS instance.
    fn verify(
        running_instance: &LCCCS,
        new_instance: &CCCS,
        proof: SumCheckProof<Fr>,
        sigmas: &[Fr],
        thetas: &[Fr],
    ) -> LCCCS {
        let mut transcript = IOPTranscript::<Fr>::new(b"multifolding");
        transcript.append_message(b"init", b"init").unwrap();
        // TODO appends to transcript

        let ccs = &running_instance.ccs;

        let gamma: Fr = transcript.get_and_append_challenge(b"gamma").unwrap();
        let beta: Vec<Fr> = transcript
            .get_and_append_challenge_vectors(b"beta", ccs.s)
            .unwrap();

        let vp_aux_info = VPAuxInfo::<Fr> {
            max_degree: ccs.d + 1,
            num_variables: ccs.s,
            phantom: PhantomData::<Fr>,
        };

        // Compute \sum gamma^j u_j
        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..running_instance.v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += running_instance.v[j] * gamma_j;
        }

        // verify sumcheck
        let sc_subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
            sum_v_j_gamma,
            &proof,
            &vp_aux_info,
            &mut transcript,
        )
        .unwrap();

        // Dig into the sumcheck claim and extract the randomness used
        let r_x_prime = sc_subclaim.point.clone();

        // Step 5 from the multifolding verification
        let c = ccs.compute_c_from_sigmas_and_thetas(
            sigmas,
            thetas,
            gamma,
            &beta,
            &running_instance.r_x,
            &r_x_prime,
        );
        // check that the g(r_x') from SumCheck proof is equal to the obtained c from sigmas&thetas
        assert_eq!(c, sc_subclaim.expected_evaluation);

        // Sanity check: we can also compute g(r_x') from the proof last evaluation value, and
        // should be equal to the previously obtained values.
        let g_on_rxprime_from_SC_last_eval = interpolate_uni_poly::<Fr>(
            &proof.proofs.last().unwrap().evaluations,
            *r_x_prime.last().unwrap(),
        )
        .unwrap();
        assert_eq!(g_on_rxprime_from_SC_last_eval, c);
        assert_eq!(
            g_on_rxprime_from_SC_last_eval,
            sc_subclaim.expected_evaluation
        );

        let rho: Fr = transcript.get_and_append_challenge(b"rho").unwrap();

        // fold instance and return it
        LCCCS::fold(
            running_instance,
            new_instance,
            sigmas,
            thetas,
            r_x_prime,
            rho,
        )
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::ccs::{get_test_ccs, get_test_z};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use crate::pedersen::Pedersen;

    #[test]
    pub fn test_multifolding() {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        // LCCCS witness
        let z_1 = get_test_z(3);
        // CCS witness
        let z_2 = get_test_z(4);

        // Compute some parts of the input LCCCS instance
        // XXX move to its own structure
        let r_x: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let v = ccs.compute_v_j(&z_1, &r_x);

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (running_instance, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z_1, &r_x, &v);
        let (new_instance, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z_2);

        // run the prover side of the multifolding
        let (sumcheck_proof, sigmas, thetas, folded_lcccs, folded_witness) =
            Multifolding::prove(&running_instance, &new_instance, w1, w2);

        // run the verifier side of the multifolding
        let folded_lcccs_v = Multifolding::verify(
            &running_instance,
            &new_instance,
            sumcheck_proof,
            &sigmas,
            &thetas,
        );

        assert_eq!(folded_lcccs, folded_lcccs_v);

        // check that the folded instance with the folded witness holds the LCCCS relation
        folded_lcccs
            .check_relation(&pedersen_params, &folded_witness)
            .unwrap();
    }
}
