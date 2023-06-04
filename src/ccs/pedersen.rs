use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::{scalar_mul::variable_base::VariableBaseMSM, Group};
use std::ops::Mul;

use super::util::{vec_add, vec_scalar_mul};
use transcript::IOPTranscript;

use ark_std::{rand::Rng, UniformRand};

pub struct Proof {
    R: G1Projective,
    u_: Vec<Fr>,
    ru_: Fr,
}

pub struct Params {
    g: G1Projective,
    h: G1Projective,
    pub generators: Vec<G1Affine>, // Affine for the MSM
}

#[derive(Clone, Debug)]
pub struct Commitment(pub G1Projective);

pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params {
    let h_scalar = Fr::rand(rng);
    let g: G1Projective = G1Projective::generator();
    let generators: Vec<G1Affine> = vec![G1Affine::rand(rng); max];
    Params {
        g,
        h: g.mul(h_scalar),
        generators,
    }
}

pub fn commit(
    params: &Params,
    v: &[Fr],
    r: &Fr, // random value is provided, in order to be choosen by other parts of the protocol
) -> Commitment {
    let msm = G1Projective::msm(&params.generators, &v).unwrap();

    let cm = params.h.mul(r) + msm;
    Commitment(cm)
}

pub fn prove(
    params: &Params,
    transcript: &mut IOPTranscript<Fr>,
    cm: &Commitment,
    v: &Vec<Fr>,
    r: &Fr,
) -> Proof {
    let r1 = transcript.get_and_append_challenge(b"r1").unwrap();
    let d = transcript
        .get_and_append_challenge_vectors(b"d", v.len())
        .unwrap();

    let msm = G1Projective::msm(&params.generators, &d).unwrap();
    let R: G1Projective = params.h.mul(r1) + msm;

    transcript
        .append_serializable_element(b"cm", &cm.0)
        .unwrap();
    transcript.append_serializable_element(b"R", &R).unwrap();
    let e = transcript.get_and_append_challenge(b"e").unwrap();

    let u_ = vec_add(&vec_scalar_mul(v, &e), &d);
    let ru_ = e * r + r1;

    Proof { R, u_, ru_ }
}
pub fn verify(
    params: &Params,
    transcript: &mut IOPTranscript<Fr>,
    cm: Commitment,
    proof: Proof,
) -> bool {
    // r1, d just to match Prover's transcript
    transcript.get_and_append_challenge(b"r1").unwrap(); // r_1
    transcript
        .get_and_append_challenge_vectors(b"d", proof.u_.len())
        .unwrap(); // d

    transcript
        .append_serializable_element(b"cm", &cm.0)
        .unwrap();
    transcript
        .append_serializable_element(b"R", &proof.R)
        .unwrap();
    let e = transcript.get_and_append_challenge(b"e").unwrap();
    let lhs = proof.R + cm.0.mul(e);

    let msm = G1Projective::msm(&params.generators, &proof.u_).unwrap();
    let rhs = params.h.mul(proof.ru_) + msm;
    if lhs != rhs {
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pedersen_commitment() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = new_params(&mut rng, n);

        // init Prover's transcript
        let mut transcript_p = IOPTranscript::<Fr>::new(b"pedersen_test");
        transcript_p.append_message(b"init", b"init").unwrap();
        // init Verifier's transcript
        let mut transcript_v = IOPTranscript::<Fr>::new(b"pedersen_test");
        transcript_v.append_message(b"init", b"init").unwrap();

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);

        let cm = commit(&params, &v, &r);
        let proof = prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }
}
