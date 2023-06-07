use ark_ec::CurveGroup;

use crate::util::vec::{vec_add, vec_scalar_mul};
use transcript::IOPTranscript;

use ark_std::{rand::Rng, UniformRand};

use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Proof<C: CurveGroup> {
    R: C,
    u_: Vec<C::ScalarField>,
    ru_: C::ScalarField,
}

#[derive(Clone, Debug)]
pub struct Params<C: CurveGroup> {
    g: C,
    h: C,
    pub generators: Vec<C::Affine>, // Affine for the MSM
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Commitment<C: CurveGroup>(pub C);

#[derive(Clone, Debug)]
pub struct Pedersen<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> Pedersen<C> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let h_scalar = C::ScalarField::rand(rng);
        let g: C = C::generator();
        let generators: Vec<C::Affine> = vec![C::Affine::rand(rng); max];
        Params {
            g,
            h: g.mul(h_scalar),
            generators,
        }
    }

    pub fn commit(
        params: &Params<C>,
        v: &[C::ScalarField],
        r: &C::ScalarField, // random value is provided, in order to be choosen by other parts of the protocol
    ) -> Commitment<C> {
        let msm = C::msm(&params.generators, v).unwrap();

        let cm = params.h.mul(r) + msm;
        Commitment(cm)
    }

    pub fn prove(
        params: &Params<C>,
        transcript: &mut IOPTranscript<C::ScalarField>,
        cm: &Commitment<C>,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Proof<C> {
        let r1 = transcript.get_and_append_challenge(b"r1").unwrap();
        let d = transcript
            .get_and_append_challenge_vectors(b"d", v.len())
            .unwrap();

        let msm = C::msm(&params.generators, &d).unwrap();
        let R: C = params.h.mul(r1) + msm;

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
        params: &Params<C>,
        transcript: &mut IOPTranscript<C::ScalarField>,
        cm: Commitment<C>,
        proof: Proof<C>,
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

        let msm = C::msm(&params.generators, &proof.u_).unwrap();
        let rhs = params.h.mul(proof.ru_) + msm;
        if lhs != rhs {
            return false;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    fn test_pedersen_commitment() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::new_params(&mut rng, n);

        // init Prover's transcript
        let mut transcript_p = IOPTranscript::<Fr>::new(b"pedersen_test");
        transcript_p.append_message(b"init", b"init").unwrap();
        // init Verifier's transcript
        let mut transcript_v = IOPTranscript::<Fr>::new(b"pedersen_test");
        transcript_v.append_message(b"init", b"init").unwrap();

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);

        let cm = Pedersen::<G1Projective>::commit(&params, &v, &r);
        let proof = Pedersen::<G1Projective>::prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = Pedersen::<G1Projective>::verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }
}
