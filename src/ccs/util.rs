/// Some basic utilities
///
/// Stole a bunch of code from Alex in https://github.com/alex-ozdemir/bulletproofs
/// and wrote some lame tests for it
use ark_bls12_381::Fr;
use ark_std::cfg_iter;
use ark_std::Zero;

use crate::ccs::ccs::Matrix; // XXX abstraction leak

/// Hadamard product between two vectors
pub fn hadamard(a: &Vec<Fr>, b: &Vec<Fr>) -> Vec<Fr> {
    cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect()
}

// Multiply matrix by vector
pub fn mat_vec_mul(mat: &Matrix, vec: &[Fr]) -> Vec<Fr> {
    // matrices are lists of rows
    // rows are (value, idx) pairs
    let mut result = vec![Fr::zero(); mat.len()];
    for (r, mat_row) in mat.iter().enumerate() {
        for (c, mat_val) in mat_row.iter().enumerate() {
            assert!(c < vec.len());
            result[r] += *mat_val * vec[c];
        }
    }
    result
}

// Multiply vector by scalar
pub fn vec_scalar_mul(vec: &[Fr], c: &Fr) -> Vec<Fr> {
    let mut result = vec![Fr::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = a * c;
    }
    result
}

// Add two vectors
pub fn vec_add(vec_a: &[Fr], vec_b: &[Fr]) -> Vec<Fr> {
    assert_eq!(vec_a.len(), vec_b.len());

    let mut result = vec![Fr::zero(); vec_a.len()];
    for i in 0..vec_a.len() {
        result[i] = vec_a[i] + vec_b[i];
    }
    result
}

pub fn to_F_matrix(M: Vec<Vec<usize>>) -> Vec<Vec<Fr>> {
    let mut R: Vec<Vec<Fr>> = vec![Vec::new(); M.len()];
    for i in 0..M.len() {
        R[i] = vec![Fr::zero(); M[i].len()];
        for j in 0..M[i].len() {
            R[i][j] = Fr::from(M[i][j] as u64);
        }
    }
    R
}

pub fn to_F_vec(z: Vec<usize>) -> Vec<Fr> {
    let mut r: Vec<Fr> = vec![Fr::zero(); z.len()];
    for i in 0..z.len() {
        r[i] = Fr::from(z[i] as u64);
    }
    r
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_hadamard() -> () {
        let A = vec![
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
            Fr::from(5u64),
            Fr::from(6u64),
        ];

        let B = vec![
            Fr::from(6u64),
            Fr::from(5u64),
            Fr::from(4u64),
            Fr::from(3u64),
            Fr::from(2u64),
            Fr::from(1u64),
        ];

        let C = hadamard(&A, &B);
        assert_eq!(
            C,
            vec![
                Fr::from(6u64),
                Fr::from(10u64),
                Fr::from(12u64),
                Fr::from(12u64),
                Fr::from(10u64),
                Fr::from(6u64)
            ]
        );
    }

    #[test]
    fn test_mat_vec_mul() -> () {
        let A = vec![
            vec![Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)],
            vec![Fr::from(4u64), Fr::from(11u64), Fr::from(14u64)],
            vec![Fr::from(2u64), Fr::from(8u64), Fr::from(17u64)],
        ];
        let v = vec![Fr::from(19u64), Fr::from(55u64), Fr::from(50u64)];

        let result = mat_vec_mul(&A, &v);
        assert_eq!(
            result,
            vec![Fr::from(403u64), Fr::from(1381u64), Fr::from(1328u64)]
        );

        assert_eq!(
            vec_scalar_mul(&result, &Fr::from(2u64)),
            vec![Fr::from(806u64), Fr::from(2762u64), Fr::from(2656u64)]
        );
    }
}
