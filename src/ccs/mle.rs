/// Some basic MLE utilities
use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_std::Zero;

use crate::ccs::ccs::Matrix; // XXX abstraction leak

// XXX shouldn't consume the matrix
pub fn matrix_to_mle(n_vars: usize, matrix: Matrix) -> DenseMultilinearExtension<Fr> {
    // Flatten matrix into a vector
    let mut M_evals: Vec<Fr> = matrix.into_iter().flatten().collect();

    // XXX is this a reasonable thing to do in the case where it's not a power of two??

    // If it's not a power of two, pad to the power of two
    M_evals.extend(std::iter::repeat(Fr::zero()).take((1 << n_vars) - M_evals.len()));

    vec_to_mle(n_vars, M_evals)
}

pub fn vec_to_mle(n_vars: usize, v: Vec<Fr>) -> DenseMultilinearExtension<Fr> {
    DenseMultilinearExtension::<Fr>::from_evaluations_vec(n_vars, v)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mle() {
        let A = vec![
            vec![
                Fr::from(2u64),
                Fr::from(3u64),
                Fr::from(4u64),
                Fr::from(4u64),
            ],
            vec![
                Fr::from(4u64),
                Fr::from(11u64),
                Fr::from(14u64),
                Fr::from(14u64),
            ],
            vec![
                Fr::from(2u64),
                Fr::from(8u64),
                Fr::from(17u64),
                Fr::from(17u64),
            ],
            vec![
                Fr::from(420u64),
                Fr::from(4u64),
                Fr::from(2u64),
                Fr::from(0u64),
            ],
        ];

        let _mle = matrix_to_mle(4, A);
        // XXX useless test
    }
}
