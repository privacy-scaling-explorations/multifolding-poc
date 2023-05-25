/// Some basic MLE utilities
use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, Zero};

use crate::ccs::ccs::Matrix; // XXX abstraction leak

// XXX shouldn't consume the matrix
pub fn matrix_to_mle(matrix: Matrix) -> DenseMultilinearExtension<Fr> {
    let n_vars: usize = (log2(matrix.len()) + log2(matrix[0].len())) as usize; // n_vars = s + s'

    // Flatten matrix into a vector
    let mut M_evals: Vec<Fr> = matrix.into_iter().flatten().collect();

    // XXX is this a reasonable thing to do in the case where it's not a power of two of n_vars??

    // Pad to 2^n_vars
    M_evals.extend(std::iter::repeat(Fr::zero()).take((1 << n_vars) - M_evals.len()));

    vec_to_mle(n_vars, M_evals)
}

pub fn vec_to_mle(n_vars: usize, v: Vec<Fr>) -> DenseMultilinearExtension<Fr> {
    // Pad to 2^n_vars
    let v_padded: Vec<Fr> = [
        v.clone(),
        std::iter::repeat(Fr::zero())
            .take((1 << n_vars) - v.len())
            .collect(),
    ]
    .concat();
    DenseMultilinearExtension::<Fr>::from_evaluations_vec(n_vars, v_padded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccs::util::to_F_matrix;

    #[test]
    fn test_matrix_to_mle() {
        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4],
            vec![4, 11, 14, 14],
            vec![2, 8, 17, 17],
            vec![420, 4, 2, 0],
        ]);

        let mle = matrix_to_mle(A);
        assert_eq!(mle.evaluations.len(), 16); // 4x4 matrix, thus 2bit x 2bit, thus 2^4=16 evals

        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4, 1],
            vec![4, 11, 14, 14, 2],
            vec![2, 8, 17, 17, 3],
            vec![420, 4, 2, 0, 4],
            vec![420, 4, 2, 0, 5],
        ]);
        let mle = matrix_to_mle(A);
        assert_eq!(mle.evaluations.len(), 64); // 5x5 matrix, thus 3bit x 3bit, thus 2^6=64 evals
    }
}
