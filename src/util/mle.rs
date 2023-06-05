/// Some basic MLE utilities
use ark_bls12_381::Fr;
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, Zero};

use crate::ccs::Matrix; // XXX abstraction leak

/// Pad matrix so that its columns and rows are powers of two
fn pad_matrix(matrix: &Matrix) -> Matrix {
    // Find the desired dimensions after padding
    let rows = matrix.len();
    let cols = matrix[0].len();
    let padded_rows = rows.next_power_of_two();
    let padded_cols = cols.next_power_of_two();

    // Create a new padded matrix
    // XXX inefficient. take a mutable matrix as input instead?
    let mut padded_matrix = vec![vec![Fr::zero(); padded_cols]; padded_rows];

    // Copy values from the input matrix to the padded matrix
    for (i, row) in matrix.iter().enumerate() {
        for (j, &value) in row.iter().enumerate() {
            padded_matrix[i][j] = value;
        }
    }

    padded_matrix
}

// XXX shouldn't consume the matrix
pub fn matrix_to_mle(matrix: Matrix) -> DenseMultilinearExtension<Fr> {
    let n_vars: usize = (log2(matrix.len()) + log2(matrix[0].len())) as usize; // n_vars = s + s'

    // Matrices might need to get padded before turned into an MLE
    let padded_matrix = pad_matrix(&matrix);

    // Flatten matrix into a vector
    let M_evals: Vec<Fr> = padded_matrix.into_iter().flatten().collect();

    vec_to_mle(n_vars, &M_evals)
}

pub fn vec_to_mle(n_vars: usize, v: &Vec<Fr>) -> DenseMultilinearExtension<Fr> {
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
    use crate::{
        ccs::get_test_z,
        espresso::multilinear_polynomial::{fix_last_variables, fix_variables},
        util::{hypercube::BooleanHypercube, vec::to_F_matrix},
    };
    use ark_poly::MultilinearExtension;

    #[test]
    fn test_matrix_to_mle() {
        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4],
            vec![4, 11, 14, 14],
            vec![2, 8, 17, 17],
            vec![420, 4, 2, 0],
        ]);

        let A_mle = matrix_to_mle(A);
        assert_eq!(A_mle.evaluations.len(), 16); // 4x4 matrix, thus 2bit x 2bit, thus 2^4=16 evals

        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4, 1],
            vec![4, 11, 14, 14, 2],
            vec![2, 8, 17, 17, 3],
            vec![420, 4, 2, 0, 4],
            vec![420, 4, 2, 0, 5],
        ]);
        let A_mle = matrix_to_mle(A.clone());
        assert_eq!(A_mle.evaluations.len(), 64); // 5x5 matrix, thus 3bit x 3bit, thus 2^6=64 evals

        // check that the A_mle evaluated over the boolean hypercube equals the matrix A_i_j values
        let bhc = BooleanHypercube::new(A_mle.num_vars);
        let A_padded = pad_matrix(&A);
        for (i, A_i) in A_padded.iter().enumerate() {
            for (j, _) in A_i.iter().enumerate() {
                let s_i_j = bhc.at_i(i * A_i.len() + j);
                assert_eq!(A_mle.evaluate(&s_i_j).unwrap(), A_padded[i][j]);
            }
        }
    }

    #[test]
    fn test_vec_to_mle() {
        let z = get_test_z(3);
        let n_vars = 3;
        let z_mle = vec_to_mle(n_vars, &z);

        // check that the z_mle evaluated over the boolean hypercube equals the vec z_i values
        let bhc = BooleanHypercube::new(z_mle.num_vars);
        for i in 0..z.len() {
            let s_i = bhc.at_i(i);
            assert_eq!(z_mle.evaluate(&s_i).unwrap(), z[i]);
        }
        // for the rest of elements of the boolean hypercube, expect it to evaluate to zero
        for i in (z.len())..(1 << z_mle.num_vars) {
            let s_i = bhc.at_i(i);
            assert_eq!(z_mle.evaluate(&s_i).unwrap(), Fr::zero());
        }
    }

    #[test]
    fn test_fix_variables() {
        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4],
            vec![4, 11, 14, 14],
            vec![2, 8, 17, 17],
            vec![420, 4, 2, 0],
        ]);

        let A_mle = matrix_to_mle(A.clone());
        let bhc = BooleanHypercube::new(2);
        for (i, y) in bhc.enumerate() {
            // First check that the arkworks and espresso funcs match
            let expected_fix_left = A_mle.fix_variables(&y); // try arkworks fix_variables
            let fix_left = fix_variables(&A_mle, &y); // try espresso fix_variables

            assert_eq!(fix_left, expected_fix_left);

            // Check that fixing first variables pins down a column
            // i.e. fixing x to 0 will return the first column
            //      fixing x to 1 will return the second column etc.
            let column_i: Vec<Fr> = A.clone().iter().map(|x| x[i]).collect();
            assert_eq!(fix_left.evaluations, column_i);

            // Now check that fixing last variables pins down a row
            // i.e. fixing y to 0 will return the first row
            //      fixing y to 1 will return the second row etc.
            let row_i: Vec<Fr> = A[i].clone();
            let fix_right = fix_last_variables(&A_mle, &y);
            assert_eq!(fix_right.evaluations, row_i);
        }
    }
}
