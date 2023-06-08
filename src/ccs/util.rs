use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use std::ops::Add;

use crate::espresso::multilinear_polynomial::fix_variables;
use crate::espresso::multilinear_polynomial::scalar_mul;

use crate::util::hypercube::BooleanHypercube;
use crate::util::mle::matrix_to_mle;
use crate::util::mle::vec_to_mle;
use crate::util::vec::Matrix;

/// Return a vector of evaluations p_j(r) = \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
/// for all j values in 0..self.t
pub fn compute_all_sum_Mz_evals<F: PrimeField>(
    vec_M: &[Matrix<F>],
    z: &Vec<F>,
    r: &[F],
    s_prime: usize,
) -> Vec<F> {
    // Convert z to MLE
    let z_y_mle = vec_to_mle(s_prime, z);
    // Convert all matrices to MLE
    let M_x_y_mle: Vec<DenseMultilinearExtension<F>> =
        vec_M.iter().cloned().map(matrix_to_mle).collect();

    let mut v = Vec::with_capacity(M_x_y_mle.len());
    for M_i in M_x_y_mle {
        let sum_Mz = compute_sum_Mz(M_i, &z_y_mle, s_prime);
        let v_i = sum_Mz.evaluate(r).unwrap();
        v.push(v_i);
    }
    v
}

/// Return the multilinear polynomial p(x) = \sum_{y \in {0,1}^s'} M_j(x, y) * z(y)
pub fn compute_sum_Mz<F: PrimeField>(
    M_j: DenseMultilinearExtension<F>,
    z: &DenseMultilinearExtension<F>,
    s_prime: usize,
) -> DenseMultilinearExtension<F> {
    let mut sum_Mz = DenseMultilinearExtension {
        evaluations: vec![F::zero(); M_j.evaluations.len()],
        num_vars: M_j.num_vars - s_prime,
    };

    let bhc = BooleanHypercube::new(s_prime);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let M_j_y = fix_variables(&M_j, &y);
        let z_y = z.evaluate(&y).unwrap();
        let M_j_z = scalar_mul(&M_j_y, &z_y);
        sum_Mz = sum_Mz.add(M_j_z);
    }
    sum_Mz
}

#[cfg(test)]
pub mod test {
    use super::*;

    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::test_rng;
    use ark_std::One;
    use ark_std::UniformRand;
    use ark_std::Zero;

    use crate::ccs::ccs::get_test_ccs;
    use crate::ccs::ccs::get_test_z;
    use crate::espresso::multilinear_polynomial::fix_last_variables;
    use crate::espresso::virtual_polynomial::eq_eval;

    use crate::ccs::util::compute_sum_Mz;

    #[test]
    fn test_compute_sum_Mz_over_boolean_hypercube() -> () {
        let ccs = get_test_ccs::<G1Projective>();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();
        let z_mle = vec_to_mle(ccs.s_prime, &z);

        // check that evaluating over all the values x over the boolean hypercube, the result of
        // the next for loop is equal to 0
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            // println!("x {:?}", x);
            let mut r = Fr::zero();
            for i in 0..ccs.q {
                let mut Sj_prod = Fr::one();
                for j in ccs.S[i].clone() {
                    let M_j = matrix_to_mle(ccs.M[j].clone());
                    let sum_Mz = compute_sum_Mz(M_j, &z_mle, ccs.s_prime);
                    let sum_Mz_x = sum_Mz.evaluate(&x).unwrap();
                    Sj_prod *= sum_Mz_x;
                }
                r += Sj_prod * ccs.c[i];
            }
            assert_eq!(r, Fr::zero());
        }
    }

    /// Given M(x,y) matrix and a random field element `r`, test that ~M(r,y) is is an s'-variable polynomial which
    /// compresses every column j of the M(x,y) matrix by performing a random linear combination between the elements
    /// of the column and the values eq_i(r) where i is the row of that element
    ///
    /// For example, for matrix M:
    ///
    /// [2, 3, 4, 4
    ///  4, 4, 3, 2
    ///  2, 8, 9, 2
    ///  9, 4, 2, 0]
    ///
    /// The polynomial ~M(r,y) is a polynomial in F^2 which evaluates to the following values in the hypercube:
    /// - M(00) = 2*eq_00(r) + 4*eq_10(r) + 2*eq_01(r) + 9*eq_11(r)
    /// - M(10) = 3*eq_00(r) + 4*eq_10(r) + 8*eq_01(r) + 4*eq_11(r)
    /// - M(01) = 4*eq_00(r) + 3*eq_10(r) + 9*eq_01(r) + 2*eq_11(r)
    /// - M(11) = 4*eq_00(r) + 2*eq_10(r) + 2*eq_01(r) + 0*eq_11(r)
    ///
    /// This is used by Hypernova in LCCCS to perform a verifier-chosen random linear combination between the columns
    /// of the matrix and the z vector. This technique is also used extensively in "An Algebraic Framework for
    /// Universal and Updatable SNARKs".
    #[test]
    fn test_compute_M_r_y_compression() -> () {
        let mut rng = test_rng();

        // s = 2, s' = 3
        let ccs = get_test_ccs::<G1Projective>();

        let M = ccs.M[0].clone();
        let M_mle = matrix_to_mle(M.clone());

        // Fix the polynomial ~M(r,y)
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let M_r_y = fix_last_variables(&M_mle, &r);

        // Now let's compute M_r_y the other way around
        for j in 0..M[0].len() {
            // Go over every column of M
            let column_j: Vec<Fr> = M.clone().iter().map(|x| x[j]).collect();

            // and perform the random lincomb between the elements of the column and eq_i(r)
            let rlc = BooleanHypercube::new(ccs.s)
                .enumerate()
                .into_iter()
                .map(|(i, x)| column_j[i] * eq_eval(&x, &r).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);

            assert_eq!(M_r_y.evaluations[j], rlc);
        }
    }
}
