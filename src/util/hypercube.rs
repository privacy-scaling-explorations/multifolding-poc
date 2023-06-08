/// A boolean hypercube structure to create an ergonomic evaluation domain
use crate::espresso::virtual_polynomial::bit_decompose;
use ark_ff::PrimeField;

use std::marker::PhantomData;

/// A boolean hypercube that returns its points as an iterator
/// If you iterate on it for 3 variables you will get points in little-endian order:
/// 000 -> 100 -> 010 -> 110 -> 001 -> 101 -> 011 -> 111
#[derive(Debug)]
pub struct BooleanHypercube<F: PrimeField> {
    _f: PhantomData<F>,
    n_vars: usize,
    current: u64,
    max: u64,
}

impl<F: PrimeField> BooleanHypercube<F> {
    pub fn new(n_vars: usize) -> Self {
        BooleanHypercube::<F> {
            _f: PhantomData::<F>,
            n_vars,
            current: 0,
            max: 2_u32.pow(n_vars as u32) as u64,
        }
    }

    /// returns the entry at given i (which is the little-endian bit representation of i)
    pub fn at_i(&self, i: usize) -> Vec<F> {
        assert!(i < self.max as usize);
        let bits = bit_decompose((i) as u64, self.n_vars);
        bits.iter().map(|&x| F::from(x)).collect()
    }
}

impl<F: PrimeField> Iterator for BooleanHypercube<F> {
    type Item = Vec<F>;

    fn next(&mut self) -> Option<Self::Item> {
        let bits = bit_decompose(self.current, self.n_vars);
        let result: Vec<F> = bits.iter().map(|&x| F::from(x)).collect();
        self.current += 1;

        if self.current > self.max {
            return None;
        }

        Some(result)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn test_hypercube() -> () {
        for (i, point) in BooleanHypercube::<Fr>::new(3).enumerate() {
            println!("#{}: {:?}", i, point);
            // TODO: this is not a test...
        }
    }
}
