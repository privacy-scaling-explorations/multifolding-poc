/// A boolean hypercube structure to create an ergonomic evaluation domain

/// XXX maybe rename it to domain to resemble the univariate case
use ark_bls12_381::Fr;

/// A boolean hypercube that returns its points as an iterator
/// If you iterate on it for 3 variables you will get points in big-endian order:
/// 000 -> 001 -> 010 -> 011 -> 100 -> 101 -> 110 -> 111
pub struct BooleanHypercube {
    n_vars: usize,
    current: u64,
    max: u64,
}

impl BooleanHypercube {
    pub fn new(n_vars: usize) -> Self {
        BooleanHypercube {
            n_vars: n_vars,
            current: 0,
            max: 2_u32.pow(n_vars as u32) as u64,
        }
    }
}

// XXX This works with big endian but bit_decompose from espresso works with little endian!!! Be careful about
// compatibility. We might need to switch this to little endian

/// Decompose an integer into a binary vector in big endian.
pub fn bit_decompose(input: u64, num_var: usize) -> Vec<bool> {
    let mut res = Vec::with_capacity(num_var);
    let mut i = input;
    for _ in 0..num_var {
        res.insert(0, i & 1 == 1);
        i >>= 1;
    }
    res
}

impl Iterator for BooleanHypercube {
    type Item = Vec<Fr>;

    fn next(&mut self) -> Option<Self::Item> {
        let bits = bit_decompose(self.current, self.n_vars);
        let result: Vec<Fr> = bits.iter().map(|&x| Fr::from(x)).collect();
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

    #[test]
    fn test_hypercube() -> () {
        for (i, point) in BooleanHypercube::new(4).enumerate() {
            println!("#{}: {:?}", i, point);
            // XXX this is not a test...
        }
    }
}
