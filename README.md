# Hypernova multifolding

A complete implementation of the [Hypernova](https://eprint.iacr.org/2023/573) folding scheme (see section 5 of the paper) in arkworks.

This implementation is not meant to be used in production. Its purpose is to help us refine the interfaces and abstractions, so that multifolding can be integrated into a wider Hypernova implementation. A complete Hypernova implementation includes IVC, an in-circuit multifolding verifier, and R1CS-to-CCS and Plonkish-to-CCS compilers.


<center>
<img
    width="65%"
    src="https://github.com/privacy-scaling-explorations/multifolding-poc/raw/main/doc/images/multifolding_diagram.png"
/>
</center>

## Documentation

See `src/multifolding.rs:test_multifolding()` for a demonstration of the multifolding.

See `TODO.md` for open future tasks.

## Building & Running

As usual, you can run the tests using `cargo test --release`.

## Acknowledgements

Shoutout to Espresso Systems for the [Hyperplonk implementation](https://github.com/EspressoSystems/hyperplonk/tree/main/arithmetic/src) that included useful multivariate polynomial routines.
