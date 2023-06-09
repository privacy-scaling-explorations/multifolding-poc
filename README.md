# Hypernova multifolding

An arkworks implementation of the folding scheme of [Hypernova](https://eprint.iacr.org/2023/573) (see section 5 of the paper).

This is a complete implementation of the multifolding scheme, but it's not meant to be used in production. It's main purpose is to show that multifolding works, and to help us refine the interfaces and abstractions required, so that multifolding can be implemented as part of a wider Hypernova implementation. A proper Hypernova implementation includes IVC, an in-circuit multifolding verifier, and R1CS-to-CCS and Plonkish-to-CCS compilers.


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






