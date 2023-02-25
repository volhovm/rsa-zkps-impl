# rsa-zkps-impl

This is a prototype implementation of the two protocols, DV, and DVRange, proving knowledge-of-ciphertext, and range, correspondingly, 
of the Paillier encryption scheme variant, in the situation where the prover public key is potentially subverted. 
The problem and the protocols were introduced in the following paper:

**Zero-Knowledge Arguments for Subverted RSA Groups** by *Dimitris Kolonelos, Mary Maller, and Mikhail Volkhov*.

**TODO** insert eprint link.

The implementation in `/src` contains all the protocols: primarily DV (`designated.rs`), DVRange (`designated_range.rs`), and several variants of the basic Sigma protocol (`schnorr_*.rs`). 
We provide our benchmarks in `/bench`, and `/measurement_results` contains results of the benchmarks run for the eprint version of the paper.
