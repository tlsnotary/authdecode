# AUTHDECODE

This crates implements the AUTHDECODE functionality described in the [`tlsn` repo](https://github.com/tlsnotary/tlsn/pull/39). It uses the [`ark-poly-commit`](https://github.com/arkworks-rs/poly-commit) crate for proofs that are generic over polynomial commitment schemes.

What is implemented:

* The `R_binary` relation has a prover and verifier, and unit tests
* Selective revelation is implemented and benchmarked. To see the benchmarks, run `cargo test --release -- --nocapture`
* The skeleton of the `R_decode` prover

What remains to be done:

* Complete the implementation of `R_decode`. The protocol is simple, but it seems that `ark-poly-commit` is missing a definition of scalar multiplication on commitments. This is necessary in order to compute the `Δ·com_p` term in `R_decode`. Fortunately, it exposes [addition](https://docs.rs/ark-poly-commit/0.3.0/ark_poly_commit/kzg10/struct.Commitment.html#impl-AddAssign%3C(%3CE%20as%20PairingEngine%3E%3A%3AFr%2C%20%26%27a%20Commitment%3CE%3E)%3E) on the relevant types, so scalar multiplication isn't far off.
* Optional: implement the `R_pack` protocol to pack plaintext bits into bytes
* Use [`merlin`](https://docs.rs/merlin/latest/merlin/index.html) transcripts to generate challenges. Currently, they're just placeholder values. A secure Fiat-Shamir'ed protocol should be hashing the whole transcript.
* Ensure proper hiding for plaintext polynomials. It might already be the case that this works, via the `supported_hiding_bound` in [`PolynomialCommitment::trim`](https://docs.rs/ark-poly-commit/0.3.0/ark_poly_commit/trait.PolynomialCommitment.html#tymethod.trim).
