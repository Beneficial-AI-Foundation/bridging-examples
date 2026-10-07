# Semantics and remaining obligations

commit calls next_u8 once, then hash(message,salt) once, on the normal-return path. The extracted Result monad propagates callback failure/divergence; successful output includes the updated RNG state and self-contained opening. verify has no RNG parameter, calls hash once, and returns equality as Bool inside Result. Shared hash receiver produces no returned hash state; Rust interior/global-state behavior is not thereby proven pure.

The next bridge must explicitly interpret successful hash calls by one fixed total function and relate U8 to Fin 256, Opening to message/salt, and RNG state. RNG success and distribution are separate obligations. CMCommit accepts salt explicitly, whereas Rust samples it internally. No cryptographic correctness, hiding, binding, or randomness claim is proved in n1. Wrapping addition is an insecure tests-only fixture.

Pinned extraction: Aeneas 5b9dcf33dccdb1560ea7203ac57ea202476b6ed3; Charon 4ad295c1bf982b5533ce7d85f4ddc889ff3127f8; Rust nightly-2026-08-18. Extraction tooling and Rust-to-Lean correspondence remain trust boundaries.
