# Assumptions and coverage

All extracted functions are required coverage. No opaque replacements, external RNG implementation, semantic repairs, or new axioms were introduced. ByteRng is an explicit generic dictionary input, not a randomness guarantee. The concrete TwoByteRng is deterministic and fails when exhausted. Uniform initial entropy and its joint residual-state law remain future Lean proof work.

Pins: Aeneas 5b9dcf33dccdb1560ea7203ac57ea202476b6ed3; Charon binary 4ad295c1bf982b5533ce7d85f4ddc889ff3127f8; Rust nightly-2026-08-18; Lean 4.31.0. The existing binary/pin checker passed. Aeneas source checkout matches the pinned revision. No Charon source clone was needed or used; source-clone staleness is unavailable, binary version matches the pin. No upstream freshness claim.

Trust remains in Rust compilation, Charon/Aeneas translation, and Lean checking. This extraction does not prove cryptographic security or Rust-to-Lean compiler correctness.
