# Assumptions and coverage

All extracted functions remain in scope. The extraction uses no opaque replacements,
semantic repairs, or new axioms. `ByteRng` is a generic callback interface. It does
not guarantee randomness.

The eager VCVio specification samples a complete `Bool → Fin 256` table before
answering queries. The Rust implementation draws only on cache misses.
`lazy_eq_eager` proves equal client output distributions under `RngContract`.
The contract specifies a joint law for each draw and the remaining RNG state.
It requires successful uniform draws whose returned byte is independent of the
remaining RNG state. This excludes RNGs that retain a log of returned bytes,
even when their output bytes are independent and uniform. The contract is a
sufficient condition for the theorem and covers at most two draws.

`TwoByteRng` is a deterministic fixture. It fails when exhausted. `fixtureContract`
proves the contract when Lean supplies independent uniform initial entropy.
`fixture_lazy_eq_eager` specializes the general bridge to this fixture. The proof
does not establish this contract for an operating-system RNG.

Clients access the oracle through queries. They do not inspect or modify its cache
or RNG state. The theorem compares client outputs, not timing or RNG consumption.
The Rust fields are public, so this restriction is part of the experiment interface.

Pins: Aeneas `5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust `nightly-2026-08-18`, and Lean
`4.31.0`. The bridge relies on faithful Rust-to-Lean extraction and Lean checking.
It does not prove compiler correctness or cryptographic security.
