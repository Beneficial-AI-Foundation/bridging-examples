# Assumptions and coverage

All extracted functions remain in scope. The extraction uses no opaque replacements,
semantic repairs, or new axioms. `ByteRng` is a generic callback interface. It does
not guarantee randomness.

## Where randomness enters

The Rust `TwoByteRng` consumes two supplied bytes deterministically. It calls no
external randomness library and fails when exhausted. Aeneas translates that
behavior, including the state changes and failure path. The generated Lean does
not supply probability distributions or assert that the supplied bytes are uniform.

A handwritten Lean probability layer wraps the generated operations.
`fixtureStates 2` in `BridgingExamples/LazyOracle/Fixture.lean` samples two independent
uniform values from `Fin 256` and places them in the translated RNG state.
`lazyExperiment` in `ProbabilityBridge.lean` samples this initial state and then
runs the translated oracle. The generated code is not modified to add randomness.

Both bytes are sampled before the client runs. The oracle consumes them and assigns
them to keys only on cache misses. Thus the implementation uses lazy assignment
from a random byte supply. The eager specification samples a complete table with
values already assigned to keys.

## Contract and bridge

`RngContract` is a handwritten Lean structure in the bridge layer. Its `states`
field supplies the RNG state distributions. Its `draw` field requires a proof of
the conditions on the translated draw operation. It does not generate randomness,
change the Rust behavior, or perform a runtime randomness test.

The contract requires successful uniform draws whose returned byte is independent
of the remaining RNG state. This excludes RNGs that retain a log of returned bytes,
even when their output bytes are independent and uniform. It is a sufficient
condition for the theorem and covers at most two draws. No draw law is required
at budget zero, because the oracle then has both answers cached.

`fixtureContract` proves this condition for the translated `TwoByteRng` under
`fixtureStates`. `lazy_eq_eager` proves equal client output distributions assuming
such a contract. `fixture_lazy_eq_eager` then applies that theorem with the proved
fixture contract. Uniform initialization and its contract proof are required
parts of this concrete result. Neither follows from the Rust trait or extraction alone.

`Spec.lean` defines only the abstract query interface and the eager experiment.
The implementation's probability layer, contract, and proofs belong to the bridge.
This development establishes no randomness guarantee for an operating-system RNG.

## Observation and trust boundaries

Clients access the oracle through queries, with one RNG threaded through the calls.
They do not inspect or modify the cache or RNG state, or consume RNG bytes between
queries. The theorem compares client outputs, not timing or RNG consumption.
The Rust fields are public, so this restriction is part of the experiment interface.

Pins: Aeneas `5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust `nightly-2026-08-18`, and Lean
`4.31.0`. The bridge relies on faithful Rust-to-Lean extraction and Lean checking.
It does not prove compiler correctness or cryptographic security.
