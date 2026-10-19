# Bridging Rust implementations to Lean specifications

How do we connect a cryptographic specification to the code that implements it?
This project explores that question through small, worked examples in Rust and Lean 4.
It supports the [Signal Shot](https://github.com/Beneficial-AI-Foundation/signal-shot)
project's longer-term goal of formally verifying libsignal.

We start with simple examples so that the connection between code and specification is easy
to follow. ML-KEM and erasure coding motivated this work, but their complexity made them less
suitable as starting points. The examples here use generic callbacks and mutable state,
introducing patterns relevant to Rust cryptographic libraries without requiring a large codebase.

## What is bridging?

[Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust programs into Lean definitions.
Its frontend, Charon, first extracts an intermediate representation of the Rust code.
Separately, [VCVio](https://github.com/Verified-zkEVM/VCVio) provides a language for expressing
cryptographic algorithms and reasoning about their behavior in Lean.

Having both in Lean does not automatically connect them. The implementation might use bytes,
structs, and mutable state, while the specification uses mathematical values and oracle queries.
We write **representation maps** to relate these values, then prove that the extracted operations
agree with the specification. That is the bridge.

```mermaid
flowchart LR
    R["Rust implementation"] -->|"Charon + Aeneas"| L["Generated Lean code"]
    L --> B["Representation maps and proofs"]
    B -->|"Proved agreement"| S["Lean specification in VCVio"]
```

Extraction generates the implementation's Lean definitions. The representation maps and proofs
are written by us. They account for returned values, changes to state, and failure behavior.

## The examples

### Commitment: connecting an implementation to a specification

A commitment lets someone commit to a message and reveal it later. Our small Rust implementation
combines a message with a salt obtained from an RNG, passes both to a hash callback, and returns
the digest together with an opening. Verification recomputes the digest from the opening.

The bridge connects these operations to VCVio's existing `CMCommit` and `CMCheck` definitions.
It maps Rust bytes to mathematical bytes and the opening to a message–salt pair. An explicit
contract describes how the hash callback corresponds to the specification's oracle.

We prove that both operations agree with the specification under that contract. When the hash
always succeeds and represents one fixed function, committing and then verifying returns `true`
after a successful RNG draw, with the correct final RNG state. Failed or divergent RNG calls
remain visible in the result.

This establishes conditional correctness. It does not yet prove that a concrete hash satisfies
the contract, that salts are random, or that the scheme hides messages and prevents conflicting
openings. The byte-sized example and its deliberately insecure test hash are educational.

Read the [Rust code](rust/commitment/src/lib.rs), its
[generated Lean translation](Generated/Commitment/Funs.lean), and the
[bridge proofs](BridgingExamples/Commitment/Bridge.lean).

### Lazy Rust implementation, eager VCVio specification

This example compares two ways to assign byte values to the keys `false` and `true`.
The eager specification samples the complete answer table before any query.
The Rust oracle assigns an answer only when a key is first queried, then caches it.
Repeated queries return the cached answer. There are at most two byte requests.

The concrete Rust example does not generate random bytes or call an external randomness library.
`TwoByteRng` is a deterministic fixture that consumes two supplied bytes.
For example, `TwoByteRng::new(7, 19)` always returns `7`, then `19`.
The probability model is introduced in handwritten Lean around the Aeneas translation.
The development separates these steps:

1. Implement byte consumption in Rust. `LazyOracle.query` calls `ByteRng.next_u8` only on a cache miss.
   The trait specifies a byte-returning operation, with no randomness guarantee.
   `TwoByteRng` consumes its supplied bytes in order and panics when exhausted.
2. Translate the implementation with Aeneas. The generated Lean records the operations, state changes, and failure behavior.
   Given a concrete RNG implementation and state, its behavior is deterministic.
   Aeneas introduces no probability distribution or randomness assumption.
3. Introduce randomness in handwritten Lean. `fixtureStates 2` independently samples two uniform values from `Fin 256`, the byte space `0…255`.
   It places them in the translated `TwoByteRng` state.
   `lazyExperiment` samples that initial state, then runs the translated oracle with it.
   This probability layer wraps the generated code without modifying it.
4. State and prove the Lean RNG contract. A contract is a mathematical condition required by the bridge.
   `RngContract.draw` requires each needed draw to succeed and return a uniform byte independent of the remaining RNG state.
   The contract does not generate randomness or test it at runtime.
   `fixtureContract` proves that the translated fixture with `fixtureStates` satisfies this condition.
5. Prove the bridge to the eager specification. `lazy_eq_eager` proves equal client output distributions for any RNG satisfying the contract.
   `fixture_lazy_eq_eager` applies that theorem to the uniformly initialized fixture.
   Clients can choose later queries from earlier answers.

Both concrete Lean experiments sample their randomness before running the client.
The lazy experiment samples an ordered supply of bytes, then assigns bytes to keys on demand.
The eager experiment samples a table whose entries are already assigned to keys.
The theorem compares their output distributions, not individual runs with the same supplied bytes.

The contract is a sufficient condition for the bridge, stronger than independent uniform outputs alone.
It excludes RNGs that keep a log of returned bytes, because that state reveals the returned byte.
The theorem covers query-only clients with one RNG threaded through the calls.
It does not compare internal state, RNG consumption, or timing, and it establishes no operating-system RNG guarantee.

The [eager specification](BridgingExamples/LazyOracle/Spec.lean) contains only the abstract query interface and eager experiment.
The randomness setup, contract, and proofs belong to the bridge:

- [Rust implementation](rust/lazy-oracle/src/lib.rs) and [Aeneas translation](Generated/LazyOracle/Funs.lean).
- [Deterministic cache refinement](BridgingExamples/LazyOracle/Bridge.lean).
- [Lean probability layer, RNG contract, and general bridge](BridgingExamples/LazyOracle/ProbabilityBridge.lean).
- [Uniform initialization, contract proof, and concrete bridge](BridgingExamples/LazyOracle/Fixture.lean).

For an even smaller introduction, the [byte-identity example](BridgingExamples/Smoke.lean)
shows the complete path from an extracted function to a simple mathematical specification.

## Installation

Install [Lean through elan](https://lean-lang.org/install/manual/), along with Git and curl.
The repository selects its Lean version automatically. To check the existing proofs, run these
commands from the project directory in a Bash terminal:

```bash
LEAN_NUM_THREADS=4 nice -n 19 lake exe cache get
LEAN_NUM_THREADS=4 nice -n 19 lake build
```

The generated Lean files are included, so this does not require Rust or the extraction tools.
Lean supports Linux, macOS, and Windows; in a native Windows shell, set `LEAN_NUM_THREADS` to `4`
and run the Lake commands without the Unix `nice` wrapper. This project has been validated
end to end on Linux x86_64; other platforms still need validation.

If you also want to extract the Rust examples yourself, you will need Bash, Python 3, a C
compiler/linker, and the usual archive utilities. The setup script installs the pinned Rust,
Charon, and Aeneas tools locally:

```bash
bash scripts/setup-tools.sh
bash scripts/check.sh
```

Setup selects binaries for Linux x86_64, Linux ARM64, or Apple Silicon macOS. Windows users can
run it inside [WSL2](https://learn.microsoft.com/en-us/windows/wsl/install); Intel Mac users need
a supported Linux environment for extraction. On macOS, install Xcode Command Line Tools first.
The first run downloads dependencies. `check.sh` re-extracts the small byte-identity example and
checks all Lean proofs; the individual extraction scripts are in [scripts/](scripts/).

## Finding your way around

The code follows the same progression as the diagram: [rust/](rust/) contains the implementations
and tests, [Generated/](Generated/) contains Aeneas output, and
[BridgingExamples/](BridgingExamples/) contains the handwritten bridges and proofs.
Generated files should be regenerated rather than edited. Dependency versions are fixed in
[lake-manifest.json](lake-manifest.json) and the setup scripts.

The proofs contain no admissions or new axioms. The `TrustAudit.lean` files report their axiom
dependencies during the build. Some imported Aeneas lemmas emit existing admission warnings,
but those admissions are absent from the audited bridge proofs. The verification still relies
on Lean's kernel and on the Rust-to-Lean translation being faithful.

These examples demonstrate a verification method. They do not yet verify libsignal or provide
production cryptographic implementations.
