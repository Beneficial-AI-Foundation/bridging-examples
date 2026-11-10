# Bridging Rust implementations to Lean specifications

Examples that connect Rust code to cryptographic specifications in Lean 4, using
[Aeneas](https://github.com/AeneasVerif/aeneas) and
[VCVio](https://github.com/Verified-zkEVM/VCVio).

Each example is a folder `BridgingExamples/<Example>/`:

- **Rust**, in `rust/`: the implementation.
- **Aeneas**, in `Aeneas.lean`: the Lean code that Aeneas generates from it.
- **Spec**, in `Spec.lean`: properties of generated functions.
- **Crypto**, in `Crypto.lean`: cryptographic counterparts, specified in VCVio.
- **Bridge**, in `Bridge.lean`: distributional equivalence of Aeneas and Crypto models.

See the examples in the
[explorer](https://beneficial-ai-foundation.github.io/bridging-examples/). This revision contains
the Rust and Aeneas stages.

## Examples

- **Smoke**: byte identity for an extraction smoke test.
- **Probabilistic Smoke**: fill a buffer from an external random number generator.
- **Byte Mask**: one-byte masking, a fresh random pad combined with the value by XOR.
- **Commitment**: educational byte-sized salted-hash commitment.
- **Modular Masking**: sampling and additive masking modulo q.
- **Encrypt then Mac**: Encrypt then Mac with sampled nonces.
- **One Time Pad**: one-time pad encryption of 16-byte blocks.
- **Lazy Oracle**: a finite lazy oracle with a generic mutable RNG interface.
