Examples connecting Rust code to cryptographic specifications in Lean 4, using
[Aeneas](https://github.com/AeneasVerif/aeneas) and [VCVio](https://github.com/Verified-zkEVM/VCVio). 

Each example is in a folder `BridgingExamples/<Example>/` containing:

- **Rust**: the implementation of a cryptographic primitive.
- **Aeneas**: the Lean models that Aeneas extracted from the implementation.
- **Spec**: functional properties of extracted functions.
- **Crypto**: cryptographic Lean models for the extracted functions, specified in VCVio.
- **Bridge**: distributional equivalence of Aeneas and Crypto models, under assumed probabilistic specifications for externally called functions.

## Examples

See [explorer](https://beneficial-ai-foundation.github.io/bridging-examples/).

- [**Smoke**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=Smoke): byte identity for an extraction smoke test.
- [**Probabilistic Smoke**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=ProbSmoke): fill a buffer from an external random number generator.
- [**Byte Mask**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=ByteMask): one-byte masking, a fresh random pad combined with the value by XOR.
- [**Commitment**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=Commitment): educational byte-sized salted-hash commitment.
- [**Modular Masking**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=ModularMasking): sampling and additive masking modulo q.
- [**Encrypt then Mac**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=EtM): Encrypt then Mac with sampled nonces.
- [**One Time Pad**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=OneTimePad): one-time pad encryption of 16-byte blocks.
- [**Lazy Oracle**](https://beneficial-ai-foundation.github.io/bridging-examples/#example=LazyOracle): a finite lazy oracle with a generic mutable RNG interface.
