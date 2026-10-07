# Extraction assumptions

- Aeneas: `5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`.
- Charon: `4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`.
- Rust: `nightly-2026-08-18`, default distributed sysroot.
- Coverage: all functions in this crate. No opaque functions, exclusions, or semantic repairs.
- The usual Rust-to-Lean translation trust boundary remains; this is not a proof of the extractor itself.
- No randomness or cryptographic assumptions are introduced by this deterministic probe.
