//! Minimal extraction probe, before introducing the cryptographic examples.

/// Preserve a byte across the Rust/Aeneas/Lean representation boundary.
pub fn identity_byte(value: u8) -> u8 {
    value
}
