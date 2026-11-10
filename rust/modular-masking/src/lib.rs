//! Sampling and additive masking modulo q.

use rand::{Rng, RngCore};

/// Sample an integer in 0..q.
pub fn sample_range<R: RngCore>(rng: &mut R, q: u32) -> u32 {
    rng.random_range(0..q)
}

/// Sample a residue modulo q.
pub fn random_field<R: RngCore>(rng: &mut R, q: u32) -> u32 {
    sample_range(rng, q)
}

/// Add the value and pad modulo q, using a 64-bit intermediate sum.
pub fn field_mask(q: u32, value: u32, pad: u32) -> u32 {
    ((value as u64 + pad as u64) % q as u64) as u32
}

/// Sample a pad in 0..q and add it to the input modulo q.
pub fn random_mask<R: RngCore>(rng: &mut R, q: u32, value: u32) -> u32 {
    let pad = random_field(rng, q);
    field_mask(q, value, pad)
}
