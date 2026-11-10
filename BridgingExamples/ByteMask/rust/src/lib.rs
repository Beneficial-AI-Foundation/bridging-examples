//! One-byte masking: a fresh random pad, combined with the value by XOR.

use rand::RngCore;

/// Mask a byte with a fresh pad. Returns the pad and the masked byte.
pub fn mask<R: RngCore>(rng: &mut R, value: u8) -> (u8, u8) {
    let mut pad = [0u8; 1];
    rng.fill_bytes(&mut pad);
    (pad[0], value ^ pad[0])
}

/// Remove the pad from a masked byte.
pub fn unmask(pad: u8, masked: u8) -> u8 {
    masked ^ pad
}
