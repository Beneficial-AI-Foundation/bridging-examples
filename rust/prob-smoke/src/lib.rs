//! Fill a buffer from an external random number generator.

use rand::RngCore;

/// Fill the buffer with bytes from the generator.
pub fn fill_random<R: RngCore>(rng: &mut R, buffer: &mut [u8]) {
    rng.fill_bytes(buffer)
}
