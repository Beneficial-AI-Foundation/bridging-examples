//! One-time pad encryption of 16-byte blocks.

use rand::CryptoRng;

pub type Block = [u8; 16];
pub type Key = [u8; 16];

/// Fill a 16-byte key with RNG output.
pub fn keygen<R: CryptoRng>(rng: &mut R) -> Key {
    let mut key = [0u8; 16];
    rng.fill_bytes(&mut key);
    key
}

/// XOR the key into the message, byte by byte.
pub fn encrypt(key: &Key, message: &Block) -> Block {
    let mut ciphertext = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        ciphertext[i] = key[i] ^ message[i];
        i += 1;
    }
    ciphertext
}

/// XOR the key into the ciphertext, by calling [`encrypt`].
pub fn decrypt(key: &Key, ciphertext: &Block) -> Block {
    encrypt(key, ciphertext)
}
