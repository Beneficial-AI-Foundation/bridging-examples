//! Encrypt then Mac with sampled nonces.

// `?` extracts to axioms (`Try::branch`, `FromResidual::from_residual`); `match` does not.
#![allow(clippy::question_mark)]

pub type Key = [u8; 32];
pub type Block = [u8; 16];
pub type Nonce = [u8; 12];
pub type Tag = [u8; 16];

/// A stateful source of key bytes. Uniformity and independence are separate assumptions.
pub trait KeyRng {
    /// Draw a key, or `None` if the source fails.
    fn next_key(&mut self) -> Option<Key>;
}

/// A stateful nonce source. Sampling does not guarantee distinct outputs.
pub trait NonceRng {
    /// Draw a nonce, or `None` if the source fails.
    fn next_nonce(&mut self) -> Option<Nonce>;
}

/// An encryption key and a MAC key.
pub struct Keys {
    pub enc_key: Key,
    pub mac_key: Key,
}

/// Draw the encryption key, then the MAC key. Returns `None` if a draw fails.
pub fn keygen<R: KeyRng>(rng: &mut R) -> Option<Keys> {
    let enc_key = match rng.next_key() {
        Some(key) => key,
        None => return None,
    };
    let mac_key = match rng.next_key() {
        Some(key) => key,
        None => return None,
    };
    Some(Keys { enc_key, mac_key })
}

/// A cipher on one block, under a key and a nonce.
pub trait Cipher {
    /// Encrypt a block.
    fn encrypt(&self, key: &Key, nonce: &Nonce, message: &Block) -> Block;
    /// Decrypt a block, or `None` on failure.
    fn decrypt(&self, key: &Key, nonce: &Nonce, ciphertext: &Block) -> Option<Block>;
}

/// A MAC over a nonce and a ciphertext block.
pub trait Mac {
    /// Compute the tag.
    fn authenticate(&self, key: &Key, nonce: &Nonce, ciphertext: &Block) -> Tag;
    /// Check the tag.
    fn verify(&self, key: &Key, nonce: &Nonce, ciphertext: &Block, tag: &Tag) -> bool;
}

/// A nonce, the encrypted block, and the tag over both.
pub struct Ciphertext {
    pub nonce: Nonce,
    pub body: Block,
    pub tag: Tag,
}

/// Draw a nonce, encrypt the message, and authenticate the nonce and ciphertext.
pub fn encrypt<R: NonceRng, E: Cipher, M: Mac>(
    rng: &mut R,
    cipher: &E,
    mac: &M,
    keys: &Keys,
    message: &Block,
) -> Option<Ciphertext> {
    let nonce = match rng.next_nonce() {
        Some(nonce) => nonce,
        None => return None,
    };
    let body = cipher.encrypt(&keys.enc_key, &nonce, message);
    let tag = mac.authenticate(&keys.mac_key, &nonce, &body);
    Some(Ciphertext { nonce, body, tag })
}

/// Verify the tag, then decrypt. Returns `None` if either fails.
pub fn decrypt<E: Cipher, M: Mac>(
    cipher: &E,
    mac: &M,
    keys: &Keys,
    ciphertext: &Ciphertext,
) -> Option<Block> {
    if !mac.verify(
        &keys.mac_key,
        &ciphertext.nonce,
        &ciphertext.body,
        &ciphertext.tag,
    ) {
        return None;
    }
    cipher.decrypt(&keys.enc_key, &ciphertext.nonce, &ciphertext.body)
}
