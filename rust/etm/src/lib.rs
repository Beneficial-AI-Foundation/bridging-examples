//! Encrypt then Mac with sampled nonces.

pub type Key = [u8; 32];
pub type Block = [u8; 16];
pub type Nonce = [u8; 12];

/// A stateful source of key bytes. Uniformity and independence are separate assumptions.
pub trait KeyRng {
    fn next_key(&mut self) -> Option<Key>;
}

/// A stateful nonce source. Sampling does not guarantee distinct outputs.
pub trait NonceRng {
    fn next_nonce(&mut self) -> Option<Nonce>;
}

pub struct Keys {
    pub enc_key: Key,
    pub mac_key: Key,
}

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

pub trait Cipher {
    fn encrypt(&self, key: &Key, nonce: &Nonce, message: &Block) -> Block;
    fn decrypt(&self, key: &Key, nonce: &Nonce, ciphertext: &Block) -> Option<Block>;
}

pub trait Mac {
    fn authenticate(&self, key: &Key, nonce: &Nonce, ciphertext: &Block) -> Block;
    fn verify(&self, key: &Key, nonce: &Nonce, ciphertext: &Block, tag: &Block) -> bool;
}

pub struct Ciphertext {
    pub nonce: Nonce,
    pub body: Block,
    pub tag: Block,
}

/// Draw a nonce, encrypt the message, and authenticate the nonce and ciphertext.
pub fn encrypt<R: NonceRng, E: Cipher, M: Mac>(
    rng: &mut R,
    cipher: &E,
    mac: &M,
    enc_key: &Key,
    mac_key: &Key,
    message: &Block,
) -> Option<Ciphertext> {
    let nonce = match rng.next_nonce() {
        Some(nonce) => nonce,
        None => return None,
    };
    let body = cipher.encrypt(enc_key, &nonce, message);
    let tag = mac.authenticate(mac_key, &nonce, &body);
    Some(Ciphertext { nonce, body, tag })
}

pub fn decrypt<E: Cipher, M: Mac>(
    cipher: &E,
    mac: &M,
    enc_key: &Key,
    mac_key: &Key,
    ciphertext: &Ciphertext,
) -> Option<Block> {
    if !mac.verify(
        mac_key,
        &ciphertext.nonce,
        &ciphertext.body,
        &ciphertext.tag,
    ) {
        return None;
    }
    cipher.decrypt(enc_key, &ciphertext.nonce, &ciphertext.body)
}
