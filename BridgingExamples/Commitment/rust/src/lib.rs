//! Educational byte-sized salted-hash commitment.
//!
//! The interfaces impose no randomness or cryptographic security guarantee.
//! Correctness across commit and verify requires hash calls to terminate
//! successfully and return one fixed function of message and salt.
//! An immutable receiver alone does not establish this requirement.

/// A source of bytes, used for the salt.
pub trait ByteRng {
    /// Draw the next byte.
    fn next_u8(&mut self) -> u8;
}

/// A hash of a message byte and a salt byte.
pub trait ByteHash {
    /// Hash the message with the salt.
    fn hash(&self, message: u8, salt: u8) -> u8;
}

/// The message and salt that open a commitment.
pub struct Opening {
    pub message: u8,
    pub salt: u8,
}

/// Draw a salt and hash the message with it. Returns the commitment and its opening.
pub fn commit<H: ByteHash, R: ByteRng>(hash: &H, rng: &mut R, message: u8) -> (u8, Opening) {
    let salt = rng.next_u8();
    let commitment = hash.hash(message, salt);
    (commitment, Opening { message, salt })
}

/// Hash the opening and compare the result with the commitment.
pub fn verify<H: ByteHash>(hash: &H, commitment: u8, opening: &Opening) -> bool {
    commitment == hash.hash(opening.message, opening.salt)
}
