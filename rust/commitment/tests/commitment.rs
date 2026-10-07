use bridge_commitment::{commit, verify, ByteHash, ByteRng};

// Insecure deterministic test fixture; not a cryptographic hash.
struct FixtureHash;

impl ByteHash for FixtureHash {
    fn hash(&self, message: u8, salt: u8) -> u8 {
        message.wrapping_add(salt)
    }
}

struct SingleByteRng {
    salt: Option<u8>,
    draws: usize,
}

impl ByteRng for SingleByteRng {
    fn next_u8(&mut self) -> u8 {
        self.draws += 1;
        self.salt.take().expect("fixture RNG exhausted")
    }
}

#[test]
fn commit_returns_opening_and_verifies() {
    let mut rng = SingleByteRng { salt: Some(11), draws: 0 };
    let (c, opening) = commit(&FixtureHash, &mut rng, 250);
    assert_eq!(c, 5);
    assert_eq!(opening.message, 250);
    assert_eq!(opening.salt, 11);
    assert_eq!(rng.draws, 1);
    assert!(verify(&FixtureHash, c, &opening));
}

#[test]
fn changed_commitment_is_rejected() {
    let mut rng = SingleByteRng { salt: Some(11), draws: 0 };
    let (c, opening) = commit(&FixtureHash, &mut rng, 7);
    assert_eq!(c, 18);
    assert!(!verify(&FixtureHash, 19, &opening));
}

#[test]
fn verify_does_not_draw() {
    let mut rng = SingleByteRng { salt: Some(11), draws: 0 };
    assert_eq!(rng.draws, 0);
    let (c, opening) = commit(&FixtureHash, &mut rng, 7);
    assert_eq!(rng.draws, 1);
    for _ in 0..3 {
        assert!(verify(&FixtureHash, c, &opening));
        assert!(!verify(&FixtureHash, 19, &opening));
        assert_eq!(rng.draws, 1);
    }
}
