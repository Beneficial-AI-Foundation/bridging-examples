//! A finite lazy oracle with a generic mutable RNG interface.

/// A source of bytes. This interface makes no randomness guarantee.
pub trait ByteRng {
    fn next_u8(&mut self) -> u8;
}

pub struct LazyOracle {
    pub false_value: Option<u8>,
    pub true_value: Option<u8>,
}

impl LazyOracle {
    pub fn new() -> Self {
        Self {
            false_value: None,
            true_value: None,
        }
    }

    pub fn query<R: ByteRng>(&mut self, key: bool, rng: &mut R) -> u8 {
        let cached = if key {
            self.true_value
        } else {
            self.false_value
        };
        match cached {
            Some(value) => value,
            None => {
                let value = rng.next_u8();
                if key {
                    self.true_value = Some(value);
                } else {
                    self.false_value = Some(value);
                }
                value
            }
        }
    }
}

/// A deterministic fixture that consumes at most two supplied entropy bytes.
pub struct TwoByteRng {
    pub next: Option<u8>,
    pub tail: Option<u8>,
}

impl TwoByteRng {
    pub fn new(first: u8, second: u8) -> Self {
        Self {
            next: Some(first),
            tail: Some(second),
        }
    }
}

impl ByteRng for TwoByteRng {
    fn next_u8(&mut self) -> u8 {
        match self.next {
            Some(value) => {
                self.next = self.tail;
                self.tail = None;
                value
            }
            None => panic!("entropy exhausted"),
        }
    }
}
