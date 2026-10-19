use bridge_lazy_oracle::{LazyOracle, TwoByteRng};

#[test]
fn first_draw_is_assigned_to_first_queried_key() {
    let mut oracle = LazyOracle::new();
    let mut rng = TwoByteRng::new(7, 19);
    assert_eq!(oracle.query(true, &mut rng), 7);
    assert_eq!(oracle.query(true, &mut rng), 7);
    assert_eq!((rng.next, rng.tail), (Some(19), None));
    assert_eq!(oracle.query(false, &mut rng), 19);
    assert_eq!((oracle.false_value, oracle.true_value), (Some(19), Some(7)));
    assert_eq!((rng.next, rng.tail), (None, None));
}

#[test]
fn miss_consumes_one_and_caches() {
    let mut oracle = LazyOracle::new();
    let mut rng = TwoByteRng::new(7, 19);
    assert_eq!(oracle.query(false, &mut rng), 7);
    assert_eq!((oracle.false_value, oracle.true_value), (Some(7), None));
    assert_eq!((rng.next, rng.tail), (Some(19), None));
    assert_eq!(oracle.query(true, &mut rng), 19);
    assert_eq!((oracle.false_value, oracle.true_value), (Some(7), Some(19)));
    assert_eq!((rng.next, rng.tail), (None, None));
}

#[test]
fn hit_keeps_rng_state() {
    let mut oracle = LazyOracle { false_value: Some(73), true_value: Some(41) };
    let mut rng = TwoByteRng { next: None, tail: None };
    assert_eq!(oracle.query(false, &mut rng), 73);
    assert_eq!((oracle.false_value, oracle.true_value), (Some(73), Some(41)));
    assert_eq!((rng.next, rng.tail), (None, None));
}

#[test]
fn adaptive_repeat_is_stable() {
    let mut oracle = LazyOracle::new();
    let mut rng = TwoByteRng::new(7, 19);
    let first = oracle.query(false, &mut rng);
    let second_key = first == 7;
    let second = oracle.query(second_key, &mut rng);
    assert_eq!((first, second), (7, 19));
    assert_eq!(oracle.query(false, &mut rng), first);
    assert_eq!(oracle.query(second_key, &mut rng), second);
    assert_eq!((oracle.false_value, oracle.true_value), (Some(7), Some(19)));
    assert_eq!((rng.next, rng.tail), (None, None));
}

#[test]
#[should_panic(expected = "entropy exhausted")]
fn exhausted_rng_panics_on_miss() {
    let mut oracle = LazyOracle::new();
    let mut rng = TwoByteRng { next: None, tail: None };
    oracle.query(false, &mut rng);
}
