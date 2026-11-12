import BridgingExamples.Smoke.Bridge

/-! The axioms of the Smoke theorems. `lake build` fails if either list changes, for example when
a proof gains a `sorry` or a new axiom. -/

/-- info: 'smoke.Spec.identity_byte_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Spec.identity_byte_spec

/-- info: 'smoke.Bridge.identity_byte_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Bridge.identity_byte_bridge
