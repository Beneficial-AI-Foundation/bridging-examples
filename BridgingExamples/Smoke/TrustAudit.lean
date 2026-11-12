import BridgingExamples.Smoke.Distributional.Bridge
import BridgingExamples.Smoke.Direct.Bridge

/-! The axioms of the Smoke theorems. `lake build` fails if a list changes, for example when a
proof gains a `sorry` or a new axiom. -/

/-- info: 'smoke.Distributional.Spec.identity_byte_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Distributional.Spec.identity_byte_spec

/-- info: 'smoke.Distributional.Bridge.identity_byte_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Distributional.Bridge.identity_byte_bridge

/-- info: 'smoke.Direct.Spec.identity_byte_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Direct.Spec.identity_byte_spec

/-- info: 'smoke.Direct.Bridge.identity_byte_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms smoke.Direct.Bridge.identity_byte_bridge
