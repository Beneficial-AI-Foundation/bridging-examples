import BridgingExamples.Smoke

/-! Kernel dependency checks for the smoke bridge and the upstream results we plan to reuse. -/

/-- info: 'BridgingExamples.Smoke.identity_byte_returns' does not depend on any axioms -/
#guard_msgs in
#print axioms BridgingExamples.Smoke.identity_byte_returns

/-- info: 'BridgingExamples.Smoke.implementation_eq_specification' does not depend on any axioms -/
#guard_msgs in
#print axioms BridgingExamples.Smoke.implementation_eq_specification

/-- info: 'BridgingExamples.Smoke.implementation_eq_specification_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BridgingExamples.Smoke.implementation_eq_specification_dist

/--
info: 'OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable

/-- info: 'binding_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binding_bound

/-- info: 'hiding_bound_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hiding_bound_finite
