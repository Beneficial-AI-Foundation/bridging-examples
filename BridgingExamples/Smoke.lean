import Generated.Funs
import BridgingExamples.Result
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Examples.CommitmentScheme

/-!
# Toolchain and representation smoke test

The Rust identity function is deliberately trivial. This module checks that the actual
extraction, Aeneas's result type, and the VCVio modules needed by the next examples coexist.
Failure and divergence remain explicit; neither is silently replaced by a successful value.
-/

namespace BridgingExamples.Smoke

/-- Observe a Rust byte as a natural number, preserving every result constructor. -/
def observeByte (result : Aeneas.Std.Result Aeneas.Std.U8) : Aeneas.Std.Result Nat :=
  (fun x => x.val) <$> result

/-- The extracted implementation, embedded as a deterministic VCVio computation. -/
def implementation (x : Aeneas.Std.U8) : ProbComp (Aeneas.Std.Result Nat) :=
  pure (observeByte (bridge_smoke.identity_byte x))

/-- Independent mathematical specification of byte identity. -/
def specification (n : Nat) : ProbComp (Aeneas.Std.Result Nat) :=
  pure (.ok n)

/-- The extracted function succeeds and preserves its input. -/
theorem identity_byte_returns (x : Aeneas.Std.U8) :
    bridge_smoke.identity_byte x = .ok x := by
  rfl

/-- Pointwise refinement across the representation boundary. -/
theorem implementation_eq_specification (x : Aeneas.Std.U8) :
    implementation x = specification x.val := by
  simp [implementation, specification, observeByte, bridge_smoke.identity_byte]

/-- The implementation and specification have equal output distributions. -/
theorem implementation_eq_specification_dist (x : Aeneas.Std.U8) :
    evalDist (implementation x) = evalDist (specification x.val) := by
  rw [implementation_eq_specification]

end BridgingExamples.Smoke
