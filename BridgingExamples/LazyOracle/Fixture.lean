import BridgingExamples.LazyOracle.ProbabilityBridge

/-!
# A concrete instance of the RNG contract

The Rust fixture consumes a finite stream of entropy. The Lean experiment
initializes that stream uniformly. This file proves that it satisfies the
contract used by the general bridge. It does not model an operating-system RNG.
-/

open OracleComp OracleSpec

namespace bridge_lazy_oracle.Bridge

def modelToByte (value : Fin 256) : Aeneas.Std.U8 :=
  Aeneas.Std.UScalar.mk (ty := .U8) (BitVec.ofFin value)

theorem byteToModel_modelToByte (value : Fin 256) :
    byteToModel (modelToByte value) = value := by
  change (BitVec.ofFin (w := 8) value).toFin = value
  simp

/-- The fixture has zero, one, or two independent uniform bytes left. -/
def fixtureStates : Nat → ProbComp TwoByteRng
  | 0 => pure { next := none, tail := none }
  | 1 => do
      let value ← $ᵗ (Fin 256)
      pure { next := some (modelToByte value), tail := none }
  | _ + 2 => do
      let first ← $ᵗ (Fin 256)
      let second ← $ᵗ (Fin 256)
      pure { next := some (modelToByte first), tail := some (modelToByte second) }

def fixtureContract : RngContract TwoByteRng.Insts.Bridge_lazy_oracleByteRng where
  states := fixtureStates
  lossless := by
    intro n hn
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
      simp [fixtureStates]
  draw := by
    intro n hn
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;>
      simp [fixtureStates, TwoByteRng.Insts.Bridge_lazy_oracleByteRng.next_u8] <;> rfl

/-- The concrete fixture is an instance of the general lazy-to-eager bridge. -/
theorem fixture_lazy_eq_eager {α : Type} (client : OracleComp ByteSpec α) :
    𝒟[lazyExperiment TwoByteRng.Insts.Bridge_lazy_oracleByteRng
      (fixtureStates 2) client] =
    𝒟[Aeneas.Std.Result.ok <$> eagerExperiment client] :=
  lazy_eq_eager fixtureContract client

end bridge_lazy_oracle.Bridge
