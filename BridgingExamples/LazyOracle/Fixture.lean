import BridgingExamples.LazyOracle.ProbabilityBridge

/-!
# A concrete instance of the RNG contract

This handwritten file supplies the concrete randomness setup for the bridge.
The Rust `TwoByteRng` and its Aeneas translation deterministically consume two
supplied bytes. Neither implementation generates randomness.

`fixtureStates 2` introduces randomness in Lean: sample two independent uniform
bytes, then place them in the translated RNG state. `fixtureContract` proves that
this setup satisfies the handwritten `RngContract`. `fixture_lazy_eq_eager` then
applies the general bridge theorem to this setup.

The bytes are sampled before the client runs. Their assignment to keys remains
lazy: the first new key receives the first byte, and the other key receives the
second. The eager specification samples a table with values already assigned to
keys. This example does not model an operating-system RNG.
-/

open OracleComp OracleSpec

namespace bridge_lazy_oracle.Bridge

def modelToByte (value : Fin 256) : Aeneas.Std.U8 :=
  Aeneas.Std.UScalar.mk (ty := .U8) (BitVec.ofFin value)

theorem byteToModel_modelToByte (value : Fin 256) :
    byteToModel (modelToByte value) = value := by
  change (BitVec.ofFin (w := 8) value).toFin = value
  simp

/-- Handwritten uniform initialization of the translated deterministic fixture.

The bridge uses budgets zero through two. In particular, `fixtureStates 2` samples
two independent uniform bytes before any query. These sampling operations come
from the Lean experiment, not from Rust or the Aeneas translation.
-/
def fixtureStates : Nat → ProbComp TwoByteRng
  | 0 => pure { next := none, tail := none }
  | 1 => do
      let value ← $ᵗ (Fin 256)
      pure { next := some (modelToByte value), tail := none }
  | _ + 2 => do
      let first ← $ᵗ (Fin 256)
      let second ← $ᵗ (Fin 256)
      pure { next := some (modelToByte first), tail := some (modelToByte second) }

/-- Prove the required draw law for the translated fixture with `fixtureStates`.
This is a Lean proof, not an assumed axiom or a runtime randomness test. -/
def fixtureContract : RngContract TwoByteRng.Insts.Bridge_lazy_oracleByteRng where
  states := fixtureStates
  draw := by
    intro n hn
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;>
      simp [fixtureStates, TwoByteRng.Insts.Bridge_lazy_oracleByteRng.next_u8] <;> rfl

/-- Apply the general bridge after supplying uniform initialization and its contract proof. -/
theorem fixture_lazy_eq_eager {α : Type} (client : OracleComp ByteSpec α) :
    𝒟[lazyExperiment TwoByteRng.Insts.Bridge_lazy_oracleByteRng
      (fixtureStates 2) client] =
    𝒟[Aeneas.Std.Result.ok <$> eagerExperiment client] :=
  lazy_eq_eager fixtureContract client

end bridge_lazy_oracle.Bridge
