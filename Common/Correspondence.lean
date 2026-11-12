import Common.Result
import Common.Byte
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure

open Aeneas.Std

namespace BridgingExamples

/-- A deterministic bridge from a functional specification. -/
theorem bridge_of_spec {α : Type} {m : Result α} {value : α} (h : WP.spec m (· = value)) :
    (pure m : ProbComp (Result α)) =ᵈ
    (do let result ← (pure value : ProbComp α)
        pure (Result.ok result)) := by
  obtain ⟨_, hm, rfl⟩ := returns h
  simp [hm]

/-- Continue after a call whose distribution on `entropy` is known. -/
theorem bind_call {R α β : Type} {entropy : ProbComp R} {call : R → Result α}
    {outcome : ProbComp (Result α)}
    (h : (do let state ← entropy; pure (call state)) =ᵈ outcome) (k : α → Result β) :
    (do let state ← entropy
        pure (call state >>= k)) =ᵈ
    (do let result ← outcome
        pure (result >>= k)) := by
  have := h.map (fun result => result >>= k)
  simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using this

/-- Uniform byte vectors of equal lengths have the same distribution. A buffer's length is
often known only as an equation, such as the length of the slice of a one-byte array. -/
theorem uniformVector_bind_congr {γ : Type} {m k : ℕ} (h : m = k)
    (f : List.Vector U8 m → ProbComp γ) (g : List.Vector U8 k → ProbComp γ)
    (hfg : ∀ v : List.Vector U8 m, f v = g ⟨v.val, h ▸ v.property⟩) :
    (uniformSample (List.Vector U8 m) >>= f) =ᵈ (uniformSample (List.Vector U8 k) >>= g) := by
  subst h
  have : f = g := funext fun v => hfg v
  rw [this]

end BridgingExamples
