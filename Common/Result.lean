module
public import Aeneas
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

public section

namespace BridgingExamples

/-- Rust effects have no continuation after failure, so results still have
exactly the success, failure, and divergence cases. -/
@[elab_as_elim]
theorem resultCases {α : Type} {motive : Aeneas.Std.Result α → Prop}
    (r : Aeneas.Std.Result α)
    (ok : ∀ a, motive (.ok a))
    (fail : ∀ e, motive (.fail e))
    (div : motive .div) : motive r := by
  cases r with
  | ret a => exact ok a
  | div => exact div
  | vis e k =>
    cases e with
    | fail e =>
      have hk : k = PEmpty.elim := by funext x; exact PEmpty.elim x
      subst k
      exact fail e

@[simp] theorem resultMapOk {α β : Type} (f : α → β) (a : α) :
    f <$> Aeneas.Std.Result.ok a = Aeneas.Std.Result.ok (f a) := by
  change Aeneas.Std.bind (.ok a) (fun a => .ok (f a)) = _
  simp

@[simp] theorem resultMapFail {α β : Type} (f : α → β) (e : Aeneas.Std.Error) :
    f <$> (Aeneas.Std.Result.fail e : Aeneas.Std.Result α) = Aeneas.Std.Result.fail e := by
  change Aeneas.Std.bind (.fail e) (fun a => .ok (f a)) = _
  simp

@[simp] theorem resultMapDiv {α β : Type} (f : α → β) :
    f <$> (Aeneas.Std.Result.div : Aeneas.Std.Result α) = Aeneas.Std.Result.div := by
  change Aeneas.Std.bind .div (fun a => .ok (f a)) = _
  simp

@[simp] theorem uncurry_eq {α β γ : Type} (f : α → β → γ) :
    Aeneas.Std.uncurry f = fun p => f p.1 p.2 := by
  funext p
  cases p
  rfl

/-- A specification is a successful return satisfying the postcondition. -/
theorem returns {α : Type} {m : Aeneas.Std.Result α} {p : α → Prop} (h : Aeneas.Std.WP.spec m p) :
    ∃ value, m = Aeneas.Std.Result.ok value ∧ p value := by
  induction m using resultCases with
  | ok value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp h⟩
  | fail e => simp at h
  | div => simp at h

/-- Use all result events when comparing output distributions. -/
instance {α : Type} : MeasurableSpace (Aeneas.Std.Result α) := ⊤

instance {α : Type} : DiscreteMeasurableSpace (Aeneas.Std.Result α) := ⟨fun _ => trivial⟩

end BridgingExamples
