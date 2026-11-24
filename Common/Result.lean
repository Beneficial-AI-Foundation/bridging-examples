module
public import Aeneas
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

public section

namespace BridgingExamples

/-- The cases of a result: success, failure, divergence, and sampling. With the `random` effect of
`aeneas.patch`, a result can ask for `n` random bytes and continue with `k`. Failure has no
continuation. -/
@[elab_as_elim]
theorem resultCases {α : Type} {motive : Aeneas.Std.Result α → Prop}
    (r : Aeneas.Std.Result α)
    (ok : ∀ a, motive (.ok a))
    (fail : ∀ e, motive (.fail e))
    (div : motive .div)
    (random : ∀ n k, motive (.vis (.random n) k)) : motive r := by
  cases r with
  | ret a => exact ok a
  | div => exact div
  | vis e k =>
    cases e with
    | fail e =>
      have hk : k = PEmpty.elim := by funext x; exact PEmpty.elim x
      subst k
      exact fail e
    | random n => exact random n k

@[simp] theorem ok_ne_vis {α : Type} (a : α) (e : Aeneas.Std.RustEffect.Input) (k) :
    Aeneas.Std.Result.ok a ≠ Aeneas.Std.Result.vis e k := by
  intro h
  have := congrArg Aeneas.Std.Result.match h
  simp [Aeneas.Std.Result.match.ok, Aeneas.Std.Result.match.vis] at this

/-- `m` does not start by sampling. -/
def NoSample {α : Type} (m : Aeneas.Std.Result α) : Prop :=
  ∀ n k, m ≠ Aeneas.Std.Result.vis (.random n) k

@[simp] theorem noSample_ok {α : Type} (a : α) : NoSample (Aeneas.Std.Result.ok a) :=
  fun _ k => ok_ne_vis a _ k

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

/-- A specification of a result that does not start by sampling is a successful return satisfying
the postcondition. `NoSample` is needed because `spec` is demonic on the `random` effect: it holds
if every sampled path satisfies the postcondition. -/
theorem returns {α : Type} {m : Aeneas.Std.Result α} {p : α → Prop} (h : Aeneas.Std.WP.spec m p)
    (hm : NoSample m) : ∃ value, m = Aeneas.Std.Result.ok value ∧ p value := by
  induction m using resultCases with
  | ok value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp h⟩
  | fail e => simp at h
  | div => simp at h
  | random n k => exact absurd rfl (hm n k)

/-- A failure does not start by sampling. -/
@[simp] theorem noSample_fail {α : Type} (e : Aeneas.Std.Error) :
    NoSample (Aeneas.Std.Result.fail e : Aeneas.Std.Result α) := by
  intro n k h
  have := congrArg Aeneas.Std.Result.match h
  simp [Aeneas.Std.Result.match.fail, Aeneas.Std.Result.match.vis] at this

/-- `returns` for a loop. If every step of the loop satisfies its specification and does not start
by sampling, and the measure decreases, then the loop returns a value satisfying `post`. -/
theorem loop_returns {α β : Type} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Aeneas.Std.Result (Aeneas.Std.ControlFlow α β)) (x : α)
    (hBody : ∀ x, inv x → Aeneas.Std.WP.spec (body x) fun r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x)
    (hNoSample : ∀ x, inv x → NoSample (body x)) (hInv : inv x) :
    ∃ value, Aeneas.Std.loop body x = Aeneas.Std.Result.ok value ∧ post value := by
  induction h : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst h
    obtain ⟨r, hr, hq⟩ := returns (hBody x hInv) (hNoSample x hInv)
    rw [Aeneas.Std.loop, hr, Aeneas.Std.bind_ok]
    cases r with
    | done y => exact ⟨y, rfl, hq⟩
    | cont x' => exact ih _ hq.2 x' hq.1 rfl

/-- Use all result events when comparing output distributions. -/
instance {α : Type} : MeasurableSpace (Aeneas.Std.Result α) := ⊤

instance {α : Type} : DiscreteMeasurableSpace (Aeneas.Std.Result α) := ⟨fun _ => trivial⟩

end BridgingExamples
