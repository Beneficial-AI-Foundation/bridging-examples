import BridgingExamples.LazyOracle.Bridge

/-!
# Bridge from lazy Rust execution to eager VCVio sampling

This file is handwritten bridge code. Aeneas translates Rust operations and state
changes into deterministic Lean functions. Its generated code supplies no
probability distribution over RNG states.

`lazyExperiment` introduces the probability layer around those functions. It
samples the supplied `initialRng` distribution, then runs the translated oracle.
For the concrete fixture, `fixtureStates 2` in `Fixture.lean` supplies two
independent uniform bytes. The translated `TwoByteRng` only consumes those bytes.

`RngContract` states the conditions required of an RNG and its state distributions.
It neither generates randomness nor adds a runtime check. `fixtureContract`
proves those conditions for the uniformly initialized translated fixture.
`lazy_eq_eager` then proves equivalence with the independently defined eager
specification in `Spec.lean`, conditional on the contract. `Fixture.lean` applies
that theorem to obtain the concrete result.

The cache model and the lazy VCVio random oracle are intermediate proof steps.
The remaining RNG-state distribution is tracked jointly with each answer so that
clients can choose later queries from earlier answers.
-/

open OracleComp OracleSpec

namespace bridge_lazy_oracle.Bridge

private theorem map_distribution_eq {α β : Type}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    {x y : ProbComp α} (h : 𝒟[x] = 𝒟[y]) (f : α → β) :
    𝒟[f <$> x] = 𝒟[f <$> y] := by
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, h]

/-- Number of keys whose answers have not yet been assigned. -/
def remaining (cache : OracleSpec.QueryCache ByteSpec) : Nat :=
  (if (cache false).isSome then 0 else 1) +
  (if (cache true).isSome then 0 else 1)

/-- Handwritten bridge contract for the translated RNG and its state distributions.

`states` supplies a probability distribution for each remaining draw budget.
`draw` is a proof obligation about those distributions and the translated
`next_u8` operation. It does not introduce a random operation into generated code.

`draw` states a joint law: the next byte is uniform and independent of the
remaining RNG state. This is stronger than independent uniform output bytes:
the post-draw state must carry no information about the returned byte.
RNGs that retain a log of returned bytes are excluded, even when the conclusion
of `lazy_eq_eager` holds for them.
Only two draws are needed. No condition is imposed on exhausted RNG calls.
-/
structure RngContract {R : Type} (rngInst : ByteRng R) where
  states : Nat → ProbComp R
  draw : ∀ n, n < 2 →
    𝒟[(fun rng => Prod.map byteToModel id <$> rngInst.next_u8 rng) <$> states (n + 1)] =
    𝒟[do
      let value ← $ᵗ (Fin 256)
      let rng ← states n
      pure (Aeneas.Std.Result.ok (value, rng))]

def residualRng {R : Type} {rngInst : ByteRng R}
    (contract : RngContract rngInst) (cache : OracleSpec.QueryCache ByteSpec) :
    ProbComp R := contract.states (remaining cache)

theorem evalDist_lazyCacheModel_query_residualRng
    {R : Type} {rngInst : ByteRng R} (contract : RngContract rngInst)
    (key : Bool)
    (cache : OracleSpec.QueryCache ByteSpec) :
    𝒟[do
      let rng ← residualRng contract cache
      pure ((lazyCacheModel rngInst key).run (cache, rng))] =
    𝒟[do
      let answerAndCache ←
        (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
      let rng ← residualRng contract answerAndCache.2
      pure (Aeneas.Std.Result.ok
        (answerAndCache.1, (answerAndCache.2, rng)))] := by
  have hmiss (key : Bool) (n : Nat) (hn : n < 2) :=
    map_distribution_eq (contract.draw n hn)
      (fun result => (fun p : Fin 256 × R =>
        (p.1, cache.cacheQuery key p.1, p.2)) <$> result)
  simp only [Function.comp_def, Prod.map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind] at hmiss
  cases hfalse : cache false <;> cases htrue : cache true <;> cases key <;>
    simp [residualRng, remaining, lazyCacheModel, QueryImpl.withCachingAux_apply,
      uniformSampleImpl, hfalse, htrue] <;>
    try rfl
  · convert (hmiss false 1 (by omega)) using 1 <;> simp
  · convert (hmiss true 1 (by omega)) using 1 <;> simp
  · convert (hmiss false 0 (by omega)) using 1 <;> simp
  · convert (hmiss true 0 (by omega)) using 1 <;> simp

theorem evalDist_lazyCacheModel_client_residualRng
    {R α : Type} {rngInst : ByteRng R}
    (contract : RngContract rngInst)
    (client : OracleComp ByteSpec α)
    (cache : OracleSpec.QueryCache ByteSpec) :
    𝒟[do
      let rng ← residualRng contract cache
      pure
        ((_root_.simulateQ
          (lazyCacheModel rngInst)
          client).run (cache, rng))] =
    𝒟[do
      let answerAndCache ←
        (_root_.simulateQ
          (OracleSpec.randomOracle (spec := ByteSpec))
          client).run cache
      let rng ← residualRng contract answerAndCache.2
      pure
        (Aeneas.Std.Result.ok
          (answerAndCache.1, (answerAndCache.2, rng)))] := by
  induction client using OracleComp.inductionOn generalizing cache with
  | pure value =>
    change
      𝒟[do
        let rng ← residualRng contract cache
        pure (Aeneas.Std.Result.ok (value, (cache, rng)))] =
      𝒟[do
        let rng ← residualRng contract cache
        pure (Aeneas.Std.Result.ok (value, (cache, rng)))]
    rfl
  | query_bind key continuation ih =>
    let continueResult :
        Aeneas.Std.Result
            (ByteSpec.Range key ×
              (OracleSpec.QueryCache ByteSpec × R)) →
          Aeneas.Std.Result
            (α × (OracleSpec.QueryCache ByteSpec × R)) :=
      fun result => do
        let head ← result
        (_root_.simulateQ
          (lazyCacheModel rngInst)
          (continuation head.1)).run head.2
    calc
      _ = 𝒟[continueResult <$> (do
          let rng ← residualRng contract cache
          pure
            ((lazyCacheModel rngInst key).run
              (cache, rng)))] := by
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
              continueResult, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
            rfl
      _ = 𝒟[continueResult <$> (do
          let answerAndCache ←
            (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
          let rng ← residualRng contract answerAndCache.2
          pure
            (Aeneas.Std.Result.ok
              (answerAndCache.1, (answerAndCache.2, rng))))] :=
        map_distribution_eq
          (evalDist_lazyCacheModel_query_residualRng contract key cache) continueResult
      _ = 𝒟[do
          let answerAndCache ←
            (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
          let rng ← residualRng contract answerAndCache.2
          pure
            ((_root_.simulateQ
              (lazyCacheModel rngInst)
              (continuation answerAndCache.1)).run
                (answerAndCache.2, rng))] := by
        simp [continueResult, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply]
      _ = 𝒟[do
          let answerAndCache ←
            (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
          let finalAnswerAndCache ←
            (_root_.simulateQ
              (OracleSpec.randomOracle (spec := ByteSpec))
              (continuation answerAndCache.1)).run answerAndCache.2
          let rng ← residualRng contract finalAnswerAndCache.2
          pure
            (Aeneas.Std.Result.ok
              (finalAnswerAndCache.1, (finalAnswerAndCache.2, rng)))] := by
        refine evalDist_bind_congr _ _ _ ?_
        intro answerAndCache
        exact ih answerAndCache.1 answerAndCache.2
      _ = _ := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]

/-- Handwritten probability layer around the deterministic Aeneas translation.

Sample `initialRng`, then run the translated oracle from that state. The concrete
fixture uses `fixtureStates 2`, defined in `Fixture.lean`, to supply uniform bytes.
This definition accepts any initial distribution; the bridge theorem requires
the conditions in `RngContract`.
-/
def lazyExperiment
    {R α : Type} (rngInst : ByteRng R)
    (initialRng : ProbComp R)
    (client : OracleComp ByteSpec α) :
    ProbComp (Aeneas.Std.Result α) := do
  let rng ← initialRng
  pure (do
    let self ← LazyOracle.new
    Prod.fst <$>
      (_root_.simulateQ (implementation rngInst) client).run (self, rng))

theorem evalDist_lazyExperiment_eq_randomOracle
    {R α : Type} {rngInst : ByteRng R}
    (contract : RngContract rngInst)
    (client : OracleComp ByteSpec α) :
    𝒟[lazyExperiment rngInst (contract.states 2) client] =
    𝒟[Aeneas.Std.Result.ok <$>
      (_root_.simulateQ
        (OracleSpec.randomOracle (spec := ByteSpec))
        client).run' (∅ : OracleSpec.QueryCache ByteSpec)] := by
  have hrefine (rng : R) :
      (do
        let self ← LazyOracle.new
        Prod.fst <$>
          (_root_.simulateQ
            (implementation rngInst)
            client).run (self, rng)) =
      Prod.fst <$>
        (_root_.simulateQ
          (lazyCacheModel rngInst)
          client).run
            ((∅ : OracleSpec.QueryCache ByteSpec), rng) := by
    have h := congrArg (Prod.fst <$> ·)
      (initialized_client_refines
        rngInst client rng)
    simpa [LazyOracle.new, Functor.map_map, Function.comp_def, Prod.map] using h
  have himplementation :
      lazyExperiment rngInst (contract.states 2) client = (do
        let rng ← residualRng contract (∅ : OracleSpec.QueryCache ByteSpec)
        pure
          (Prod.fst <$>
            (_root_.simulateQ
              (lazyCacheModel rngInst)
              client).run ((∅ : OracleSpec.QueryCache ByteSpec), rng))) := by
    simp [lazyExperiment, residualRng, remaining, hrefine]
  rw [himplementation]
  have hclient := map_distribution_eq
    (evalDist_lazyCacheModel_client_residualRng contract client
      (∅ : OracleSpec.QueryCache ByteSpec))
    (fun result => Prod.fst <$> result)
  have hresidual (cache : OracleSpec.QueryCache ByteSpec)
      (value : Aeneas.Std.Result α) :
      𝒟[do
        let _ ← residualRng contract cache
        pure value] = 𝒟[(pure value : ProbComp (Aeneas.Std.Result α))] := by
    exact OracleComp.evalDist_bind_const _ _

  calc
    _ = 𝒟[(fun result => Prod.fst <$> result) <$> (do
        let rng ← residualRng contract (∅ : OracleSpec.QueryCache ByteSpec)
        pure
          ((_root_.simulateQ
            (lazyCacheModel rngInst)
            client).run ((∅ : OracleSpec.QueryCache ByteSpec), rng)))] := by
      simp [Functor.map_map]
    _ = 𝒟[(fun result => Prod.fst <$> result) <$> (do
        let answerAndCache ←
          (_root_.simulateQ
            (OracleSpec.randomOracle (spec := ByteSpec))
            client).run (∅ : OracleSpec.QueryCache ByteSpec)
        let rng ← residualRng contract answerAndCache.2
        pure
          (Aeneas.Std.Result.ok
            (answerAndCache.1, (answerAndCache.2, rng))))] := hclient
    _ = 𝒟[Aeneas.Std.Result.ok <$>
        (_root_.simulateQ
          (OracleSpec.randomOracle (spec := ByteSpec))
          client).run' (∅ : OracleSpec.QueryCache ByteSpec)] := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
        StateT.run'_eq]
      refine evalDist_bind_congr _ _ _ ?_
      intro answerAndCache
      simpa only [Function.comp_apply, Aeneas.Std.bind_tc_ok, Aeneas.Std.pure_tc_eq] using hresidual answerAndCache.2
        (Aeneas.Std.Result.ok answerAndCache.1 : Aeneas.Std.Result α)

/-- Main bridge, conditional on the handwritten Lean RNG contract.

Randomness enters the implementation experiment through `contract.states 2`.
The contract's proof of the joint draw law justifies the comparison with the eager
specification. Aeneas supplies the translated operations, not this probability law.
Clients can choose queries adaptively.
Internal cache contents and RNG consumption are not observations in this theorem. -/
theorem lazy_eq_eager
    {R α : Type} {rngInst : ByteRng R}
    (contract : RngContract rngInst)
    (client : OracleComp ByteSpec α) :
    𝒟[lazyExperiment rngInst (contract.states 2) client] =
    𝒟[Aeneas.Std.Result.ok <$> eagerExperiment client] := by
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_lazyExperiment_eq_randomOracle contract]
  exact map_distribution_eq
    (OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable client)
    Aeneas.Std.Result.ok

end bridge_lazy_oracle.Bridge
