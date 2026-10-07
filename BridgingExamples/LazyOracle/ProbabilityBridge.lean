import BridgingExamples.LazyOracle.Bridge
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

open OracleComp OracleSpec

namespace bridge_lazy_oracle.Bridge

def modelToByte (value : Fin 256) : Aeneas.Std.U8 :=
  Aeneas.Std.UScalar.mk (ty := .U8) (BitVec.ofFin value)

theorem byteToModel_modelToByte (value : Fin 256) :
    byteToModel (modelToByte value) = value := by
  change (BitVec.ofFin (w := 8) value).toFin = value
  simpa using (@BitVec.toFin_ofFin 8 value)

def residualRng (cache : OracleSpec.QueryCache ByteSpec) :
    ProbComp TwoByteRng :=
  match cache false, cache true with
  | none, none => do
      let first ← $ᵗ (Fin 256)
      let second ← $ᵗ (Fin 256)
      pure
        { next := some (modelToByte first)
          tail := some (modelToByte second) }
  | some _, some _ =>
      pure
        { next := none
          tail := none }
  | _, _ => do
      let last ← $ᵗ (Fin 256)
      pure
        { next := some (modelToByte last)
          tail := none }

theorem evalDist_model_query_residualRng
    (key : Bool)
    (cache : OracleSpec.QueryCache ByteSpec) :
    𝒟[do
      let rng ← residualRng cache
      pure
        ((model TwoByteRng.Insts.Bridge_lazy_oracleByteRng key).run
          (cache, rng))] =
    𝒟[do
      let answerAndCache ←
        (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
      let rng ← residualRng answerAndCache.2
      pure
        (Aeneas.Std.Result.ok
          (answerAndCache.1, (answerAndCache.2, rng)))] := by
  cases hfalse : cache false <;> cases htrue : cache true <;> cases key <;>
    simp [residualRng, model, QueryImpl.withCachingAux_apply,
      uniformSampleImpl, hfalse, htrue,
      TwoByteRng.Insts.Bridge_lazy_oracleByteRng.next_u8,
      byteToModel_modelToByte] <;> rfl

theorem evalDist_model_client_residualRng
    {α : Type}
    (client : OracleComp ByteSpec α)
    (cache : OracleSpec.QueryCache ByteSpec) :
    𝒟[do
      let rng ← residualRng cache
      pure
        ((_root_.simulateQ
          (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
          client).run (cache, rng))] =
    𝒟[do
      let answerAndCache ←
        (_root_.simulateQ
          (OracleSpec.randomOracle (spec := ByteSpec))
          client).run cache
      let rng ← residualRng answerAndCache.2
      pure
        (Aeneas.Std.Result.ok
          (answerAndCache.1, (answerAndCache.2, rng)))] := by
  induction client using OracleComp.inductionOn generalizing cache with
  | pure value =>
    change
      𝒟[do
        let rng ← residualRng cache
        pure (Aeneas.Std.Result.ok (value, (cache, rng)))] =
      𝒟[do
        let rng ← residualRng cache
        pure (Aeneas.Std.Result.ok (value, (cache, rng)))]
    rfl
  | query_bind key continuation ih =>
    let continueResult :
        Aeneas.Std.Result
            (ByteSpec.Range key ×
              (OracleSpec.QueryCache ByteSpec × TwoByteRng)) →
          Aeneas.Std.Result
            (α × (OracleSpec.QueryCache ByteSpec × TwoByteRng)) :=
      fun result => do
        let head ← result
        (_root_.simulateQ
          (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
          (continuation head.1)).run head.2
    calc
      _ = 𝒟[continueResult <$> (do
          let rng ← residualRng cache
          pure
            ((model TwoByteRng.Insts.Bridge_lazy_oracleByteRng key).run
              (cache, rng)))] := by
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
              continueResult, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
      _ = 𝒟[continueResult <$> (do
          let answerAndCache ←
            (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
          let rng ← residualRng answerAndCache.2
          pure
            (Aeneas.Std.Result.ok
              (answerAndCache.1, (answerAndCache.2, rng))))] :=
        evalDist_map_eq_of_evalDist_eq
          (evalDist_model_query_residualRng key cache) continueResult
      _ = 𝒟[do
          let answerAndCache ←
            (OracleSpec.randomOracle (spec := ByteSpec) key).run cache
          let rng ← residualRng answerAndCache.2
          pure
            ((_root_.simulateQ
              (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
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
          let rng ← residualRng finalAnswerAndCache.2
          pure
            (Aeneas.Std.Result.ok
              (finalAnswerAndCache.1, (finalAnswerAndCache.2, rng)))] := by
        refine evalDist_bind_congr' _ ?_
        intro answerAndCache
        exact ih answerAndCache.1 answerAndCache.2
      _ = _ := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]

def implementationExperiment
    {α : Type}
    (client : OracleComp ByteSpec α) :
    ProbComp (Aeneas.Std.Result α) := do
  let first ← $ᵗ (Fin 256)
  let second ← $ᵗ (Fin 256)
  pure (do
    let rng ←
      TwoByteRng.new (modelToByte first) (modelToByte second)
    let self ← LazyOracle.new
    Prod.fst <$>
      (_root_.simulateQ
        (implementation TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
        client).run (self, rng))

theorem evalDist_implementationExperiment_eq_randomOracle
    {α : Type}
    (client : OracleComp ByteSpec α) :
    𝒟[implementationExperiment client] =
    𝒟[Aeneas.Std.Result.ok <$>
      (_root_.simulateQ
        (OracleSpec.randomOracle (spec := ByteSpec))
        client).run' (∅ : OracleSpec.QueryCache ByteSpec)] := by
  have hrefine (rng : TwoByteRng) :
      (do
        let self ← LazyOracle.new
        Prod.fst <$>
          (_root_.simulateQ
            (implementation TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
            client).run (self, rng)) =
      Prod.fst <$>
        (_root_.simulateQ
          (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
          client).run
            ((∅ : OracleSpec.QueryCache ByteSpec), rng) := by
    have h := congrArg (Prod.fst <$> ·)
      (initialized_client_refines
        TwoByteRng.Insts.Bridge_lazy_oracleByteRng client rng)
    simpa [Functor.map_map, Function.comp_def, Prod.map] using h
  have himplementation :
      implementationExperiment client = (do
        let rng ← residualRng (∅ : OracleSpec.QueryCache ByteSpec)
        pure
          (Prod.fst <$>
            (_root_.simulateQ
              (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
              client).run ((∅ : OracleSpec.QueryCache ByteSpec), rng))) := by
    simp [implementationExperiment, residualRng, TwoByteRng.new, hrefine]
  rw [himplementation]
  have hclient := evalDist_map_eq_of_evalDist_eq
    (evalDist_model_client_residualRng client
      (∅ : OracleSpec.QueryCache ByteSpec))
    (fun result => Prod.fst <$> result)
  have hresidual (cache : OracleSpec.QueryCache ByteSpec)
      (value : Aeneas.Std.Result α) :
      𝒟[do
        let _ ← residualRng cache
        pure value] = 𝒟[(pure value : ProbComp (Aeneas.Std.Result α))] := by
    have hfailure : Pr[⊥ | residualRng cache] = 0 := by
      cases hfalse : cache false <;> cases htrue : cache true <;>
        simp [residualRng, hfalse, htrue]
    apply evalDist_ext
    intro output
    rw [probOutput_bind_const, hfailure, tsub_zero, one_mul]
  calc
    _ = 𝒟[(fun result => Prod.fst <$> result) <$> (do
        let rng ← residualRng (∅ : OracleSpec.QueryCache ByteSpec)
        pure
          ((_root_.simulateQ
            (model TwoByteRng.Insts.Bridge_lazy_oracleByteRng)
            client).run ((∅ : OracleSpec.QueryCache ByteSpec), rng)))] := by
      simp [Functor.map_map]
    _ = 𝒟[(fun result => Prod.fst <$> result) <$> (do
        let answerAndCache ←
          (_root_.simulateQ
            (OracleSpec.randomOracle (spec := ByteSpec))
            client).run (∅ : OracleSpec.QueryCache ByteSpec)
        let rng ← residualRng answerAndCache.2
        pure
          (Aeneas.Std.Result.ok
            (answerAndCache.1, (answerAndCache.2, rng))))] := hclient
    _ = 𝒟[Aeneas.Std.Result.ok <$>
        (_root_.simulateQ
          (OracleSpec.randomOracle (spec := ByteSpec))
          client).run' (∅ : OracleSpec.QueryCache ByteSpec)] := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
        StateT.run'_eq]
      refine evalDist_bind_congr' _ ?_
      intro answerAndCache
      exact hresidual answerAndCache.2
        (pure answerAndCache.1 : Aeneas.Std.Result α)

theorem evalDist_implementationExperiment_eq_uniformTable
    {α : Type}
    (client : OracleComp ByteSpec α) :
    𝒟[implementationExperiment client] =
    𝒟[do
      let table ← $ᵗ (Bool → Fin 256)
      pure
        (Aeneas.Std.Result.ok
          (_root_.evalWithAnswerFn
            (QueryImpl.ofFn table)
            client))] := by
  rw [evalDist_implementationExperiment_eq_randomOracle]
  exact evalDist_map_eq_of_evalDist_eq
    (OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable client)
    Aeneas.Std.Result.ok

end bridge_lazy_oracle.Bridge
