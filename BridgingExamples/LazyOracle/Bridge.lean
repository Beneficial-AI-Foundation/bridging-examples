import Generated.LazyOracle.Funs
import BridgingExamples.LazyOracle.Spec
import Aeneas.Std.WP
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

namespace bridge_lazy_oracle.Bridge

def byteToModel (value : Aeneas.Std.U8) : Fin 256 :=
  value.bv.toFin

def cacheToModel (self : LazyOracle) :
    OracleSpec.QueryCache ByteSpec :=
  fun key =>
    (if key then self.true_value else self.false_value).map byteToModel

def stateToModel {R : Type} (state : LazyOracle × R) :
    OracleSpec.QueryCache ByteSpec × R :=
  (cacheToModel state.1, state.2)

def implementation {R : Type} (rngInst : ByteRng R) :
    QueryImpl ByteSpec (StateT (LazyOracle × R) Aeneas.Std.Result) :=
  fun key => StateT.mk fun state =>
    Prod.map byteToModel id <$>
      LazyOracle.query rngInst state.1 key state.2

/-- Internal proof model of the Rust cache. The public specification is `eagerExperiment`. -/
def lazyCacheModel {R : Type} (rngInst : ByteRng R) :
    QueryImpl ByteSpec
      (StateT (OracleSpec.QueryCache ByteSpec × R) Aeneas.Std.Result) :=
  QueryImpl.withCachingAux (spec := ByteSpec)
    (fun _ _ _ rngState => rngState)
    (fun _ _ rngState =>
      Prod.map byteToModel id <$> rngInst.next_u8 rngState)

theorem byteToModel_bijective :
    Function.Bijective byteToModel := by
  constructor
  · intro x y hxy
    cases x with
    | mk xb =>
      cases y with
      | mk yb =>
        congr
        exact (BitVec.toFin_bijective 8).1 hxy
  · intro y
    obtain ⟨value, hvalue⟩ := (BitVec.toFin_bijective 8).2 y
    exact ⟨⟨value⟩, hvalue⟩

theorem new_refines :
    cacheToModel <$> LazyOracle.new =
      Aeneas.Std.Result.ok (∅ : OracleSpec.QueryCache ByteSpec) := by
  apply congrArg Aeneas.Std.Result.ok
  funext key
  cases key <;> rfl

theorem query_refines {R : Type} (rngInst : ByteRng R)
    (key : Bool) (state : LazyOracle × R) :
    Prod.map id stateToModel <$>
        (implementation rngInst key).run state =
      (lazyCacheModel rngInst key).run (stateToModel state) := by
  rcases state with ⟨⟨falseValue, trueValue⟩, rngState⟩
  cases key <;> simp only [implementation, lazyCacheModel, stateToModel, cacheToModel,
    LazyOracle.query, QueryImpl.withCachingAux_apply]
  · cases falseValue with
    | some value => rfl
    | none =>
      cases hdraw : rngInst.next_u8 rngState with
      | fail error => simp [hdraw]; rfl
      | div => simp [hdraw]; rfl
      | ok draw =>
        rcases draw with ⟨value, rngState'⟩
        simp [hdraw]
        change Aeneas.Std.Result.ok _ = Aeneas.Std.Result.ok _
        apply congrArg Aeneas.Std.Result.ok
        change
          (byteToModel value,
              cacheToModel { false_value := some value, true_value := trueValue },
              rngState') =
            (byteToModel value,
              (cacheToModel { false_value := none, true_value := trueValue }).cacheQuery
                false (byteToModel value),
              rngState')
        congr 2
        funext queryKey
        cases queryKey <;> rfl
  · cases trueValue with
    | some value => rfl
    | none =>
      cases hdraw : rngInst.next_u8 rngState with
      | fail error => simp [hdraw]; rfl
      | div => simp [hdraw]; rfl
      | ok draw =>
        rcases draw with ⟨value, rngState'⟩
        simp [hdraw]
        change Aeneas.Std.Result.ok _ = Aeneas.Std.Result.ok _
        apply congrArg Aeneas.Std.Result.ok
        change
          (byteToModel value,
              cacheToModel { false_value := falseValue, true_value := some value },
              rngState') =
            (byteToModel value,
              (cacheToModel { false_value := falseValue, true_value := none }).cacheQuery
                true (byteToModel value),
              rngState')
        congr 2
        funext queryKey
        cases queryKey <;> rfl

theorem client_refines {R α : Type} (rngInst : ByteRng R)
    (client : OracleComp ByteSpec α) (state : LazyOracle × R) :
    Prod.map id stateToModel <$>
        (_root_.simulateQ (implementation rngInst) client).run state =
      (_root_.simulateQ (lazyCacheModel rngInst) client).run
        (stateToModel state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (implementation rngInst) (lazyCacheModel rngInst) stateToModel
    (query_refines rngInst) client state

theorem initialized_client_refines {R α : Type} (rngInst : ByteRng R)
    (client : OracleComp ByteSpec α) (rngState : R) :
    (do
      let self ← LazyOracle.new
      Prod.map id stateToModel <$>
        (_root_.simulateQ (implementation rngInst) client).run
          (self, rngState)) =
      (_root_.simulateQ (lazyCacheModel rngInst) client).run
        (∅, rngState) := by
  have hstate :
      stateToModel ({ false_value := none, true_value := none }, rngState) =
        (∅, rngState) := by
    change (cacheToModel { false_value := none, true_value := none }, rngState) =
      (∅, rngState)
    congr
    funext key
    cases key <;> rfl
  simpa [LazyOracle.new, hstate] using
    client_refines rngInst client
      ({ false_value := none, true_value := none }, rngState)

end bridge_lazy_oracle.Bridge
