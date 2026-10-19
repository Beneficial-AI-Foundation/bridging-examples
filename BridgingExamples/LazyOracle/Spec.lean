import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Eager specification for the lazy Rust oracle

The specification samples a complete table before the client runs. It has no
cache and no RNG state. The bridge compares client output distributions.
-/

namespace bridge_lazy_oracle.Bridge

abbrev ByteSpec : OracleSpec Bool := Bool →ₒ Fin 256

/-- Sample both answers upfront, then answer every query by table lookup. -/
def eagerExperiment {α : Type} (client : OracleComp ByteSpec α) : ProbComp α := do
  let table ← $ᵗ (Bool → Fin 256)
  pure (_root_.evalWithAnswerFn (QueryImpl.ofFn table) client)

end bridge_lazy_oracle.Bridge
