import Generated.LazyOracle.Funs
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Lazy-oracle extraction checkpoint

This module checks that the genuine Rust extraction and the pinned VCVio
oracle APIs coexist. It does not establish probabilistic refinement.
-/

#check Aeneas.Std.Result
#check QueryImpl.withCachingAux
#check OracleComp.map_run_simulateQ_eq_of_query_map_eq
#check OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
