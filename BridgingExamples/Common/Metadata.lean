module
public meta import Lean

public meta section

open Lean Elab Command

namespace BridgingExamples.Metadata

structure Link where
  stage : Name
  declaration : Name
  targets : Array Name
  deriving Inhabited

initialize links : SimpleScopedEnvExtension Link (Array Link) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := Array.push }

syntax (name := specFor) "spec_for" ident+ : attr
syntax (name := cryptoFor) "crypto_for" ident+ : attr
syntax (name := bridgeFor) "bridge_for" ident+ : attr
syntax (name := assumptionFor) "assumption_for" ident+ : attr

private def registerLink (name : Name) (stage : Name) : IO Unit :=
  registerBuiltinAttribute {
    name
    descr := "Associate a local declaration with existing atoms."
    add := fun declaration stx kind => do
      let targets ← stx[1].getArgs.mapM fun target =>
        Elab.realizeGlobalConstNoOverloadWithInfo target
      links.add { stage, declaration, targets } kind
  }

initialize registerLink `specFor `spec
initialize registerLink `cryptoFor `crypto
initialize registerLink `bridgeFor `bridge
initialize registerLink `assumptionFor `assumption

elab "#export_explorer " output:str : command => do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some mod ← findModuleOf? name | continue
    unless mod.toString.startsWith "Generated." || mod.toString.startsWith "BridgingExamples." do
      continue
    let some ranges ← findDeclarationRangesCore? name | continue
    if name.isInternal then continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "type"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | _ => "definition"
    let linked := (links.getState env).filter (·.declaration == name)
    let axioms ← collectAxioms name
    let type ← liftTermElabM <| Meta.ppExpr info.type
    let returnsProp ← liftTermElabM <| Meta.forallTelescopeReducing info.type fun _ body =>
      pure body.isProp
    let isProof ← liftTermElabM <| Meta.isProp info.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("start", toJson ranges.range.pos.line),
      ("end", toJson ranges.range.endPos.line),
      ("selection", toJson ranges.selectionRange.pos.line),
      ("kind", toJson kind), ("type", toJson type.pretty),
      ("projectionOf", toJson ((env.getProjectionStructureName? name).map Name.toString)),
      ("returnsProp", toJson returnsProp),
      ("isProof", toJson isProof), ("isFunction", toJson info.type.isForall),
      ("typeReferences", toJson (info.type.getUsedConstants.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("links", Json.arr <| linked.map fun link => Json.mkObj [
        ("stage", toJson link.stage.toString),
        ("targets", toJson (link.targets.map Name.toString))])]
  liftIO <| IO.FS.writeFile output.getString (Json.arr rows).pretty

end BridgingExamples.Metadata
