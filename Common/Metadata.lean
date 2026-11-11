module
public meta import Lean

/-!
# Explorer metadata

The explorer links each extracted atom to its handwritten spec, Crypto counterpart, bridge
theorem and assumptions. It finds them by name (`crate.Spec.f_spec`, `crate.Crypto.f`,
`crate.Bridge.f_bridge`, …), and by the attributes of this file where names do not match.

* `@[spec_for a…]`, `@[crypto_for a…]`, `@[bridge_for a…]` and `@[assumption_for a…]` link a
  declaration to the extracted atoms `a…`.
* `#export_explorer "path"` writes the compiled declarations of the `BridgingExamples` and
  `Common` modules, with their links, as JSON.

`explorer/export.mjs` runs `#export_explorer` in a file that imports every module, followed by
`#export_proof_ranges` (`Common/SourceRanges.lean`).
-/

public meta section

open Lean Elab Command

namespace BridgingExamples.Metadata

/-- A link recorded by one attribute: `declaration` is linked to the extracted atoms `targets`
in `stage`, one of `spec`, `crypto`, `bridge` and `assumption`. -/
structure Link where
  stage : Name
  declaration : Name
  targets : Array Name
  deriving Inhabited

/-- The recorded links. They are stored with each module, so the export sees the links of every
imported module. -/
initialize links : SimpleScopedEnvExtension Link (Array Link) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := Array.push }

/-- `@[spec_for a…]`: this declaration is a functional specification of the atoms `a…`. -/
syntax (name := specFor) "spec_for" ident+ : attr
/-- `@[crypto_for a…]`: this declaration is the Crypto counterpart of the atoms `a…`. -/
syntax (name := cryptoFor) "crypto_for" ident+ : attr
/-- `@[bridge_for a…]`: this declaration is a bridge theorem for the atoms `a…`. -/
syntax (name := bridgeFor) "bridge_for" ident+ : attr
/-- `@[assumption_for a…]`: this declaration is an assumption about the atoms `a…`. -/
syntax (name := assumptionFor) "assumption_for" ident+ : attr

/-- Registers the attribute `name`, which links a declaration to its arguments in `stage`. Each
argument must name an existing constant, so a misspelled atom is an error. -/
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

/-- `#export_explorer "path"` writes to `path` a JSON array with one record per declaration of
a `BridgingExamples` or `Common` module, skipping internal names and declarations without a
source position. A record has the fields:

* `name` and `module`;
* `start` and `end`, the first and last source lines, and `selection`, the line of the name;
* `kind`: `theorem`, `axiom`, `type` (an inductive type or structure), `constructor`,
  `recursor` or `definition`;
* `type`, the pretty-printed type, and `typeReferences`, the constants it mentions;
* `projectionOf`: for a structure field, the structure;
* `returnsProp`: the type ends in `Prop`, as for a predicate; `isProof`: the type is a
  proposition, as for a theorem; `isFunction`: the type has binders;
* `axioms`, the axioms the declaration depends on, and `links`, its attribute links. -/
elab "#export_explorer " output:str : command => do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some mod ← findModuleOf? name | continue
    unless mod.toString.startsWith "BridgingExamples." || mod.toString.startsWith "Common." do
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
