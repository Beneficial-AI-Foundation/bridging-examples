module
public meta import Lean

/-!
# Explorer metadata

For each extracted atom, the explorer shows its spec, Crypto counterpart, bridge theorem and
assumptions. It finds them by name (`crate.Spec.f_spec`, `crate.Crypto.f`,
`crate.Bridge.f_bridge`, …). Where a name does not follow this pattern, one of the attributes
`@[spec_for a…]`, `@[crypto_for a…]`, `@[bridge_for a…]` and `@[assumption_for a…]` links the
declaration to the atoms `a…`.

`explorer/export.mjs` runs `#export_explorer "path"`, which writes every declaration of the
`BridgingExamples` and `Common` modules to a JSON file, with its source lines, type, axioms and
links. The explorer page is generated from that file.
-/

public meta section

open Lean Elab Command

namespace BridgingExamples.Metadata

/-- A link made by an attribute: `declaration` has the role `role` (`spec`, `crypto`, `bridge`
or `assumption`) for each extracted atom in `targets`. -/
structure Link where
  role : Name
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

/-- Registers the attribute `name`, which gives a declaration the role `role` for the atoms named
by its arguments. Each argument must name an existing constant, so a misspelled atom is an error.
-/
private def registerLink (name : Name) (role : Name) : IO Unit :=
  registerBuiltinAttribute {
    name
    descr := "Associate a local declaration with existing atoms."
    add := fun declaration stx kind => do
      let targets ← stx[1].getArgs.mapM fun target =>
        Elab.realizeGlobalConstNoOverloadWithInfo target
      links.add { role, declaration, targets } kind
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
* `axioms`, the axioms the declaration depends on, and `links`, the role and target atoms of
  each of its attributes. -/
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
        ("role", toJson link.role.toString),
        ("targets", toJson (link.targets.map Name.toString))])]
  liftIO <| IO.FS.writeFile output.getString (Json.arr rows).pretty

end BridgingExamples.Metadata
