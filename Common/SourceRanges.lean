module
public meta import Common.Metadata

public meta section

open Lean Elab Command

namespace BridgingExamples.Metadata

private def proofRange? (env : Environment) (source : String) : Option (Name × Json) := do
  let command <- (Parser.runParserCategory env `command source).toOption
  let declaration <- command.find? (fun stx => stx.isOfKind ``Parser.Command.theorem)
  let value <- declaration.find? (fun stx => stx.getKind == ``Parser.Command.declValSimple ||
    stx.getKind == ``Parser.Command.declValEqns || stx.getKind == ``Parser.Command.whereStructInst)
  let start <- (if value.isOfKind ``Parser.Command.declValSimple then value[1] else value).getPos?
  let stop <- value.getTailPos?
  pure (declaration[1][0].getId,
    Json.mkObj [("startByte", toJson start.byteIdx), ("endByte", toJson stop.byteIdx)])

elab "#export_proof_ranges " output:str : command => do
  let env <- getEnv
  let text <- liftIO <| IO.FS.readFile output.getString
  let .ok json := Json.parse text | throwError "Invalid explorer metadata"
  let .ok exported := json.getArr? | throwError "Expected declarations"
  let mut declarations := exported
  for (name, info) in env.constants.toList do
    let .thmInfo _ := info | continue
    unless isPrivateName name && !env.isProjectionFn name do continue
    let some mod <- findModuleOf? name | continue
    unless mod.toString.startsWith "BridgingExamples." do continue
    let some ranges <- findDeclarationRangesCore? name | continue
    let source <- liftIO <| IO.FS.readFile (mod.toString.replace "." "/" ++ ".lean")
    let first := ranges.range.pos.line
    let last := ranges.range.endPos.line
    let snippet := "\n".intercalate (((source.splitOn "\n").drop (first - 1)).take (last - first + 1))
    let some (declName, _) := proofRange? env snippet | continue
    unless declName.getString! == (privateToUserName name).getString! do continue
    let axioms <- collectAxioms name
    let type <- liftTermElabM <| Meta.ppExpr info.type
    let linked := (links.getState env).filter (·.declaration == name)
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("start", toJson first), ("end", toJson last),
      ("selection", toJson ranges.selectionRange.pos.line),
      ("kind", toJson "theorem"), ("type", toJson type.pretty),
      ("projectionOf", Json.null), ("returnsProp", toJson false),
      ("isProof", toJson true), ("isFunction", toJson info.type.isForall),
      ("axioms", toJson (axioms.map Name.toString)),
      ("links", Json.arr <| linked.map fun link => Json.mkObj [
        ("role", toJson link.role.toString),
        ("targets", toJson (link.targets.map Name.toString))])]
  let mut sources : Std.HashMap String (List String) := {}
  let mut rows : Array Json := #[]
  for declaration in declarations do
    let mut proof := Json.null
    if declaration.getObjValD "kind" == toJson "theorem" &&
        (declaration.getObjValD "projectionOf").isNull then
      let .ok mod := (declaration.getObjValD "module").getStr? | continue
      let .ok first := (declaration.getObjValD "start").getNat? | continue
      let .ok last := (declaration.getObjValD "end").getNat? | continue
      let path := mod.replace "." "/" ++ ".lean"
      let lines <- match sources[path]? with
        | some lines => pure lines
        | none => do
          let source <- liftIO <| IO.FS.readFile path
          let lines := source.splitOn "\n"
          sources := sources.insert path lines
          pure lines
      let source := "\n".intercalate ((lines.drop (first - 1)).take (last - first + 1))
      proof := ((proofRange? env source).map Prod.snd).getD Json.null
    rows := rows.push <| declaration.setObjVal! "proofRange" proof
  liftIO <| IO.FS.writeFile output.getString (Json.arr rows).pretty

end BridgingExamples.Metadata
