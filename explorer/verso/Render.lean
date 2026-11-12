/-
Render SubVerso module exports with Verso's HTML renderer (`Highlighted.toHtml`).

  lake env lean --run explorer/verso/Render.lean [--assets DIR] [IN.json OUT.json]…

`IN.json` is the output of `subverso-extract-mod` for one module. `OUT.json` is
`{ "items": [html of each command, in order], "docs": { hover id: hover html } }`.
`--assets DIR` writes Verso's stylesheet and scripts. `explorer/verso.mjs` runs this file.
-/
import Verso.Code.Highlighted
import Verso.Code.Highlighted.WebAssets
import SubVerso.Module

open Lean Verso Verso.Code Verso.Output Verso.Code.Highlighted SubVerso.Highlighting SubVerso.Module

/-- Proof states are kept: the page shows the state after a tactic when the reader points at it. -/
def context : HighlightHtmlM.Context Doc.Genre.none where
  linkTargets := {}
  traverseContext := ()
  definitionIds := {}
  options := { inlineProofStates := true, definitionsAsTargets := false }

def render (input output : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let module ← IO.ofExcept (Module.fromJson? json)
  let action : HighlightHtmlM Doc.Genre.none (Array Html) :=
    module.items.mapM fun item => item.code.elideRedundantProofStates.toHtml
  let (htmls, state) := (action.run context).run {}
  let items := htmls.map fun html => Json.str (html.asString (breakLines := false))
  IO.FS.writeFile output <| Json.compress <|
    Json.mkObj [("items", Json.arr items), ("docs", state.dedup.docJson)]

def assets (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/highlighting.css") highlightingStyle
  IO.FS.writeFile (dir ++ "/highlighting.js") (highlightingJs (highlightJsonPromise := "window.versoDocs"))
  IO.FS.writeFile (dir ++ "/popper.js") WebAssets.popper
  IO.FS.writeFile (dir ++ "/tippy.js") WebAssets.tippy
  IO.FS.writeFile (dir ++ "/tippy-border.css") WebAssets.tippy.border.css
  IO.FS.writeFile (dir ++ "/marked.js") WebAssets.marked

partial def run : List String → IO UInt32
  | [] => pure 0
  | "--assets" :: dir :: rest => do assets dir; run rest
  | input :: output :: rest => do render input output; run rest
  | _ => do
    IO.eprintln "usage: Render.lean [--assets DIR] [IN.json OUT.json]…"
    pure 1

def main (args : List String) : IO UInt32 := run args
