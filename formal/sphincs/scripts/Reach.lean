import LeanForest
import FORS
import Lean

/-!
Reachability audit. `lake env lean scripts/Reach.lean` writes `reach.txt`, one line per declaration
of a `LeanForest` or `FORS` module: module, name, source line range, whether the proof terms of
the theorems pinned in the two `Axioms.lean` reach it, whether they or the names cited in README.md,
PROOF.md, FOREST.md and FORS.md (any declaration whose name ends with a code span) reach it, and
whether it is an instance. Declarations that reachability cannot see but the elaborator needs (rfl simp lemmas,
instances, names used only in simp lists) must be kept when pruning by hand.
-/

open Lean

def reachFrom (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    if let .inductInfo info := ci then used := used ++ info.ctors.toArray
    for c in used do
      if !visited.contains c then stack := stack.push c
  return visited

/-- The suffixes of a name, joined with `appendCore`: `++` would read a suffix like `_hyg.42` of a
hygienic name as a name with macro scopes, and panic. -/
def nameSuffixes (n : Name) : List Name :=
  (List.range n.getNumParts).map fun k =>
    (n.componentsRev.take (k + 1)).reverse.foldl Name.appendCore Name.anonymous

open Elab Command in
run_cmd do
  let env ← getEnv
  let forestGuards ← IO.FS.lines "LeanForest/Axioms.lean"
  let forsGuards ← IO.FS.lines "FORS/Axioms.lean"
  let guards := forestGuards ++ forsGuards
  let pinned := guards.filterMap fun line =>
    if line.startsWith "#print axioms " then some (line.drop 14).trimAscii.toString.toName else none
  let mut spans : NameSet := {}
  for doc in ["README.md", "PROOF.md", "FOREST.md", "FORS.md"] do
    let pieces := (← IO.FS.readFile doc).splitOn "`"
    for i in [0:pieces.length] do
      if i % 2 == 1 then spans := spans.insert pieces[i]!.toName
  let mut decls : Array (Name × Name) := #[]
  let mut cited : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    if !((`LeanForest).isPrefixOf moduleName || (`FORS).isPrefixOf moduleName) then continue
    for name in env.header.moduleData[i]!.constNames do
      decls := decls.push (moduleName, name)
      if (nameSuffixes name).any spans.contains then cited := cited.push name
  let fromPinned := reachFrom env pinned
  let fromAll := reachFrom env (pinned ++ cited)
  let mut out : String := ""
  for (moduleName, name) in decls do
    let range ← match ← findDeclarationRanges? name with
      | some rs => pure s!"{rs.range.pos.line}|{rs.range.endPos.line}"
      | none => pure "-|-"
    let flag (b : Bool) := if b then "1" else "0"
    out := out ++ s!"{moduleName}|{name}|{range}|{flag (fromPinned.contains name)}|" ++
      s!"{flag (fromAll.contains name)}|{flag (Meta.isInstanceCore env name)}\n"
  IO.FS.writeFile "reach.txt" out
  let count (s : NameSet) := (decls.filter fun (_, n) => s.contains n).size
  logInfo m!"pinned {pinned.size}, cited {cited.size}, declarations {decls.size}, reached from pinned {count fromPinned}, from pinned or cited {count fromAll}"
