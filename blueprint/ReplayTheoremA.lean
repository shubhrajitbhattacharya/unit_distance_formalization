import Lean.Replay

open Lean

namespace ExactTheoremReplay

private def finalModule := `PlanarUnitDistances.ExactUnconditional
private def finalTheorem := `PlanarUnitDistances.IntegralGrid.exact_unconditional
private def exactStatement := `PlanarUnitDistances.TheoremA
private def isProjectModule (m : Name) := (`PlanarUnitDistances).isPrefixOf m

private structure Library where
  declarations : Std.HashMap Name (Name × ConstantInfo) := {}
  modules : NameSet := {}
  regions : Array CompactedRegion := #[]

/-- Read the final module and its project imports as proof data, outside the
environment in which the kernel will verify the selected declarations. -/
private partial def readProject (todo : List Name) (lib : Library) : IO Library := do
  let n :: more := todo | return lib
  if lib.modules.contains n then return ← readProject more lib
  let path ← findOLean n
  let mut paths := #[path]
  let server := OLeanLevel.server.adjustFileName path
  if ← server.pathExists then
    paths := paths.push server
    let priv := OLeanLevel.private.adjustFileName path
    if ← priv.pathExists then paths := paths.push priv
  let parts ← readModuleDataParts paths
  let some (m,_) := parts.back? | throw <| IO.userError s!"empty object {n}"
  let mut declarations := lib.declarations
  for name in m.constNames, c in m.constants do
    if let some (_,other) := declarations[name]? then
      unless other == c do throw <| IO.userError s!"different imported declarations named {name}"
    else
      declarations := declarations.insert name (n,c)
  let imports := m.imports.toList.map (·.module) |>.filter isProjectModule
  readProject (imports ++ more) {
    declarations := declarations
    modules := lib.modules.insert n
    regions := lib.regions ++ parts.map (·.2)
  }

private def dependencies (c : ConstantInfo) : NameSet :=
  match c with
  | .inductInfo i => c.getUsedConstantsAsSet ++ NameSet.ofList i.all
  | _ => c.getUsedConstantsAsSet

private def permittedAxiom (n : Name) :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

private def verify (base : Environment) (lib : Library)
    (inventory edges : Option System.FilePath) : IO Unit := do
  if base.header.moduleNames.any isProjectModule || (base.find? finalTheorem).isSome then
    throw <| IO.userError "a project module is already present in the Mathlib base"
  let some (owner, .thmInfo endpoint) := lib.declarations[finalTheorem]?
    | throw <| IO.userError "the endpoint is missing or is not a theorem"
  unless owner == finalModule && endpoint.type == mkConst exactStatement && endpoint.levelParams.isEmpty do
    throw <| IO.userError "incorrect endpoint owner or literal type; expected TheoremA with zero assumptions"
  let mut seen : NameSet := {}
  let mut visitedModules : NameSet := {}
  let mut external : NameSet := {}
  let mut checked : Std.HashMap Name ConstantInfo := {}
  let mut todo := [finalTheorem]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some previous := base.find? n then
      if let some (_,projectCopy) := lib.declarations[n]? then
        unless previous == projectCopy do throw <| IO.userError s!"conflicting Mathlib declaration {n}"
      external := external.insert n
      continue
    let some (owner,c) := lib.declarations[n]? | throw <| IO.userError s!"missing {n}"
    if c.isUnsafe || c.isPartial then throw <| IO.userError s!"unsafe or partial project dependency {n}"
    if let .axiomInfo _ := c then throw <| IO.userError s!"project axiom {n}"
    visitedModules := visitedModules.insert owner
    checked := checked.insert n c
    todo := (dependencies c).toList ++ todo
  let mut outsideSeen : NameSet := {}
  let mut axioms : NameSet := {}
  todo := external.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if outsideSeen.contains n then continue
    outsideSeen := outsideSeen.insert n
    let some c := base.find? n | throw <| IO.userError s!"missing external dependency {n}"
    if c.isUnsafe || c.isPartial then
      throw <| IO.userError s!"unsafe or partial external dependency {n}"
    if let .axiomInfo _ := c then
      unless permittedAxiom n do throw <| IO.userError s!"unexpected axiom {n}"
      axioms := axioms.insert n
    todo := (dependencies c).toList ++ todo
  let verified ← base.toKernelEnv.replay checked
  let some (.thmInfo replayed) := verified.find? finalTheorem
    | throw <| IO.userError "the kernel did not add the final theorem"
  unless replayed.type == mkConst exactStatement && replayed.value == endpoint.value do
    throw <| IO.userError "the kernel did not preserve the exact theorem type and proof"
  let ordered := checked.toArray.map (·.1) |>.qsort Name.lt
  let mut rows := "module\tdeclaration\n"
  for n in ordered do
    let some (m, _) := lib.declarations[n]? | throw <| IO.userError s!"missing owner for {n}"
    if (verified.find? n).isNone then throw <| IO.userError s!"declaration absent after replay: {n}"
    rows := rows ++ s!"{m}\t{n}\n"
  if let some path := inventory then
    IO.FS.writeFile path rows
  if let some path := edges then
    IO.FS.withFile path .write fun file => do
      file.putStrLn "dependent\tdependency"
      for n in ordered do
        let some c := checked[n]? | throw <| IO.userError s!"missing declaration {n}"
        for d in (dependencies c).toArray.qsort Name.lt do
          if checked.contains d then file.putStrLn s!"{n}\t{d}"
  IO.println s!"Verified {finalTheorem} : {exactStatement}."
  IO.println "The declaration has zero premises, zero universe parameters, and the literal target type."
  IO.println s!"Replayed {checked.size} project declarations from {visitedModules.size} modules against Mathlib. Loaded {lib.modules.size} project modules as input data."
  IO.println s!"Inspected {outsideSeen.size} transitive external declarations reached through {external.size} direct external dependencies."
  IO.println s!"Axioms: {axioms.toArray.qsort Name.lt}."
  IO.println "No reachable project axiom, unsafe declaration, or partial declaration."

end ExactTheoremReplay

unsafe def main (args : List String) : IO Unit := do
  let (inventory, edges) ← match args with
    | [] => pure (none, none)
    | [path] => pure (some (System.FilePath.mk path), none)
    | [path, direct] => pure (some (System.FilePath.mk path), some (System.FilePath.mk direct))
    | _ => throw <| IO.userError "Usage: ReplayTheoremA.lean [declarations.tsv [edges.tsv]]"
  initSearchPath (← findSysroot)
  unless Lean.versionString == "4.35.0" do throw <| IO.userError s!"unexpected Lean version {Lean.versionString}"
  let lib ← ExactTheoremReplay.readProject [ExactTheoremReplay.finalModule] {}
  withImportModules #[{module := `Mathlib}] {} (fun base => ExactTheoremReplay.verify base lib inventory edges) (trustLevel := 0)
