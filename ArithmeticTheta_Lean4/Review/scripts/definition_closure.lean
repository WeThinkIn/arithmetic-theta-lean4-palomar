import Lean

/-! Measure the custom definitions needed to interpret elaborated statements.

This is a statement-reading metric, not a proof-dependency or correctness audit.
Run through `definition_closure.py`, which supplies source/module inventories,
object paths and hashes. Definition bodies and all constructor field types are
followed, so a mere abbreviation or record wrapper does not hide dependencies.
Proof subterms and theorem proof bodies are omitted. Predicates, hypotheses,
structure proof-field types, and the explicit predicates of Classical.choose
remain part of the traversal. External library declarations form a recorded
boundary rather than being counted as this project's new definitions.
-/

open Lean Meta

namespace ArithmeticThetaReview.DefinitionClosure

private def readField {α : Type} [FromJson α] (j : Json) (key : String) : IO α :=
  match j.getObjValAs? α key with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"Configuration field {key}: {e}"

/-- Open binders before inspecting proof status; no loose-bound-variable guess. -/
private partial def collectExpr (e : Expr) (names : IO.Ref NameHashSet) : MetaM Unit := do
  if ← isProof e then return
  match e with
  | .const n _ => names.modify (·.insert n)
  | .app f a => collectExpr f names; collectExpr a names
  | .lam n d b bi | .forallE n d b bi =>
    collectExpr d names
    withLocalDecl n bi d fun x => collectExpr (b.instantiate1 x) names
  | .letE n t v b _ =>
    collectExpr t names
    collectExpr v names
    withLetDecl n t v fun x => collectExpr (b.instantiate1 x) names
  | .proj n _ b =>
    names.modify (·.insert n)
    collectExpr b names
  | .mdata _ b => collectExpr b names
  | _ => pure ()

private def constants (es : Array Expr) : MetaM (Array Name) := do
  let ref ← IO.mkRef ({} : NameHashSet)
  for e in es do collectExpr e ref
  return (← ref.get).toArray

private def moduleOf (env : Environment) (name : Name) : Option Name := do
  let i ← env.getModuleIdxFor? name
  return env.header.modules[i.toNat]!.module

structure Node where
  name : Name
  moduleName : Name
  kind : String
  counted : Bool
  internal : Bool
  dependencies : Array Name

private def inspect (env : Environment) (name : Name) : MetaM Node := do
  let ci ← getConstInfo name
  let moduleName := (moduleOf env name).getD .anonymous
  let proof ← isProp ci.type
  let projection := env.isProjectionFn name
  let internal := name.isInternal
  let mut es := #[ci.type]
  let mut more := #[]
  let kind ← match ci with
    | .defnInfo v =>
      unless proof do es := es.push v.value
      pure (if proof then "proof_definition" else if projection then "projection" else "definition")
    | .opaqueInfo v =>
      unless proof do es := es.push v.value
      pure (if proof then "opaque_proof" else "opaque_definition")
    | .thmInfo _ => pure "theorem_type"
    | .inductInfo v =>
      more := v.ctors.toArray
      pure (if (getStructureInfo? env name).isSome then "structure" else "inductive")
    | .ctorInfo v => more := #[v.induct]; pure "constructor"
    | .recInfo v => more := v.all.toArray; pure "recursor"
    | .axiomInfo _ => pure "axiom_type"
    | .quotInfo _ => pure "quotient"
  let counted := !internal &&
    ["definition", "opaque_definition", "structure", "inductive"].contains kind
  return ⟨name, moduleName, kind, counted, internal, (← constants es) ++ more⟩

private def nodeJson (n : Node) : Json :=
  Json.mkObj [("name", toJson n.name.toString),
    ("module", toJson n.moduleName.toString), ("kind", toJson n.kind),
    ("counted", toJson n.counted), ("internal", toJson n.internal),
    ("dependencies", toJson (n.dependencies.map Name.toString |>.qsort (· < ·)))]

private def measure (env : Environment) (localModules : NameHashSet)
    (reviewModules : NameHashSet) (targets : Array String) : MetaM Json := do
  let mut cache : Std.HashMap Name Node := {}
  let mut reports := #[]
  for target in targets do
    let ci ← getConstInfo target.toName
    let some targetModule := moduleOf env ci.name
      | throwError "No module for imported target {target}"
    let mut pending ← constants #[ci.type]
    let direct := pending
    let mut seen : NameHashSet := {}
    let mut boundary : NameHashSet := {}
    let mut visited : Array Node := #[]
    while let some name := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some moduleName := moduleOf env name
        | throwError "No module for imported declaration {name}"
      unless localModules.contains moduleName do
        boundary := boundary.insert name
        continue
      let node ← match cache[name]? with
        | some n => pure n
        | none =>
          let n ← inspect env name
          cache := cache.insert name n
          pure n
      visited := visited.push node
      pending := pending ++ node.dependencies
    let counted := visited.filter (·.counted)
    let old := counted.filter fun n => !reviewModules.contains n.moduleName
    let new := counted.filter fun n => reviewModules.contains n.moduleName
    reports := reports.push <| Json.mkObj [
      ("target", toJson target),
      ("target_module", toJson targetModule.toString),
      ("custom_definition_count", toJson counted.size),
      ("original_definition_count", toJson old.size),
      ("review_definition_count", toJson new.size),
      ("visited_custom_declarations", toJson visited.size),
      ("external_boundary_count", toJson boundary.size),
      ("direct_constants", toJson (direct.map Name.toString |>.qsort (· < ·))),
      ("custom_definitions", toJson (counted.map (·.name.toString) |>.qsort (· < ·))),
      ("nodes", Json.arr (visited.qsort (fun a b => a.name.toString < b.name.toString) |>.map nodeJson)),
      ("external_boundary", toJson (boundary.toArray.map Name.toString |>.qsort (· < ·)))]
  return Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("metric", toJson "proof-erased recursive statement definition closure"),
    ("reports", Json.arr reports)]

def run (args : List String) : IO UInt32 := do
  let [configuration, output] := args
    | throw <| IO.userError "Expected CONFIGURATION.json OUTPUT.json"
  let cfg ← match Json.parse (← IO.FS.readFile configuration) with
    | .ok j => pure j
    | .error e => throw <| IO.userError e
  let paths : Array String ← readField cfg "search_path"
  let imports : Array String ← readField cfg "imports"
  let locals : Array String ← readField cfg "local_modules"
  let reviews : Array String ← readField cfg "review_modules"
  let targets : Array String ← readField cfg "targets"
  let sysroot ← findSysroot
  searchPathRef.set (paths.toList.map System.FilePath.mk ++ [sysroot / "lib/lean"])
  let env ← importModules (imports.map fun m => {module := m.toName}) {}
  let localSet := locals.foldl (fun s n => s.insert n.toName) ({} : NameHashSet)
  let reviewSet := reviews.foldl (fun s n => s.insert n.toName) ({} : NameHashSet)
  let options := ({} : Options).set `maxRecDepth (16384 : Nat)
    |>.set `maxHeartbeats (800000000 : Nat)
  let ctx : Core.Context := {fileName := "<definition-closure>", fileMap := FileMap.ofString "", options}
  let result ← (((measure env localSet reviewSet targets).run').run' ctx {env}).toBaseIO
  match result with
  | .error e => throw <| IO.userError (← e.toMessageData.toString)
  | .ok report =>
    IO.FS.writeFile output report.pretty
    for item in (← readField report "reports" : Array Json) do
      let target : String ← readField item "target"
      let count : Nat ← readField item "custom_definition_count"
      IO.println s!"{target}: {count} custom definitions"
    return 0

end ArithmeticThetaReview.DefinitionClosure

def main := ArithmeticThetaReview.DefinitionClosure.run
