module
import all P2M.Sol.S_AlgebraicCurve_tateTraceCompat_of_isSeparable
import Lean
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

def readAuditParts (path : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut paths := #[path]
  for suffix in [".server", ".private"] do
    let p := System.FilePath.mk (path.toString ++ suffix)
    if ← p.pathExists then paths := paths.push p
  readModuleDataParts paths

run_cmd do
  let root := "/home/Palomar/workspace/arithmetic-theta/evidence/"
  let moduleName := `P2M.Sol.S_AlgebraicCurve_tateTraceCompat_of_isSeparable
  let rel := "P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.olean"
  let variant ← IO.getEnv "PALOMAR_AUDIT_VARIANT"
  let some variant := variant | throwError "Missing audit variant"
  unless variant == "baseline" || variant == "candidate" do throwError "Unknown audit variant"
  let resolved ← findOLean moduleName
  let expected := root ++ "tate-proof-only-optimization-2538/overlay-" ++ variant ++ "/" ++ rel
  unless resolved.toString == expected do throwError "Unexpected import path: {resolved}"
  let oldParts ← readAuditParts (System.FilePath.mk (root ++ "shared-build-hotspot-profile-2525/outputs/" ++ rel))
  let currentParts ← readAuditParts resolved
  let mut regions : Array CompactedRegion := #[]
  let mut old : NameMap ConstantInfo := {}
  let mut current : NameMap ConstantInfo := {}
  for (data, region) in oldParts do
    regions := regions.push region
    for ci in data.constants do old := old.insert ci.name ci
  for (data, region) in currentParts do
    regions := regions.push region
    for ci in data.constants do current := current.insert ci.name ci
  let env ← getEnv
  let mut rows : Array Json := #[]
  let mut mismatches : Array String := #[]
  let mut added : Array String := #[]
  let mut changedBodies : Array String := #[]
  for (name, a) in old do
    let some b := current.find? name | mismatches := mismatches.push s!"missing:{name}"; continue
    let typeEq := a.type == b.type
    let levelsEq := a.levelParams == b.levelParams
    unless typeEq && levelsEq do mismatches := mismatches.push name.toString
    let mut bodyEq := true
    match a, b with
    | .thmInfo x, .thmInfo y => bodyEq := x.value == y.value
    | .defnInfo x, .defnInfo y =>
      bodyEq := x.value == y.value
      unless bodyEq do
        let defeq ← liftTermElabM do Lean.Meta.withTransparency .all (Lean.Meta.isDefEq x.value y.value)
        unless defeq do mismatches := mismatches.push s!"definition-body-not-defeq:{name}"
      unless x.hints == y.hints && x.safety == y.safety && x.all == y.all do
        mismatches := mismatches.push s!"definition-metadata:{name}"
    | _, _ => unless a == b do mismatches := mismatches.push s!"constant-kind-or-data:{name}"
    unless bodyEq do changedBodies := changedBodies.push name.toString
    let visible := (env.find? name).isSome
    let axs ← if visible then collectAxioms name else pure #[]
    rows := rows.push (Json.mkObj [("name", toJson name.toString),
      ("exact_type_expression_equal", toJson typeEq), ("universe_parameters_equal", toJson levelsEq),
      ("body_equal", toJson bodyEq), ("visible_for_axiom_audit", toJson visible),
      ("axioms", toJson (axs.map Name.toString))])
  for (name, _) in current do
    unless old.contains name do added := added.push name.toString
  let result := Json.mkObj [("variant", toJson variant), ("resolved_module", toJson resolved.toString),
    ("declarations", toJson rows), ("mismatches", toJson mismatches), ("added_declarations", toJson added),
    ("changed_bodies", toJson changedBodies), ("retained_regions", toJson regions.size)]
  IO.FS.writeFile (root ++ "tate-proof-only-optimization-2538/declarations-" ++ variant ++ ".json")
    (result.pretty ++ "\n")
  logInfo m!"DECLARATION_AUDIT variant={variant} declarations={rows.size} mismatches={mismatches.size} added={added.size} changedBodies={changedBodies.size}"
  unless mismatches.isEmpty do throwError "Exact declaration preservation audit failed"
