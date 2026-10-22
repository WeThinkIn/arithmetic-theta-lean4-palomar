module
public import Mathlib
import all Lean.Meta.Match.Match
macro "eu1129":command=> `(@[expose] public section)
macro "au1129":command=> `(set_option autoImplicit false)
macro "ru1129":command=> `(set_option backward.isDefEq.respectTransparency false)
macro "nu1129":command=> `(noncomputable section)
elab "ec979" n:num:command=> do
  for _ in [:n.getNat] do
    let ss ← Lean.Elab.Command.getScopes
    let h := ss.head!.header
    if h.isEmpty then Lean.Elab.Command.elabCommand (← `(end))
    else Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent (Lean.Name.str Lean.Name.anonymous h))))
eu1129 au1129 open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z7, SheafOfModules → z8, CommRingCat → z9, LinearMap → z10, ModuleCat → z11, AddMonoidHom → z12, RingHom → z13, IsDomain → z14, IsIntegrallyClosed → z15, Finsupp → z18, SetLike → z19, Submodule → z20, HomogeneousIdeal → z22, HomogeneousLocalization → z23, IsScalarTower → z25, AddSubgroupClass → z26, AddSubmonoidClass → z27, Algebra → z28, Nonempty → z29 open AlgebraicGeometry renaming Scheme → zS set_option maxHeartbeats 2000000 set_option maxRecDepth 8192 set_option backward.privateInPublic true macro "rc590":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}) set_option hygiene false set_option quotPrecheck false set_option quotPrecheck true set_option hygiene true eu1129
open Lean Elab Tactic Meta in
elab "p2m_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
  g'.withContext do
    let tgt ← g'.getType
    let v ← Term.withSynthesize <| elabTermEnsuringType e tgt
    let v ← instantiateMVars v
    if v.hasExprMVar then throwError "p2m_exact_reverting: unassigned metavariables remain"
    g'.assign v
  replaceMainGoal []
open Lean Elab Command Meta in
elab "#p2m_type_eq " a:ident b:ident : command => liftTermElabM do
  let some ia := (← getEnv).find? a.getId | throwError m!"#p2m_type_eq: unknown constant {a.getId}"
  let some ib := (← getEnv).find? b.getId | throwError m!"#p2m_type_eq: unknown constant {b.getId}"
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then
    let mut pinned : Array String := #[]
    let mut seen : Array Level := #[]
    for l in la, nm in ia.levelParams do
      let l' ← instantiateLevelMVars l
      match l' with
      | .mvar _ => if seen.contains l' then pinned := pinned.push s!"{nm} (identified with another)" else seen := seen.push l'
      | _ => pinned := pinned.push s!"{nm} := {l'}"
    if pinned.isEmpty then
      logInfo m!"P2M_TYPE_EQ {a.getId} {b.getId}"
    else
      throwError m!"P2M_UNDERGENERAL: the statement's universes {pinned} had to be specialised to match the proof — the proof is less general than the card"
  else
    throwError m!"P2M_TYPE_MISMATCH\n  {a.getId} : {ta}\n  {b.getId} : {tb}"
open Lean Elab Command in elab "p2m_ns " s:str : command => modifyEnv fun env => env.registerNamespace s.getString.toName
open Lean Elab Command in
meta def p2mOpenCore (s : String) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue
    let parts := w.splitOn "~"
    let ns := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (fun h => h.toName)
    modifyScope fun sc => { sc with openDecls := OpenDecl.simple ns hidden :: sc.openDecls }
    activateScoped ns
open Lean Elab Command in elab "p2m_open " s:str : command => p2mOpenCore s.getString
open Lean Elab Command in
elab "p2m_export_all " n:str s:str : command => do
  let env ← getEnv
  let short := s.getString.toName
  let base := n.getString.toName ++ short
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₂.toList do
    let u := (privateToUserName? c).getD c
    if base.isPrefixOf u && u != base && !u.isInternalDetail then
      al := al.push (cur ++ short ++ u.replacePrefix base Name.anonymous, c)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env
open Lean Elab Command Meta in
elab "#p2m_type_eq_warn " a:ident b:ident : command => liftTermElabM do
  let some ia := (← getEnv).find? a.getId | throwError m!"#p2m_type_eq_warn: unknown constant {a.getId}"
  let some ib := (← getEnv).find? b.getId | throwError m!"#p2m_type_eq_warn: unknown constant {b.getId}"
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then logInfo m!"P2M_TYPE_EQ {a.getId} {b.getId}"
  else logWarning m!"P2M_DUP_TYPE_MISMATCH (non-fatal)\n  {a.getId} : {ta}\n  {b.getId} : {tb}"
open Lean Elab Command in
elab "p2m_alias " a:str n:str : command => do
  let env ← getEnv
  let full := n.getString.toName
  let tgt := if env.contains full then some full else (let p := mkPrivateName env full; if env.contains p then some p else none)
  match tgt with
  | some t => modifyEnv fun env => addAlias env a.getString.toName t
  | none => pure ()
open Lean Elab Command in
elab "p2m_open_scoped " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    activateScoped ((w.splitOn "~").head!).toName
syntax (name:= p2mOpenIn) "p2m_open " str " in" ppLine command: command open Lean in macro_rules | `(p2m_open $s:str in $c:command) => return mkNullNode #[← `(section), ← `(p2m_open $s:str), c, ← `(end)]
open Lean Elab Command in
elab "p2m_export " n:str m:str : command => do
  let env ← getEnv
  let ns := n.getString.toName
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for w in m.getString.splitOn " " do
    if w.isEmpty then continue
    let full := ns ++ w.toName
    if env.contains full then al := al.push (cur ++ w.toName, full)
    else
      let prv := mkPrivateName env full
      if env.contains prv then al := al.push (cur ++ w.toName, prv)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env
open Lean Elab Command in
elab "p2m_reactivate " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := w.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env
macro "p2m_open_scoped " s:str " in " c:command : command => `(section p2m_open_scoped $s $c end) namespace AlgebraicCurve ec979 1 namespace AlgebraicCurve.IdealHom ec979 2 namespace AlgebraicCurve.RelEffDivisor ec979 2 namespace AlgebraicGeometry ec979 1 namespace AlgebraicGeometry.GeometricallyIrreducible ec979 2 namespace AlgebraicGeometry.GradedOAlgebra ec979 2 namespace AlgebraicGeometry.OModulePresheaf ec979 2 namespace AlgebraicGeometry.OModulePresheaf.AffHom ec979 3 namespace AlgebraicGeometry.OModulePresheaf.AffSES ec979 3 namespace AlgebraicGeometry.OModulePresheaf.Hom ec979 3 namespace AlgebraicGeometry.OModulePresheaf.Leray ec979 3 namespace AlgebraicGeometry.OModulePresheaf.SES ec979 3 namespace AlgebraicGeometry.OModulePresheaf.internalHom ec979 3 namespace AlgebraicGeometry.ProjSpace ec979 2 namespace AlgebraicGeometry.RelEffCartierDiv ec979 2 namespace AlgebraicGeometry.RelPicard ec979 2 namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle ec979 3 namespace AlgebraicGeometry.RelPicard.relPicardPresheaf ec979 3 namespace AlgebraicGeometry.Scheme ec979 2 namespace AlgebraicGeometry.Scheme.Hom ec979 3 namespace AlgebraicGeometry.Scheme.IdealSheafData ec979 3 namespace AlgebraicGeometry.Scheme.IdealSheafData.IdealHom ec979 4 namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible ec979 4 namespace AlgebraicGeometry.Scheme.Modules ec979 3 namespace AlgebraicGeometry.Scheme.Modules.IsInvertible ec979 4 namespace AlgebraicGeometry.Scheme.OrderedAffineCover ec979 3 namespace AlgebraicGeometry.Scheme.OrderedAffineCoverOf ec979 3
namespace AlgebraicGeometry.Scheme.PresheafOfModules ec979 3 namespace AlgebraicGeometry.Scheme.PresheafOfModulesOfCommRing ec979 3 namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover ec979 3 namespace AlgebraicModelCubicR0144 ec979 1 namespace ArithmeticThetaAlgebraicCoordinatesR0143 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion ec979 3 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux ec979 4 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux.Sys ec979 5 namespace ArithmeticThetaAnnularThetaR0128 ec979 1 namespace ArithmeticThetaAnnularTorsionPrereqR0053 ec979 1 namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent ec979 2 namespace ArithmeticThetaBoundaryHodgeR0182 ec979 1 namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182 ec979 2 namespace ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182 ec979 2 namespace ArithmeticThetaCommonHalfHodgeR0185 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential ec979 2
namespace ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart ec979 2 namespace ArithmeticThetaCompatibleLevelR0178 ec979 1 namespace ArithmeticThetaComponentDegreeR0184 ec979 1 namespace ArithmeticThetaComponentDegreeR0184.GeometricComponentCuspBoundR0184 ec979 2 namespace ArithmeticThetaCorrectedGammaR0061 ec979 1 namespace ArithmeticThetaCubicModelR0144 ec979 1 namespace ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144 ec979 2 namespace ArithmeticThetaCyclicPresentationR0174 ec979 1 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174 ec979 2 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicAlgebra ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.FibreCohomology ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.FramedCurve ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Generation ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic ec979 3
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GradedEvaluation ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel.Normalized ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneCoordinates ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneQuotient ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneSectionRing ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PointedIso ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Actual ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.AlgebraicGeometry ec979 5 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.AlgebraicGeometry.OModulePresheaf ec979 6
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.AlgebraicGeometry.OModulePresheaf.CechBaseChange ec979 7 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology.LinearMap ec979 5 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology.LinearMap.FlatKerBC ec979 6 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology.LinearMap.HomologyTransport ec979 6 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.Engine19 ec979 5 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.P2mSectionsBaseChangeH0 ec979 5 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Vanishing ec979 4 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames ec979 3
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionRing ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.TensorGrouping ec979 3 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.VeroneseGeneration ec979 3 namespace ArithmeticThetaFullLevelCoverR0175 ec979 1 namespace ArithmeticThetaGeneralEllipticKatoR0168 ec979 1 namespace ArithmeticThetaGeneralEllipticKatoR0168.BaseChange ec979 2 namespace ArithmeticThetaGenericEvaluationR0140 ec979 1 namespace ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140 ec979 2 namespace ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140 ec979 2 namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141 ec979 2 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.Completion ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.GammaComparison ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.GenericConstruction ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.ModelConstruction ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.ScalarSeries ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.StageConstruction ec979 3
namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.ThetaAction ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141 ec979 2 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ActualStages ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CyclicMap ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.FactorCompletion ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.FinalConstruction ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ModelShift ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.RawAction ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.RawIteration ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ShiftPeriod ec979 3 namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.StageLocalShift ec979 3 namespace ArithmeticThetaGlobalFourTorsionR0190 ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic ec979 2 namespace ArithmeticThetaGlobalProjectiveRatiosR0266.GlobalArithmeticProjectiveRatios ec979 2 namespace ArithmeticThetaGlobalization ec979 1 namespace ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree ec979 2 namespace ArithmeticThetaIdentitySectionsR0138 ec979 1
namespace ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138 ec979 2 namespace ArithmeticThetaIdentitySectionsR0138.IdentityStageSectionRealizationR0138 ec979 2 namespace ArithmeticThetaIndexedOverlapsR0058 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129.Atlas ec979 2 namespace ArithmeticThetaInvariantRatiosR0265 ec979 1 namespace ArithmeticThetaInvariantRatiosR0265.Arithmetic ec979 2 namespace ArithmeticThetaIsogenyHalfLinesR0193 ec979 1 namespace ArithmeticThetaLegendreAtlasR0176 ec979 1 namespace ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent ec979 2 namespace ArithmeticThetaLegendreComparisonR0177 ec979 1 namespace ArithmeticThetaLevelCompactificationR0179 ec979 1 namespace ArithmeticThetaLineRoot ec979 1 namespace ArithmeticThetaLocalWeierstrassR0203 ec979 1 namespace ArithmeticThetaLocalWeierstrassR0203.Family ec979 2 namespace ArithmeticThetaMarkedGroupLawR0146 ec979 1 namespace ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw ec979 2 namespace ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196 ec979 2 namespace ArithmeticThetaModelSymmetriesR0137 ec979 1 namespace ArithmeticThetaModelSymmetriesR0137.TowerScalarTranslation ec979 2 namespace ArithmeticThetaNodeCharts ec979 1 namespace ArithmeticThetaNormalizedSections ec979 1 namespace ArithmeticThetaOpenHodgeR0180 ec979 1 namespace ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180 ec979 2 namespace ArithmeticThetaPolygonCartierR0133 ec979 1
namespace ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133 ec979 2 namespace ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133 ec979 2 namespace ArithmeticThetaPolygonCohomologyR0131 ec979 1 namespace ArithmeticThetaPositiveLineR0134 ec979 1 namespace ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134 ec979 2 namespace ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134 ec979 2 namespace ArithmeticThetaProjectiveEffectivityR0135 ec979 1 namespace ArithmeticThetaPullback ec979 1 namespace ArithmeticThetaRelativeCyclicQuotientR0173 ec979 1 namespace ArithmeticThetaRelativeDiscriminantR0171 ec979 1 namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ec979 2 namespace ArithmeticThetaRelativeKatoNaturalityR0170 ec979 1 namespace ArithmeticThetaRelativeKatoR0169 ec979 1 namespace ArithmeticThetaScaledAnnularR0050 ec979 1 namespace ArithmeticThetaScaledTateBridgeR0046 ec979 1 namespace ArithmeticThetaScaledTateCompletionExtensionR0048 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence ec979 2 namespace ArithmeticThetaSchemeHodgeR0205 ec979 1 namespace ArithmeticThetaSchemeHodgeR0205.AffineConormalHodgeNaturality ec979 2 namespace ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal ec979 2 namespace ArithmeticThetaSchemeLevelR0204 ec979 1 namespace ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier ec979 2 namespace ArithmeticThetaSchemeLevelR0204.SchemeFamilyBaseChange ec979 2
namespace ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal ec979 2 namespace ArithmeticThetaSchemeSchrodingerR0261 ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259 ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology ec979 2 namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.FiniteStage ec979 3 namespace ArithmeticThetaSchemeThetaNaturalityR0262 ec979 1 namespace ArithmeticThetaSchrodingerR0119 ec979 1 namespace ArithmeticThetaSectionOrder ec979 1 namespace ArithmeticThetaSharpCoverR0194 ec979 1 namespace ArithmeticThetaSharpCoverR0194.CanonicalHalf ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.FixedPointPullback ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.GroupInversion ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.GroupTranslation ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel ec979 5 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.Scalar ec979 5 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.Midpoint
ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation ec979 3 namespace ArithmeticThetaSheafTensor ec979 1 namespace ArithmeticThetaSimultaneousUnaryR0187 ec979 1 namespace ArithmeticThetaSquareLinesR0192 ec979 1 namespace ArithmeticThetaSymmetricMarkingR0142 ec979 1 namespace ArithmeticThetaTateCuspsR0181 ec979 1 namespace ArithmeticThetaTateSchemeMarkingR0263 ec979 1 namespace ArithmeticThetaTateSeries ec979 1 namespace ArithmeticThetaTensorPower ec979 1 namespace CategoryTheory ec979 1 namespace CategoryTheory.Limits ec979 2 namespace DoubleComplex ec979 1 namespace DoubleComplex.SubQuot ec979 2 namespace EllipticSignDescent ec979 1 namespace GoodReductionJacobian ec979 1 namespace GoodReductionJacobian.RelativeGroupLaw ec979 2 namespace GoodReductionJacobian.RelativeGroupLaw.IsCommutative ec979 3 namespace HomogeneousIdealQuotientGrading ec979 1 namespace NeronModelInfra ec979 1 namespace NeronModelInfra.NeronModelPropertyBundle ec979 2 namespace NeronSpecialFibreInfra ec979 1 namespace P2MW ec979 1 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso ec979 2 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry ec979 3 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme ec979 4 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules ec979 5
namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2 ec979 6 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.Hom ec979 7 namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull ec979 3 namespace PresheafOfModules ec979 1 namespace PresheafOfModules.InternalHom ec979 2 namespace PresheafOfModules.PullbackMonoidal ec979 2 namespace ProjSpaceCech ec979 1 namespace ProjSpaceCech.GradedModule ec979 2 namespace ProjSpaceCech.GradedModule.Frac ec979 3 namespace ProjSpaceCech.GradedModule.Frac.Rel ec979 4 namespace ProjSpaceCech.GradedModule.H ec979 3 namespace ProjSpaceCech.GradedModule.Hom ec979 3 namespace ProjSpaceCech.GradedModule.Presentation ec979 3 namespace ProjSpaceCech.GradedModule.sec ec979 3 namespace ProjSpaceCech.Idx ec979 2 namespace ProjSpaceCech.Twist ec979 2 namespace ProjSpaceCech.Twist.H ec979 3 namespace ProjSpaceCech.Twist.Mon ec979 3 namespace ProjSpaceCech.Twist.cochain ec979 3 namespace ProjWeierstrassCubicPrime ec979 1 namespace SheafOfModules ec979 1 namespace WeierstrassCurve ec979 1 namespace WeierstrassCurve.DrinfeldGlobal ec979 2 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel.RelativeGroupLaw ec979 2 namespace HomogeneousIdealQuotientGrading ec979 1 section rc590 eu1129 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
au1129 nu1129 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry namespace NeronModelInfra variable (R K: Type u) [z0 R] [z1 K] [z28 R K] abbrev SchemeHomOver {B Y X: Scheme.{u}} (g: Y ⟶ B) (f: X ⟶ B):= {φ: Y ⟶ X // φ ≫ f = g} ec979 1 ec979 1 ec979 1 ec979 1 namespace WeierstrassProjModel namespace RelativeGroupLaw ec979 1 ec979 1 namespace WeierstrassProjModel namespace RelativeGroupLaw ec979 1 ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 section rc590 eu1129 au1129 ru1129 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false universe u v' u' open CategoryTheory MonoidalCategory Limits Opposite namespace PresheafOfModules section general variable {C: Type u'} [Category.{v'} C] {R: Cᵒᵖ ⥤ z9.{u}} (F N: z7.{u} (R ⋙ forget₂ _ _)) namespace InternalHom abbrev PiFamily (X: Cᵒᵖ): Type (max u u' v'):= ∀ ⦃Y: Cᵒᵖ⦄ (_: X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y)
variable {F N} in def IsNatural {X: Cᵒᵖ} (φ: PiFamily F N X): Prop:= ∀ ⦃Y Z: Cᵒᵖ⦄ (f: X ⟶ Y) (g: Y ⟶ Z) (x: F.obj Y), N.map g (φ f x) = φ (f ≫ g) (F.map g x)
def naturalFamilies (X : Cᵒᵖ) : AddSubgroup (PiFamily F N X) where
  carrier := {φ | IsNatural φ}
  zero_mem' := by
    intro Y Z f g x
    simp only [Pi.zero_apply, LinearMap.zero_apply]
    exact (N.map g).hom.map_zero
  add_mem' := by
    intro φ ψ hφ hψ Y Z f g x
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hφ f g x, hψ f g x]
  neg_mem' := by
    intro φ hφ Y Z f g x
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hφ f g x]
variable {F N} @[ext] lemma naturalFamilies_ext {X: Cᵒᵖ} {φ ψ: naturalFamilies F N X} (h: ∀ ⦃Y: Cᵒᵖ⦄ (f: X ⟶ Y) (x: F.obj Y), φ.1 f x = ψ.1 f x): φ = ψ:= by sorry lemma congr_app {X: Cᵒᵖ} (φ: naturalFamilies F N X) {Y: Cᵒᵖ} {f g: X ⟶ Y} (h: f = g) (x: F.obj Y): φ.1 f x = φ.1 g x:= by sorry
instance instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩
@[simp] lemma smul_app {X: Cᵒᵖ} (r: R.obj X) (φ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (r • φ).1 f x = R.map f r • φ.1 f x:= by sorry @[simp] lemma add_app {X: Cᵒᵖ} (φ ψ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (φ + ψ).1 f x = φ.1 f x + ψ.1 f x:= by sorry
set_option hygiene false
set_option quotPrecheck false
local notation "Hg1" => (@CategoryTheory.Functor.comp.{u_3, u_1, u_1, u_2, u_1 + 1, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} R (@CategoryTheory.forget₂.{u_1, u_1, u_1 + 1, u_1, u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (fun (R S : CommRingCat.{u_1}) => @RingHom.{u_1, u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.commRing.{u_1} R)))) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (CommRingCat.commRing.{u_1} S))))) CommRingCat.carrier.{u_1} (fun (X Y : CommRingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} X) ((fun (X : CommRingCat.{u_1}) => @CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.commRing.{u_1} X))) X)) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (CommRingCat.commRing.{u_1} Y))))) CommRingCat.instConcreteCategoryRingHomCarrier.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} (fun (R S : RingCat.{u_1}) => @RingHom.{u_1, u_1} (RingCat.carrier.{u_1} R) (RingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} R) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} R) (RingCat.ring.{u_1} R))) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} S) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} S) (RingCat.ring.{u_1} S)))) RingCat.carrier.{u_1} (fun (X Y : RingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (RingCat.carrier.{u_1} X) (RingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} X) ((fun (X : RingCat.{u_1}) => @Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} X) (RingCat.ring.{u_1} X)) X)) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} Y) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} Y) (RingCat.ring.{u_1} Y)))) RingCat.instConcreteCategoryRingHomCarrier.{u_1} CommRingCat.hasForgetToRingCat.{u_1}))
local notation "Hg5" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 i)
local notation "Hg38" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F i)
local notation "Hg21" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38)
local notation "Hg39" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N i)
local notation "Hg4" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R i)
local notation "Hg33" => (@CommRing.toRing.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4))
local notation "Hg52" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg39)
local notation "Hg51" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg38)
local notation "Hg17" => (@AddCommGroup.toAddCommMonoid.{u_1} Hg21 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38))
local notation "Hg12" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4)))
local notation "Hg27" => (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) Hg12))
local notation "Hg23" => (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg32" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg31" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38)
local notation "Hg19" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg11" => (@LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32)
local notation "Hg22" => (@Quiver.opposite.{u_2, u_3} C (@CategoryTheory.ReflQuiver.toQuiver.{u_3, u_2} C (@CategoryTheory.catToReflQuiver.{u_3, u_2} C inst)))
local notation "Hg48" => (@Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i)
local notation "Hg14" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R Y)
local notation "Hg30" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg14)))
local notation "Hg47" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N Y)
local notation "Hg46" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F Y)
local notation "Hg15" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 Y)
local notation "Hg42" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)
local notation "Hg41" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)
local notation "Hg6" => (fun (Y : Opposite.{u_2 + 1} C) => @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X Y → @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (CommRingCat.carrier.{u_1} Hg14) Hg30 Hg30 (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) Hg30)) Hg41 Hg42 (@AddCommGroup.toAddCommMonoid.{u_1} Hg41 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)) (@AddCommGroup.toAddCommMonoid.{u_1} Hg42 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47))
local notation "Hg10" => (fun (x : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32)
local notation "Hg0" => (@Pi.addGroup.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addGroup.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg51 Hg52 Hg27)) i)
local notation "Hg13" => (@PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X)
local notation "Hg45" => (@AddSubgroup.instSetLike.{max (max u_1 u_2) u_3} Hg13 Hg0)
local notation "Hg29" => (@PresheafOfModules.InternalHom.naturalFamilies.{u_1, u_3, u_2} C inst R F N X)
local notation "Hg2" => (@AddSubmonoidClass.toAddCommMonoid.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@Pi.addCommMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addCommMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @LinearMap.addCommMonoid.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg51 Hg52 Hg27) i) (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg45 (@AddSubgroupClass.toAddSubmonoidClass.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 (@Pi.subNegMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.subNegMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddGroup.toSubNegMonoid.{u_1} Hg11 (@AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg31 Hg32 Hg27))) i) Hg45 (@AddSubgroup.instAddSubgroupClass.{max (max u_1 u_2) u_3} Hg13 Hg0)) Hg29)
local notation "Hg20" => (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 Hg45)
local notation "Hg3" => (@Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x)
local notation "Hg18" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R X)
local notation "Hg7" => (CommRingCat.carrier.{u_1} Hg18)
local notation "Hg16" => (@instHSMul.{u_1, max (max u_1 u_2) u_3} Hg7 Hg3 (@PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies.{u_1, u_3, u_2} C inst R F N X))
local notation "Hg26" => (@OfNat.ofNat.{max (max u_1 u_2) u_3} Hg3 (nat_lit 0) (@Zero.toOfNat0.{max (max u_1 u_2) u_3} Hg3 (@AddZero.toZero.{max (max u_1 u_2) u_3} Hg3 (@AddZeroClass.toAddZero.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddZeroClass.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2))))))
local notation "Hg28" => (@CommSemiring.toSemiring.{u_1} Hg7 (@CommRing.toCommSemiring.{u_1} Hg7 (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg18)))
local notation "Hg40" => (@instHAdd.{max (max u_1 u_2) u_3} Hg3 (@AddSemigroup.toAdd.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddSemigroup.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2))))
local notation "Hg49" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 s φ)
local notation "Hg50" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r φ)
set_option quotPrecheck true
set_option hygiene true
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_1.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r s : CommRingCat.carrier.{u_1} Hg18) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@HMul.hMul.{u_1, u_1, u_1} Hg7 Hg7 Hg7 (@instHMul.{u_1} Hg7 (@Semigroup.toMul.{u_1} Hg7 (@Monoid.toSemigroup.{u_1} Hg7 (@Semiring.toMonoid.{u_1} Hg7 Hg28)))) r s) φ) (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r Hg49) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_2.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@OfNat.ofNat.{u_1} Hg7 (nat_lit 1) (@One.toOfNat1.{u_1} Hg7 (@MulOne.toOne.{u_1} Hg7 (@MulOneClass.toMulOne.{u_1} Hg7 (@Monoid.toMulOneClass.{u_1} Hg7 (@Semiring.toMonoid.{u_1} Hg7 Hg28)))))) φ) φ := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_3.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r : CommRingCat.carrier.{u_1} Hg18), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r Hg26) Hg26 := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_4.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r : CommRingCat.carrier.{u_1} Hg18) (φ ψ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 Hg40 φ ψ)) (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 Hg40 Hg50 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r ψ)) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_5.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r s : CommRingCat.carrier.{u_1} Hg18) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@HAdd.hAdd.{u_1, u_1, u_1} Hg7 Hg7 Hg7 (@instHAdd.{u_1} Hg7 (@Distrib.toAdd.{u_1} Hg7 (@instDistribOfSemiring.{u_1} Hg7 Hg28))) r s) φ) (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 (@instHAdd.{max (max u_1 u_2) u_3} Hg3 (@AddCommMagma.toAdd.{max (max u_1 u_2) u_3} Hg3 (@AddCommSemigroup.toAddCommMagma.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddCommSemigroup.{max (max u_1 u_2) u_3} Hg3 Hg2)))) Hg50 Hg49) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_6.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@OfNat.ofNat.{u_1} Hg7 (nat_lit 0) (@Zero.toOfNat0.{u_1} Hg7 (@MulZeroClass.toZero.{u_1} Hg7 (@instMulZeroClassOfSemiring.{u_1} Hg7 Hg28)))) φ) Hg26 := by sorry
run_cmd do
  for i in [1:7] do
    let n := ("PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_" ++ toString i).toName
    let ci ← Lean.getConstInfo n
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
instance instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp
variable (F N)
def restrict {X X' : Cᵒᵖ} (h : X ⟶ X') : naturalFamilies F N X →+ naturalFamilies F N X' where
  toFun φ := ⟨fun Y f => φ.1 (h ≫ f), fun Y Z f g x => by
    rw [φ.2 (h ≫ f) g x, Category.assoc]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
@[simps obj] def presheaf : Cᵒᵖ ⥤ Ab.{max u u' v'} where
  obj X := AddCommGrpCat.of (naturalFamilies F N X)
  map h := AddCommGrpCat.ofHom (restrict F N h)
  map_id X := by
    ext φ Y f x
    change φ.1 (𝟙 X ≫ f) x = φ.1 f x
    rw [Category.id_comp]
  map_comp h h' := by
    ext φ Y f x
    change φ.1 ((h ≫ h') ≫ f) x = φ.1 (h ≫ (h' ≫ f)) x
    rw [Category.assoc]
instance instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf (X: Cᵒᵖ): Module ((R ⋙ forget₂ z9 RingCat).obj X) ((presheaf F N).obj X):= inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))
variable {N} in
def postcomp {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') (X : Cᵒᵖ) : naturalFamilies F N X →+ naturalFamilies F N' X where
  toFun φ := ⟨fun Y f =>
    { toFun := fun x => ψ.app Y (φ.1 f x)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by
        rw [(φ.1 f).map_smul]
        exact (ψ.app Y).hom.map_smul r _ }, by
    intro Y Z f g x
    change N'.map g (ψ.app Y (φ.1 f x)) = ψ.app Z (φ.1 (f ≫ g) (F.map g x))
    rw [← naturality_apply, φ.2 f g x]⟩
  map_zero' := by ext Y f x; exact (ψ.app Y).hom.map_zero
  map_add' φ φ' := by ext Y f x; exact (ψ.app Y).hom.map_add _ _
ec979 1 open InternalHom
@[simps! obj] noncomputable def ihomObj : PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) :=
  ofPresheaf (InternalHom.presheaf F N) (by
    intro X X' h r φ
    apply naturalFamilies_ext
    intro Y f x
    change (R.map (h ≫ f) r) • φ.1 (h ≫ f) x = R.map f (R.map h r) • φ.1 (h ≫ f) x
    rw [Functor.map_comp]
    rfl)
@[simp] lemma ihomObj_map_val {X X': Cᵒᵖ} (h: X ⟶ X') (φ: (ihomObj F N).obj X) {Y: Cᵒᵖ} (f: X' ⟶ Y) (x: F.obj Y): ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x:= by sorry
variable {N} in
noncomputable def ihomMap {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') : ihomObj F N ⟶ ihomObj F N' :=
  homMk { app := fun X => AddCommGrpCat.ofHom (postcomp F ψ X)
          naturality := fun {X X'} h => by ext φ; rfl } (by
    intro X r φ
    apply naturalFamilies_ext
    intro Y f x
    exact (ψ.app Y).hom.map_smul _ _)
noncomputable def ihomFunctor : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) where
  obj N := ihomObj F N
  map ψ := ihomMap F ψ
  map_id N := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
  map_comp ψ ψ' := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
ec979 1 section closed variable {C: Type u} [Category.{u} C] {R: Cᵒᵖ ⥤ z9.{u}} (F: z7.{u} (R ⋙ forget₂ _ _)) {G N: z7.{u} (R ⋙ forget₂ _ _)} namespace InternalHom
noncomputable def curryFamily (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      map_add' := fun x x' => by rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← (θ.app Y).hom.map_smul]
        rfl }, by
    intro Y Z f g x
    change N.map g (θ.app Y _) = θ.app Z _
    rw [← naturality_apply]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    change θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map g (G.map f y)) =
      θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map (f ≫ g) y)
    rw [← PresheafOfModules.map_comp_apply]⟩
@[simp] lemma curryFamily_app (θ: F ⊗ G ⟶ N) {X: Cᵒᵖ} (y: G.obj X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y):= by sorry ec979 1 open InternalHom
noncomputable def curry' (θ : F ⊗ G ⟶ N) : G ⟶ ihomObj F N :=
  homMk
    { app := fun X => AddCommGrpCat.ofHom
        { toFun := fun y => curryFamily F θ y
          map_zero' := by
            apply naturalFamilies_ext; intro Y f x
            have h0 : G.map f (0 : G.obj X) = 0 := (G.map f).hom.map_zero
            rw [curryFamily_app, h0, TensorProduct.tmul_zero]
            exact (θ.app Y).hom.map_zero
          map_add' := fun y y' => by
            apply naturalFamilies_ext; intro Y f x
            have h1 : G.map f (y + y') = G.map f y + G.map f y' := (G.map f).hom.map_add _ _
            rw [InternalHom.add_app, curryFamily_app, curryFamily_app, curryFamily_app, h1,
              TensorProduct.tmul_add]
            exact (θ.app Y).hom.map_add _ _ }
      naturality := fun {X X'} h => by
        ext y
        apply naturalFamilies_ext; intro Y f x
        change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (G.map h y)) = θ.app Y (x ⊗ₜ[R.obj Y] G.map (h ≫ f) y)
        rw [PresheafOfModules.map_comp_apply] }
    (by
      intro X r y
      apply naturalFamilies_ext; intro Y f x
      change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (r • y)) = R.map f r • θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      rw [G.map_smul]
      change θ.app Y (x ⊗ₜ[R.obj Y] ((R.map f r : R.obj Y) • G.map f y)) = _
      rw [TensorProduct.tmul_smul]
      exact (θ.app Y).hom.map_smul _ _)
noncomputable def uncurryApp (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) : (F ⊗ G).obj X ⟶ N.obj X :=
  ModuleCat.MonoidalCategory.tensorLift (fun (x : F.obj X) (y : G.obj X) => (κ.app X y).1 (𝟙 X) x)
    (fun x x' y => by simp)
    (fun r x y => by simp)
    (fun x y y' => by
      have h1 : κ.app X (y + y') = κ.app X y + κ.app X y' := (κ.app X).hom.map_add _ _
      simp only [h1]; rfl)
    (fun r x y => by
      have h1 : κ.app X (r • y) = r • κ.app X y := (κ.app X).hom.map_smul _ _
      simp only [h1]
      change R.map (𝟙 X) r • (κ.app X y).1 (𝟙 X) x = _
      rw [R.map_id]
      rfl)
lemma tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := by sorry
lemma uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by sorry
noncomputable def uncurry' (κ : G ⟶ ihomObj F N) : F ⊗ G ⟶ N where
  app X := uncurryApp F κ X
  naturality {X Y} g := ModuleCat.MonoidalCategory.tensor_ext (fun x y => by
    dsimp
    erw [tensorObj_map_tmul' F (G := G) g x y]
    erw [uncurryApp_tmul, uncurryApp_tmul]
    rw [naturality_apply κ g y]
    erw [ihomObj_map_val]
    erw [(κ.app X y).2 (𝟙 X) g x]
    exact congr_app _ (by simp) _)
lemma uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by sorry
lemma uncurry'_curry' (θ: F ⊗ G ⟶ N): uncurry' F (curry' F θ) = θ:= by sorry lemma curry'_uncurry' (κ: G ⟶ ihomObj F N): curry' F (uncurry' F κ) = κ:= by sorry
noncomputable def tensorIhomAdj : tensorLeft F ⊣ ihomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G N =>
        { toFun := curry' F
          invFun := uncurry' F
          left_inv := uncurry'_curry' F
          right_inv := curry'_uncurry' F }
      homEquiv_naturality_left_symm := fun {G G' N} γ κ => by
        ext X : 1
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        change (uncurry' F (γ ≫ κ)).app X (x ⊗ₜ[R.obj X] y) =
          (uncurry' F κ).app X ((F ◁ γ).app X (x ⊗ₜ[R.obj X] y))
        erw [uncurry'_app_tmul, uncurry'_app_tmul]
      homEquiv_naturality_right := fun {G N N'} θ ν => by
        ext X y
        apply naturalFamilies_ext; intro Y f x
        rfl }
noncomputable instance instMonoidalClosed : MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }
ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false au1129 universe u open CategoryTheory MonoidalCategory Limits nu1129 namespace SheafOfModules variable {C: Type u} [Category.{u} C] {J: GrothendieckTopology C} (𝒪: Cᵒᵖ ⥤ z9.{u}) (h𝒪: Presheaf.IsSheaf J (𝒪 ⋙ forget₂ z9 RingCat)) [originalWEquals: J.WEqualsLocallyBijective AddCommGrpCat.{u}] [originalWeakSheafify: HasWeakSheafify J AddCommGrpCat.{u}] abbrev ringSheaf: Sheaf J RingCat.{u}:= ⟨𝒪 ⋙ forget₂ z9 RingCat, h𝒪⟩ abbrev PMod:= z7.{u} (𝒪 ⋙ forget₂ z9 RingCat)
abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev toPMod: z8.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪:= z8.forget (ringSheaf 𝒪 h𝒪) ⋙ z7.restrictScalars (𝟙 (𝒪 ⋙ forget₂ z9 RingCat))
abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
instance instFaithfulRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Faithful:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instFullRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Full:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instIsLocalizationPModRingSheafSheafifyFunctorPresheafW: (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪):= by sorry include h𝒪 in theorem presheafW_isMonoidal: (presheafW J 𝒪).IsMonoidal:= by sorry def sheafifyCounitIso (M: z8.{u} (ringSheaf 𝒪 h𝒪)): (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M:= (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] ru1129 in def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅ (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) := sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))
instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal
instance monoidalClosed: MonoidalClosed (z8.{u} (ringSheaf 𝒪 h𝒪)):= Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪) ec979 1 namespace AlgebraicGeometry variable (X: Scheme.{u}) instance Scheme.PresheafOfModulesOfCommRing.monoidalCategory: MonoidalCategory X.PresheafOfModules:= inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ z9 RingCat))) instance Scheme.Modules.monoidalCategory: MonoidalCategory X.Modules:= inferInstanceAs (MonoidalCategory (z8.{u} (z8.ringSheaf X.sheaf.obj X.ringCatSheaf.property))) instance Scheme.Modules.monoidalClosed: MonoidalClosed X.Modules:= inferInstanceAs (MonoidalClosed (z8.{u} (z8.ringSheaf X.sheaf.obj X.ringCatSheaf.property))) variable {X} abbrev Scheme.Modules.dual (L: X.Modules): X.Modules:= (ihom L).obj (𝟙_ X.Modules) variable (X) in abbrev Scheme.Modules.sheafify: X.PresheafOfModules ⥤ X.Modules:= z8.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property instance instMonoidalPresheafOfModulesModulesSheafify: (Scheme.Modules.sheafify X).Monoidal:= inferInstanceAs (z8.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).Monoidal ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 nu1129 universe u open CategoryTheory MonoidalCategory namespace AlgebraicGeometry.Scheme.Modules variable {X: Scheme.{u}} def tensorPow (L: X.Modules): ℕ → X.Modules | 0 => 𝟙_ X.Modules | n + 1 => tensorPow L n ⊗ L ec979 3 ec979 1 ec979 1 ec979 1 section rc590 eu1129
set_option backward.isDefEq.respectTransparency.types false au1129 ru1129 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false universe v u v₁ u₁ v₂ u₂ open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal namespace PresheafOfModules section restrictScalars variable {C: Type u₁} [Category.{v₁} C] {R S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ R) abbrev ringCatHom: S ⋙ forget₂ z9 RingCat ⟶ R ⋙ forget₂ z9 RingCat:= Functor.whiskerRight φ (forget₂ z9 RingCat) noncomputable abbrev restrictScalarsAt (U: Cᵒᵖ): z11.{u} (R.obj U) ⥤ z11.{u} (S.obj U):= z11.restrictScalars (φ.app U).hom
noncomputable def restrictScalarsε : 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶ (restrictScalars (ringCatHom φ)).obj (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ _))) where
  app U := ε (restrictScalarsAt φ U)
  naturality {U V} i := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : S.obj U) => ?_)
    change ε (restrictScalarsAt φ V) (S.map i s) = R.map i (ε (restrictScalarsAt φ U) s)
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    exact ConcreteCategory.congr_hom (φ.naturality i) s
noncomputable def restrictScalarsμ (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) : (restrictScalars (ringCatHom φ)).obj M ⊗ (restrictScalars (ringCatHom φ)).obj N ⟶ (restrictScalars (ringCatHom φ)).obj (M ⊗ N) where
  app U := μ (restrictScalarsAt φ U) (M.obj U) (N.obj U)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    rfl
noncomputable instance restrictScalars_laxMonoidal : (restrictScalars (ringCatHom φ)).LaxMonoidal where
  ε := restrictScalarsε φ
  μ M N := restrictScalarsμ φ M N
  μ_natural_left f N := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app]
    exact μ_natural_left (restrictScalarsAt φ U) (f.app U) (N.obj U)
  μ_natural_right M f := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app]
    exact μ_natural_right (restrictScalarsAt φ U) (M.obj U) (f.app U)
  associativity M N P := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app,
      PresheafOfModulesOfCommRing.associator_hom_app]
    exact associativity (restrictScalarsAt φ U) (M.obj U) (N.obj U) (P.obj U)
  left_unitality M := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.leftUnitor_hom_app]
    exact left_unitality (restrictScalarsAt φ U) (M.obj U)
  right_unitality M := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.rightUnitor_hom_app]
    exact right_unitality (restrictScalarsAt φ U) (M.obj U)
ec979 1 section pushforward variable {C: Type u₁} [Category.{v₁} C] {D: Type u₂} [Category.{v₂} D] (F: C ⥤ D) {R: Dᵒᵖ ⥤ z9.{u}} {S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ F.op ⋙ R)
noncomputable instance pushforward_laxMonoidal : (pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).LaxMonoidal :=
  inferInstanceAs (pushforward₀OfCommRingCat F R ⋙
    restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).LaxMonoidal
noncomputable instance pullback_oplaxMonoidal [(pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).IsRightAdjoint] :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction (R := R ⋙ forget₂ _ _) (ringCatHom φ)).leftAdjointOplaxMonoidal
ec979 1 ec979 1 namespace PresheafOfModules namespace PullbackMonoidal open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal variable {C D: Type u} [SmallCategory C] [SmallCategory D] [originalProductsC: HasFiniteProducts C] [originalProductsD: HasFiniteProducts D] (F: C ⥤ D) [originalPreservesProducts: PreservesFiniteProducts F] {R: Dᵒᵖ ⥤ z9.{u}} {S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ F.op ⋙ R) local notation "R'" => R ⋙ forget₂ z9 RingCat local notation "S'" => S ⋙ forget₂ z9 RingCat
noncomputable abbrev pb : PresheafOfModules.{u} S' ⥤ PresheafOfModules.{u} R' :=
  pullback (R := R') (ringCatHom φ)
instance isIso_δ (A B: z7.{u} S'): IsIso (δ (pb F φ) A B):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts instance isIso_η: IsIso (η (pb F φ)):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts noncomputable instance pullback_monoidal: (pb F φ).Monoidal:= Functor.Monoidal.ofOplaxMonoidal _ ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 universe u open CategoryTheory MonoidalCategory Limits TopologicalSpace nu1129 namespace AlgebraicGeometry.Scheme.Modules variable {X Y: Scheme.{u}} (f: X ⟶ Y)
instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) := by sorry
instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have htop : (⊤ : Y.Opens) ≤ c.pt := leOfHom (hc.lift
          { pt := ⊤, π := Discrete.natTrans (fun j => j.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map f.base).map (homOfLE htop))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩
instance preservesFiniteProducts_opensMap: PreservesFiniteProducts (Opens.map f.base):= Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _
abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base)
    (R := X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf) (S := Y.sheaf.obj) f.c).Monoidal
variable (Y) in instance sheafify_isLocalization': (Modules.sheafify Y).IsLocalization (z8.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj):= by sorry instance instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback: Localization.Lifting (Modules.sheafify Y) (z8.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f):= ⟨z8.sheafificationCompPullback f.toRingCatSheafHom⟩
instance pullback_monoidal : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
def pullbackTensorObjIso (L M: Y.Modules): (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M:= (Functor.Monoidal.μIso (Modules.pullback f) L M).symm def pullbackTensorUnitObjIso: (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules:= (Functor.Monoidal.εIso (Modules.pullback f)).symm ec979 3 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 universe u open CategoryTheory MonoidalCategory Opposite nu1129 namespace AlgebraicGeometry.Scheme.Modules variable {X: Scheme.{u}} def tensorPowAdd (L: X.Modules) (m: ℕ): (n: ℕ) → (L.tensorPow m ⊗ L.tensorPow n ≅ L.tensorPow (m + n)) | 0 => ρ_ (L.tensorPow m) | n + 1 => (α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫ whiskerRightIso (tensorPowAdd L m n) L def tensorPowMapIso {L₁ L₂: X.Modules} (e: L₁ ≅ L₂): (n: ℕ) → (L₁.tensorPow n ≅ L₂.tensorPow n) | 0 => Iso.refl _ | n + 1 => tensorIso (tensorPowMapIso e n) e def pullbackTensorPowIso {Y: Scheme.{u}} (c: X ⟶ Y) (L: Y.Modules): (n: ℕ) → ((Modules.pullback c).obj (L.tensorPow n) ≅ ((Modules.pullback c).obj L).tensorPow n) | 0 => pullbackTensorUnitObjIso c | n + 1 => pullbackTensorObjIso c (L.tensorPow n) L ≪≫ whiskerRightIso (pullbackTensorPowIso c L n) ((Modules.pullback c).obj L) ec979 3 ec979 1 ec979 1 ec979 1 section rc590 eu1129 ru1129 au1129 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open NeronModelInfra
nu1129 namespace AlgebraicGeometry structure Scheme.Modules.IsInvertible {X: Scheme.{u}} (M: X.Modules): Prop where (exists_trivialization: ∀ x: X, ∃ (U: X.Opens), x ∈ U ∧ z29 ((Scheme.Modules.pullback U.ι).obj M ≅ z8.unit U.toScheme.ringCatSheaf)) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 universe u open CategoryTheory TopologicalSpace Opposite nu1129 namespace AlgebraicGeometry.Scheme.Modules variable {X Y: Scheme.{u}} (φ: X ⟶ Y) section variable {L: Y.Modules} {U: Y.Opens} def pullbackLocalSection (s: Γ(L, U)): Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U):= ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s ec979 1 ec979 3 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 nu1129 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory NeronModelInfra open scoped CategoryTheory.MonObj namespace GoodReductionJacobian
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
namespace RelativeGroupLaw ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 namespace GoodReductionJacobian namespace RelativeGroupLaw ec979 1 ec979 1 namespace AlgebraicGeometry namespace Scheme.TwoAffineOpenCover ec979 2 ec979 1 section rc590 eu1129 au1129 universe u open CategoryTheory CategoryTheory.Limits MonoidalCategory nu1129 namespace AlgebraicGeometry variable {X Y: Scheme.{u}} abbrev Scheme.Hom.unitToPushforwardUnit (f: X ⟶ Y): z8.unit Y.ringCatSheaf ⟶ (z8.pushforward f.toRingCatSheafHom).obj (z8.unit X.ringCatSheaf):= z8.unitToPushforwardObjUnit f.toRingCatSheafHom namespace Scheme.IdealSheafData def module (I: X.IdealSheafData): X.Modules:= (kernel I.subschemeι.unitToPushforwardUnit: z8 X.ringCatSheaf) ec979 2 ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite universe u namespace AlgebraicGeometry.Scheme.IdealSheafData variable {X: Scheme.{u}} def IsInvertible (I: X.IdealSheafData): Prop:= ∀ x: X, ∃ (U: X.affineOpens) (f: Γ(X, U)), x ∈ X.basicOpen f ∧ ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span {g} ec979 3 ec979 1 ec979 1 section rc590 eu1129 au1129 universe u open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module {X: Scheme.{u}} {I: X.IdealSheafData} (hI: I.IsInvertible): Scheme.Modules.IsInvertible I.module:= by sorry
ec979 1 ec979 1 section rc590 eu1129 au1129 universe u open CategoryTheory AlgebraicGeometry theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pow {X: Scheme.{u}} {I: X.IdealSheafData} (hI: I.IsInvertible) (n: ℕ): (I ^ n).IsInvertible:= by sorry ec979 1 ec979 1 namespace AlgebraicGeometry namespace Scheme.OrderedAffineCover ec979 2 namespace OModulePresheaf ec979 1 ec979 1 namespace AlgebraicGeometry namespace Scheme.OrderedAffineCover ec979 2 namespace OModulePresheaf namespace Hom ec979 1 namespace AffHom ec979 1 ec979 1 ec979 1 section rc590 eu1129 ru1129 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false au1129 universe u open CategoryTheory CategoryTheory.Limits nu1129 namespace AlgebraicGeometry.Scheme.IdealSheafData variable {X X': Scheme.{u}} (f: X' ⟶ X) (I: X.IdealSheafData) open Opposite lemma kernelι_unitToPushforwardUnit_map_eq_zero: (kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit) ≫ (z8.pushforward f.toRingCatSheafHom).map (I.comap f).subschemeι.unitToPushforwardUnit = 0:= by sorry def moduleToPushforwardComapModule: (I.module: z8 X.ringCatSheaf) ⟶ (z8.pushforward f.toRingCatSheafHom).obj (I.comap f).module:= kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫ (PreservesKernel.iso (z8.pushforward f.toRingCatSheafHom) (I.comap f).subschemeι.unitToPushforwardUnit).inv
def pullbackModuleComparison: (Scheme.Modules.pullback f).obj I.module ⟶ (I.comap f).module:= ((z8.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _).symm (I.moduleToPushforwardComapModule f) ec979 3 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison {X X': Scheme.{u}} (f: X' ⟶ X) {I: X.IdealSheafData} (hI: I.IsInvertible) (hI': (I.comap f).IsInvertible): IsIso (I.pullbackModuleComparison f):= by sorry ec979 1 ec979 1 namespace AlgebraicGeometry.Scheme.Hom ec979 3 namespace WeierstrassCurve.DrinfeldGlobal ec979 2 namespace ArithmeticThetaNodeCharts ec979 1 namespace ArithmeticThetaNodeCharts ec979 1 namespace ArithmeticThetaScaledTateBridgeR0046 ec979 1 namespace ArithmeticThetaScaledTateCompletionExtensionR0048 ec979 1 namespace ArithmeticThetaScaledTateCompletionExtensionR0048 ec979 1 namespace ArithmeticThetaScaledAnnularR0050 ec979 1 namespace ArithmeticThetaAnnularTorsionPrereqR0053 ec979 1 namespace ArithmeticThetaIndexedOverlapsR0058 ec979 1 namespace ArithmeticThetaIndexedOverlapsR0058 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaPolygonCohomologyR0131 ec979 1 section rc590 eu1129 au1129 ru1129
nu1129 universe u namespace ArithmeticThetaPolygonCartierR0133 open CategoryTheory AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaPolygonCohomologyR0131 variable (k: Type u) [z1 k] [z2 k] 
set_option hygiene false
set_option quotPrecheck false
local notation "Hu9" => (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} Y)))
local notation "Hu0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu9)
local notation "Hu10" => (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X)))
local notation "Hu1" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu10)
local notation "Hu5" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0))
local notation "Hu2" => (@Preorder.smallCategory.{u_1} Hu5 (@PartialOrder.toPreorder.{u_1} Hu5 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0))))
local notation "Hu6" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1))
local notation "Hu3" => (@Preorder.smallCategory.{u_1} Hu6 (@PartialOrder.toPreorder.{u_1} Hu6 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1))))
local notation "Hu4" => (@TopologicalSpace.Opens.map.{u_1} Hu1 Hu0 (@AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu10 Hu9 (@AlgebraicGeometry.LocallyRingedSpace.Hom.toHom.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X) (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} Y) (@AlgebraicGeometry.Scheme.Hom.toLRSHom'.{u_1} X Y f))))
local notation "Hu7" => (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0))
local notation "Hu8" => (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1))
local notation "Hu11" => (@CategoryTheory.ReflQuiver.toQuiver.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} (@CategoryTheory.catToReflQuiver.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} AlgebraicGeometry.Scheme.instCategory.{u_1}))
set_option quotPrecheck true
set_option hygiene true
theorem _root_.ArithmeticThetaPolygonCartierR0133.unitPullback._proof_1.{u_1} : ∀ {X Y : AlgebraicGeometry.Scheme.{u_1}} (f : @Quiver.Hom.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} Hu11 X Y), @CategoryTheory.Functor.IsContinuous.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu6 Hu3 Hu4 Hu7 Hu8 := by sorry
theorem _root_.ArithmeticThetaPolygonCartierR0133.unitPullback._proof_2.{u_1} : ∀ {X Y : AlgebraicGeometry.Scheme.{u_1}} (f : @Quiver.Hom.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} Hu11 X Y), @CategoryTheory.Functor.IsRightAdjoint.{u_1, u_1, u_1 + 1, u_1 + 1} (@SheafOfModules.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu7 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y)) (@SheafOfModules.instCategory.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu7 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y)) (@SheafOfModules.{u_1, u_1, u_1, u_1} Hu6 Hu3 Hu8 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X)) (@SheafOfModules.instCategory.{u_1, u_1, u_1, u_1} Hu6 Hu3 Hu8 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X)) (@SheafOfModules.pushforward.{u_1, u_1, u_1, u_1, u_1, u_1} Hu5 Hu2 Hu6 Hu3 Hu7 Hu8 Hu4 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y) (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X) (@ArithmeticThetaPolygonCartierR0133.unitPullback._proof_1.{u_1} X Y f) (@AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom.{u_1} X Y f)) := by sorry
run_cmd do
 for i in [1:3] do
  let n := ("ArithmeticThetaPolygonCartierR0133.unitPullback._proof_" ++ toString i).toName
  let ci ← Lean.getConstInfo n
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
def unitPullback {X Y: Scheme.{u}} (f: X ⟶ Y): (Scheme.Modules.pullback f).obj (z8.unit Y.ringCatSheaf: Y.Modules) ⟶ (z8.unit X.ringCatSheaf: X.Modules):= z8.pullbackObjUnitToUnit f.toRingCatSheafHom ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaPolygonCartierR0133 namespace GlobalCartierIdealLineR0133 ec979 1 ec979 1 namespace ArithmeticThetaPolygonCartierR0133 namespace CanonicalCartierLineReductionR0133 ec979 1 ec979 1 namespace ArithmeticThetaProjectiveEffectivityR0135 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136 namespace AlgebraizedMarkedIdealSpecializationR0136 ec979 1 ec979 1 namespace AlgebraicGeometry namespace OModulePresheaf ec979 1 ec979 1 section rc590 eu1129 au1129 set_option linter.style.haveILetI false set_option maxHeartbeats 4000000 set_option synthInstance.maxHeartbeats 400000 ru1129 set_option backward.isDefEq.respectTransparency.types false namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion namespace HomCompleteAux namespace Sys ec979 1 namespace Sys ec979 1 ec979 1 ec979 3 nu1129 universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaPolygonCartierR0133 lemma comap_power {X Y: Scheme.{u}} (f: X ⟶ Y) (I: Y.IdealSheafData) (d: ℕ): (I ^ d).comap f = (I.comap f) ^ d:= by sorry variable (k: Type u) [z1 k] [z2 k]
def idealPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) (J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I.comap f = J) : (Scheme.Modules.pullback f).obj I.module ≅ J.module := by
  have hJ' : (I.comap f).IsInvertible := h ▸ hJ
  letI := hI.isIso_pullbackModuleComparison f hJ'
  exact asIso (I.pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module h)
open CanonicalCartierLineReductionR0133 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaScaledAnnularR0050 ec979 1 namespace ArithmeticThetaCorrectedGammaR0061 ec979 1 namespace ArithmeticThetaTateSeries ec979 1 namespace ArithmeticThetaSchrodingerR0119 ec979 1 namespace ArithmeticThetaAnnularThetaR0128 ec979 1 namespace ArithmeticThetaCorrectedGammaR0061 ec979 1 namespace ArithmeticThetaIdentitySectionsR0138 ec979 1 namespace ArithmeticThetaIdentitySectionsR0138 namespace AlgebraizedThetaSectionsR0138 ec979 1 ec979 1 namespace ArithmeticThetaGenericEvaluationR0140 ec979 1 section rc590 eu1129 set_option maxHeartbeats 1600000 set_option linter.style.haveILetI false au1129 ru1129 nu1129 universe u namespace ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open scoped TensorProduct open MonoidalCategory open ArithmeticThetaPolygonCartierR0133 (unitPullback)
def dualComparison {X Y: Scheme.{u}} (c: X ⟶ Y) (L: Y.Modules): (Scheme.Modules.pullback c).obj (Scheme.Modules.dual L) ⟶ Scheme.Modules.dual ((Scheme.Modules.pullback c).obj L):= MonoidalClosed.curry ((Scheme.Modules.pullbackTensorObjIso c L (Scheme.Modules.dual L)).inv ≫ (Scheme.Modules.pullback c).map ((ihom.ev L).app (𝟙_ Y.Modules)) ≫ unitPullback c) lemma dualComparison_isIso {X Y: Scheme.{u}} (c: X ⟶ Y) (L: Y.Modules) (hL: Scheme.Modules.IsInvertible L): IsIso (dualComparison c L):= by sorry ec979 2 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaModelSymmetriesR0137 ec979 1 namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaCubicModelR0144 ec979 1 namespace ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144 ec979 2 namespace WeierstrassCurve.DrinfeldGlobal ec979 2 namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145 namespace ProjectiveCubicChart ec979 1 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145 namespace GlobalNormalizedDifferential ec979 1 ec979 1 namespace ArithmeticThetaGeneralEllipticKatoR0168 namespace BaseChange ec979 1 ec979 1 namespace ArithmeticThetaRelativeKatoR0169 ec979 1 namespace GoodReductionJacobian namespace RelativeGroupLaw ec979 1 ec979 1 namespace ArithmeticThetaRelativeDiscriminantR0171 ec979 1 section rc590 eu1129 au1129 ru1129 set_option maxHeartbeats 800000 set_option linter.style.haveILetI false
nu1129 universe u open AlgebraicGeometry CategoryTheory Opposite open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower ArithmeticThetaPullback namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull section PullbackComposition variable {X Y Z: Scheme.{u}}
def pullbackEqIso {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
ec979 1 def squarePullbackIso {A B X Y: Scheme.{u}} (a: A ⟶ B) (s: B ⟶ Y) (t: A ⟶ X) (b: X ⟶ Y) (h: a ≫ s = t ≫ b) (M: Y.Modules): (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback s).obj M) ≅ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M):= (Scheme.Modules.pullbackComp a s).app M ≪≫ pullbackEqIso h M ≪≫ ((Scheme.Modules.pullbackComp t b).app M).symm ec979 2 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal ec979 3 section rc590 eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaLocalWeierstrassR0203 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra open scoped TensorProduct abbrev Base (R: Type u) [z0 R]:= Spec (z9.of R)
structure SchemeLaw {S X: Scheme.{u}} (p: X ⟶ S) where (mul: ∀ {T: Scheme.{u}} (t: T ⟶ S), SchemeHomOver t p → SchemeHomOver t p → SchemeHomOver t p) (one: ∀ {T: Scheme.{u}} (t: T ⟶ S), SchemeHomOver t p) (inv: ∀ {T: Scheme.{u}} (t: T ⟶ S), SchemeHomOver t p → SchemeHomOver t p) (mul_assoc: ∀ {T: Scheme.{u}} (t: T ⟶ S) (x y z: SchemeHomOver t p), mul t (mul t x y) z = mul t x (mul t y z)) (one_mul: ∀ {T: Scheme.{u}} (t: T ⟶ S) (x: SchemeHomOver t p), mul t (one t) x = x) (mul_one: ∀ {T: Scheme.{u}} (t: T ⟶ S) (x: SchemeHomOver t p), mul t x (one t) = x) (inv_mul_cancel: ∀ {T: Scheme.{u}} (t: T ⟶ S) (x: SchemeHomOver t p), mul t (inv t x) x = one t) (mul_comm: ∀ {T: Scheme.{u}} (t: T ⟶ S) (x y: SchemeHomOver t p), mul t x y = mul t y x) (mul_natural: ∀ {T T': Scheme.{u}} (t: T ⟶ S) (t': T' ⟶ S) (ψ: T' ⟶ T) (hψ: ψ ≫ t = t') (x y: SchemeHomOver t p), GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t x y) = mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) (GoodReductionJacobian.schemeHomOverComp ψ hψ y)) structure Family (S: Scheme.{u}) where (curve: Scheme.{u}) (p: curve ⟶ S) (law: SchemeLaw p) (proper: IsProper p) (dimension: SmoothOfRelativeDimension 1 p) (connected: GeometricallyConnected p) def Family.zero {S: Scheme.{u}} (E: Family S): S ⟶ E.curve:= (E.law.one (𝟙 S)).val ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaFullLevelCoverR0175 ec979 1 namespace ArithmeticThetaLegendreAtlasR0176 ec979 1 namespace ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent ec979 2
namespace ArithmeticThetaLegendreComparisonR0177 ec979 1 namespace ArithmeticThetaCompatibleLevelR0178 ec979 1 namespace ArithmeticThetaSchemeLevelR0204 ec979 1 namespace ArithmeticThetaSchemeLevelR0204 namespace GlobalSchemeClassifier ec979 1 ec979 1 namespace ArithmeticThetaSchemeLevelR0204 namespace SchemeFullLevelUniversal ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaSchemeHodgeR0205 open CategoryTheory AlgebraicGeometry open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange abbrev Cotangent {S: Scheme.{u}} (E: Family S): S.Modules:= (Scheme.Modules.pullback E.zero).obj E.zero.ker.module def cotangentComparison {S T: Scheme.{u}} (E: Family S) (F: Family T) (b: T ⟶ S) (f: F.curve ⟶ E.curve) (hz: F.zero ≫ f = b ≫ E.zero) (i: (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module): (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F:= squarePullbackIso b E.zero F.zero f hz.symm E.zero.ker.module ≪≫ (Scheme.Modules.pullback F.zero).mapIso i ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaSchemeHodgeR0205 namespace AffineConormalHodgeNaturality ec979 1 ec979 1 namespace ArithmeticThetaLevelCompactificationR0179 ec979 1 namespace ArithmeticThetaOpenHodgeR0180 ec979 1 namespace ArithmeticThetaTateCuspsR0181 ec979 1 namespace ArithmeticThetaBoundaryHodgeR0182 ec979 1 section rc590
eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaSchemeHodgeR0205 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaLocalWeierstrassR0203 namespace CartesianIdentityIdeal lemma ideal_comap {S T: Scheme.{u}} (E: Family S) (F: Family T) (b: T ⟶ S) (f: F.curve ⟶ E.curve) (hc: IsPullback f F.p E.p b) (hz: F.zero ≫ f = b ≫ E.zero): E.zero.ker.comap f = F.zero.ker:= by sorry lemma zero_ideal_invertible {S: Scheme.{u}} (E: Family S): E.zero.ker.IsInvertible:= by sorry ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182 ec979 2 namespace ArithmeticThetaComponentDegreeR0184 ec979 1 namespace ArithmeticThetaComponentDegreeR0184 namespace GeometricComponentCuspBoundR0184 ec979 1 ec979 1 namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141 ec979 2 namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaSharpCoverR0194 ec979 1 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso namespace AlgebraicGeometry namespace Scheme namespace Modules namespace P2K2 ec979 4 ec979 1 ec979 1 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 namespace ArithmeticFamily ec979 1 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4
namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta namespace MarkedModel ec979 1 ec979 4 namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244 namespace SchemeDiscriminantExistence ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaSchemeThetaMarkingR0259 open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory open AlgebraicGeometry NeronModelInfra open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 open scoped TensorProduct variable {S: Scheme.{u}} (E: Family S) def thetaLine (m: ℕ): E.curve.Modules:= tensorObj (Scheme.Modules.dual ((E.zero.ker ^ m).module)) ((Scheme.Modules.pullback E.p).obj ((ArithmeticThetaSchemeHodgeR0205.Cotangent E).tensorPow m)) abbrev Lift (m: ℕ) (f: E.curve ⟶ E.curve):= (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine E m
ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 set_option linter.style.haveILetI false ru1129 set_option maxHeartbeats 1600000 set_option maxRecDepth 4096 nu1129 universe u v w namespace ArithmeticThetaSchemeThetaMarkingR0259 namespace SchemeThetaSectionCohomology open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory open AlgebraicGeometry NeronModelInfra open ArithmeticThetaLocalWeierstrassR0203 open ArithmeticThetaSchemeHodgeR0205 open scoped TensorProduct open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
def originPowerComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) : (Scheme.Modules.pullback f).obj (Scheme.Modules.dual (E.zero.ker ^ m).module) ≅ Scheme.Modules.dual (F.zero.ker ^ m).module := by
  let e := idealPullbackIso f (E.zero.ker ^ m) (F.zero.ker ^ m)
    ((CartesianIdentityIdeal.zero_ideal_invertible E).pow m)
    ((CartesianIdentityIdeal.zero_ideal_invertible F).pow m)
    (by rw [comap_power, CartesianIdentityIdeal.ideal_comap E F b f hc hz])
  letI := dualComparison_isIso f (E.zero.ker ^ m).module
    ((CartesianIdentityIdeal.zero_ideal_invertible E).pow m).isInvertible_module
  exact asIso (dualComparison f _) ≪≫
    ((MonoidalClosed.internalHom (C := F.curve.Modules)).mapIso e.symm.op).app
      (𝟙_ F.curve.Modules)
def thetaComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) : (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine F m := by
  let i := idealPullbackIso f E.zero.ker F.zero.ker
    (CartesianIdentityIdeal.zero_ideal_invertible E)
    (CartesianIdentityIdeal.zero_ideal_invertible F)
    (CartesianIdentityIdeal.ideal_comap E F b f hc hz)
  let eH := cotangentComparison E F b f hz i
  let eW := Scheme.Modules.pullbackTensorPowIso b (Cotangent E) m ≪≫
    Scheme.Modules.tensorPowMapIso eH m
  exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    (originPowerComparison E F b f hc hz m ⊗ᵢ
      ((Scheme.Modules.pullbackComp f E.p).app _ ≪≫
        (Scheme.Modules.pullbackCongr hc.w).app _ ≪≫
        ((Scheme.Modules.pullbackComp F.p b).app _).symm ≪≫
        (Scheme.Modules.pullback F.p).mapIso eW))
ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaSchemeSchrodingerR0261 open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory open AlgebraicGeometry NeronModelInfra open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 open ArithmeticThetaSchemeThetaMarkingR0259 open scoped TensorProduct variable {S: Scheme.{u}} (E: Family S) abbrev V (m: ℕ): S.Modules:= (Scheme.Modules.pushforward E.p).obj (thetaLine E m) def IsAction (m: ℕ) (f: E.curve ⟶ E.curve) (α: Lift E m f) (A: End (V E m)): Prop:= ∃ h: f ≫ E.p = E.p, ∀ (U: S.Opens) (w: Γ(thetaLine E m, E.p ⁻¹ᵁ U)), α.hom.app (f ⁻¹ᵁ (E.p ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection f w) = (thetaLine E m).presheaf.map (eqToHom (congrArg (fun g: E.curve ⟶ S => g ⁻¹ᵁ U) h)).op (A.app U w) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1129 au1129 ru1129 nu1129 universe u namespace ArithmeticThetaSchemeThetaNaturalityR0262 open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry NeronModelInfra open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
variable {S T: Scheme.{u}} (E: Family S) (F: Family T) (b: T ⟶ S) (f: F.curve ⟶ E.curve) (hc: IsPullback f F.p E.p b) (hz: F.zero ≫ f = b ≫ E.zero) abbrev thetaComparison (m: ℕ):= SchemeThetaSectionCohomology.thetaComparison E F b f hc hz m def transportedLift (m: ℕ) (g: E.curve ⟶ E.curve) (g': F.curve ⟶ F.curve) (h: g' ≫ f = f ≫ g) (α: Lift E m g): Lift F m g':= (Scheme.Modules.pullback g').mapIso (thetaComparison E F b f hc hz m).symm ≪≫ (Scheme.Modules.pullbackComp g' f).app _ ≪≫ (Scheme.Modules.pullbackCongr h).app _ ≪≫ ((Scheme.Modules.pullbackComp f g).app _).symm ≪≫ (Scheme.Modules.pullback f).mapIso α ≪≫ thetaComparison E F b f hc hz m def LiftCorresponds (m: ℕ) (g: E.curve ⟶ E.curve) (g': F.curve ⟶ F.curve) (α: Lift E m g) (α': Lift F m g'): Prop:= ∃ h: g' ≫ f = f ≫ g, α' = transportedLift E F b f hc hz m g g' h α def pushforwardMap (m: ℕ): (Scheme.Modules.pullback b).obj (V E m) ⟶ V F m:= (Scheme.Modules.pullbackPushforwardAdjunction F.p).homEquiv _ _ (((Scheme.Modules.pullbackComp F.p b).app (V E m)).hom ≫ ((Scheme.Modules.pullbackCongr hc.w.symm).app (V E m)).hom ≫ ((Scheme.Modules.pullbackComp f E.p).app (V E m)).inv ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m)) ≫ (thetaComparison E F b f hc hz m).hom) ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaTateSchemeMarkingR0263 ec979 1 namespace ArithmeticThetaInvariantRatiosR0265 namespace Arithmetic ec979 1 ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266
namespace Arithmetic ec979 1 ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1 eu1129 nu1129 universe u namespace ArithmeticThetaSchemeThetaNaturalityR0262 open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeSchrodingerR0261
variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
 (b : T ⟶ S) (f : F.curve ⟶ E.curve)
 (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
def Intertwines (m : ℕ) (A : End (V E m)) (A' : End (V F m)) : Prop :=
  (Scheme.Modules.pullback b).map A ≫ pushforwardMap E F b f hc hz m =
    pushforwardMap E F b f hc hz m ≫ A'
end ArithmeticThetaSchemeThetaNaturalityR0262 end eu1129 nu1129 namespace PalomarProjective969 open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203 open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
def Intertwining : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (E : ArithmeticThetaLocalWeierstrassR0203.Family.{0} S) (T : AlgebraicGeometry.Scheme.{0})
  (F : ArithmeticThetaLocalWeierstrassR0203.Family.{0} T) (b : Quiver.Hom.{0, 0 + 1} T S)
  (f :
    Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E))
  (hc :
    CategoryTheory.IsPullback.{0, 0 + 1} f (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} E) b)
  (hz :
    Eq.{0 + 1}
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} F) f)
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} b (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} E)))
  (m : ℕ),
  LT.lt.{0} 0 m →
    CategoryTheory.IsIso.{0, 0 + 1} (ArithmeticThetaSchemeThetaNaturalityR0262.pushforwardMap.{0} E F b f hc hz m) ∧
      ∀
        (g :
          Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E)
            (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E))
        (g' :
          Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
            (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F))
        (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} E m g)
        (α' : ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} F m g')
        (A : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} E m))
        (A' : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} F m)),
        ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds.{0} E F b f hc hz m g g' α α' →
          ArithmeticThetaSchemeSchrodingerR0261.IsAction.{0} E m g α A →
            ArithmeticThetaSchemeSchrodingerR0261.IsAction.{0} F m g' α' A' →
              ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines.{0} E F b f hc hz m A A'
theorem intertwining : Intertwining := by sorry end PalomarProjective969 end
