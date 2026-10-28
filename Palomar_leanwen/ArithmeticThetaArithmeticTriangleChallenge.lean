module
public import Mathlib
import all Lean.Meta.Match.Match
elab "ec877" n:num:command=> do
  for _ in [:n.getNat] do
    let ss ← Lean.Elab.Command.getScopes
    let h := ss.head!.header
    if h.isEmpty then
      Lean.Elab.Command.elabCommand (← `(end))
    else
      Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent (Lean.Name.str Lean.Name.anonymous h))))
@[expose] public section
open AlgebraicGeometry.Scheme.Modules renaming pullback → zPB693, pullbackComp → zPC693
open Ideal.Quotient renaming mk → zQM693
set_option autoImplicit false
open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z7, SheafOfModules → z8, CommRingCat → z9, LinearMap → z10, ModuleCat → z11, AddMonoidHom → z12, RingHom → z13, IsDomain → z14, IsIntegrallyClosed → z15, IsNoetherianRing → z16, IsAlgClosed → z17, Finsupp → z18, SetLike → z19, Submodule → z20, FractionRing → z21, HomogeneousIdeal → z22, HomogeneousLocalization → z23, IsUnit → z24, IsScalarTower → z25, AddSubgroupClass → z26, AddSubmonoidClass → z27, Algebra → z28, Nonempty → z29
open AlgebraicGeometry renaming Scheme → zS
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.privateInPublic true
macro "rc590":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {})
set_option hygiene false
set_option quotPrecheck false
local notation "CT586x5" => (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
local notation "CT586x15(" R "," inst ")" => (@CommSemiring.toSemiring.{u_1} R (@z0.toCommSemiring.{u_1} R inst))
local notation "CT586x24" => (@z18.{0, 0} CT586x5 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
local notation "CT586x41(" R "," inst ")" => (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R CT586x24 CT586x15(R, inst) CT586x15(R, inst) (@Semiring.toModule.{u_1} R CT586x15(R, inst)))
local notation "CT586x13(" R "," inst ")" => (@z6.{0, u_1} CT586x5 R (@z0.toCommSemiring.{u_1} R inst))
local notation "CT586x7(" R "," W "," inst ")" => (@z22.toIdeal.{0, u_1, u_1} Nat (@z20.{u_1, u_1} R CT586x13(R, inst) CT586x15(R, inst) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R CT586x24 CT586x15(R, inst)) CT586x41(R, inst)) CT586x13(R, inst) (@AddMonoidAlgebra.semiring.{u_1, 0} R CT586x24 CT586x15(R, inst) (@z18.instAddMonoid.{0, 0} CT586x5 Nat Nat.instAddMonoid)) (@z20.setLike.{u_1, u_1} R CT586x13(R, inst) CT586x15(R, inst) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R CT586x24 CT586x15(R, inst)) CT586x41(R, inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1.{u_1} R inst) (@z6.homogeneousSubmodule.{0, u_1} CT586x5 R (@z0.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@z6.gradedAlgebra.{0, u_1} CT586x5 R (@z0.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@z3.toProjective.{u_1} R W)))
local notation "CT586x10(" R "," inst ")" => (@Ring.toSemiring.{u_1} CT586x13(R, inst) (@AddMonoidAlgebra.ring.{u_1, 0} R CT586x24 (@z0.toRing.{u_1} R inst) (@z18.instAddMonoid.{0, 0} CT586x5 Nat Nat.instAddMonoid)))
local notation "CT586x28(" R "," inst ")" => (@OfNat.ofNat.{u_1} R (nat_lit 0) (@Zero.toOfNat0.{u_1} R (@MulZeroClass.toZero.{u_1} R (@instMulZeroClassOfSemiring.{u_1} R CT586x15(R, inst)))))
local notation "CT586x18" => (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
local notation "CT586x33(" inst "," k ")" => (@ArithmeticThetaScaledTateBridgeR0046.PolynomialChart.{u_1} k inst)
local notation "CT586x47" => (@z18.{0, 0} (Fin CT586x18) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
local notation "CT586x23(" inst "," k ")" => (@CommSemiring.toSemiring.{u_1} CT586x33(inst, k) (@z0.toCommSemiring.{u_1} CT586x33(inst, k) (@AddMonoidAlgebra.commRing.{u_1, 0} (ArithmeticThetaScaledTateBridgeR0046.Base.{u_1} k) CT586x47 (@MvPowerSeries.instCommRing.{0, u_1} Unit k (@z1.toCommRing.{u_1} k inst)) (@z18.instAddCommMonoid.{0, 0} (Fin CT586x18) Nat Nat.instAddCommMonoid))))
local notation "CT586x36" => (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
set_option quotPrecheck true
set_option hygiene true
set_option hygiene false
macro "cc0" : command => `(set_option backward.isDefEq.respectTransparency false)
macro "cc1" : command => `(set_option autoImplicit false)
macro "cc2" : command => `(@[expose] public section)
macro "cc3" : command => `(noncomputable section)
macro "cc4" : command => `(open CategoryTheory AlgebraicGeometry)
macro "cc5" : command => `(set_option maxHeartbeats 1600000)
macro "cc6" : command => `(open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra)
macro "cc7" : command => `(set_option backward.isDefEq.respectTransparency.instanceSearchTypes false)
macro "cc8" : command => `(set_option maxRecDepth 4096)
macro "cc9" : command => `(open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182)
macro "cc10" : command => `(open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171)
macro "cc11" : command => `(set_option backward.isDefEq.respectTransparency.types false)
macro "cc12" : command => `(open CategoryTheory CategoryTheory.Limits AlgebraicGeometry)
macro "cc13" : command => `(open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading)
macro "cc14" : command => `(open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204)
macro "cc15" : command => `(open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections)
macro "cc16" : command => `(set_option linter.unusedSimpArgs false)
macro "cc17" : command => `(open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176)
macro "cc18" : command => `(open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196)
macro "cc19" : command => `(open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange)
macro "cc20" : command => `(open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181)
macro "cc21" : command => `(open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183)
macro "cc22" : command => `(open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower)
macro "cc23" : command => `(open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192)
macro "cc24" : command => `(open scoped TensorProduct)
macro "cc25" : command => `(set_option linter.style.haveILetI false)
macro "cc26" : command => `(open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization)
macro "cc27" : command => `(open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187)
macro "cc28" : command => `(open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime)
macro "cc29" : command => `(open AlgebraicGeometry CategoryTheory Opposite)
macro "cc30" : command => `(open ArithmeticThetaInfinitesimalPolygonR0129)
macro "cc31" : command => `(open ArithmeticThetaLocalWeierstrassR0203)
macro "cc32" : command => `(open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback)
macro "cc33" : command => `(open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170)
macro "cc34" : command => `(open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192)
macro "cc35" : command => `(open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181)
macro "cc36" : command => `(open ArithmeticThetaProjectiveEffectivityR0135)
macro "cc37" : command => `(open ArithmeticThetaAlgebraizedMarkedLineR0136)
macro "cc38" : command => `(open ArithmeticThetaAlgebraicCoordinatesR0143)
macro "cc39" : command => `(open ArithmeticThetaRelativeDiscriminantR0171)
macro "cc40" : command => `(open ArithmeticThetaSharpKernelR0195 ArithmeticThetaTateCuspsR0181)
macro "cc41" : command => `(open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections)
macro "cc42" : command => `(open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace)
macro "cc43" : command => `(open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory)
macro "cc44" : command => `(open ArithmeticThetaGenericEvaluationR0140)
macro "cc45" : command => `(open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower)
macro "cc46" : command => `(set_option maxHeartbeats 800000)
macro "cc47" : command => `(open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison)
macro "cc48" : command => `(open ArithmeticThetaNormalizedSections ArithmeticThetaPullback)
macro "cc49" : command => `(open ArithmeticThetaIdentitySectionsR0138)
macro "cc50" : command => `(open AlgebraicGeometry CategoryTheory CategoryTheory.Limits)
macro "cc51" : command => `(open MvPolynomial WeierstrassCurve HomogeneousLocalization)
macro "cc52" : command => `(open ArithmeticThetaCompactUnaryR0183)
macro "cc53" : command => `(open CategoryTheory AlgebraicGeometry NeronModelInfra)
macro "cc54" : command => `(open ArithmeticThetaCubicModelR0144)
macro "cc55" : command => `(open ArithmeticThetaMetaplecticComparisonR0206)
macro "cc56" : command => `(set_option linter.unusedSectionVars false)
macro "cc57" : command => `(set_option backward.privateInPublic true)
macro "cc58" : command => `(open ArithmeticThetaPolygonCartierR0133)
set_option hygiene true
namespace ArithmeticThetaAlgebraicCoordinatesR0143
ec877 1
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
ec877 1
namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
ec877 2
namespace ArithmeticThetaGenericEvaluationR0140
ec877 1
namespace ArithmeticThetaGlobalFourTorsionR0190
ec877 1
namespace ArithmeticThetaGlobalization
ec877 1
namespace ArithmeticThetaIdentitySectionsR0138
ec877 1
namespace ArithmeticThetaInfinitesimalPolygonR0129
ec877 1
namespace ArithmeticThetaIsogenyHalfLinesR0193
ec877 1
namespace ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196
ec877 2
namespace ArithmeticThetaPolygonCartierR0133
ec877 1
namespace ArithmeticThetaPolygonCohomologyR0131
ec877 1
namespace ArithmeticThetaPositiveLineR0134
ec877 1
namespace ArithmeticThetaRelativeCyclicQuotientR0173
ec877 1
namespace ArithmeticThetaRelativeKatoNaturalityR0170
ec877 1
namespace ArithmeticThetaSchemeLevelR0204.SchemeFamilyBaseChange
ec877 2
namespace ProjWeierstrassCubicPrime
ec877 1
namespace HomogeneousIdealQuotientGrading
ec877 1
namespace NeronModelInfra
ec877 1
namespace WeierstrassProjModel
namespace RelativeGroupLaw
ec877 2
namespace WeierstrassProjModel
namespace RelativeGroupLaw
ec877 2
namespace WeierstrassProjModel
ec877 1
namespace WeierstrassProjModel
ec877 1
namespace WeierstrassProjModel
ec877 1
namespace SheafOfModules
ec877 1
namespace AlgebraicGeometry
ec877 1
section
rc590
cc2
cc0
cc1
universe u
cc12
open NeronModelInfra
cc3
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X: Scheme.{u}} (M: X.Modules): Prop where (exists_trivialization: ∀ x: X, ∃ (U: X.Opens), x ∈ U ∧ z29 ((zPB693 U.ι).obj M ≅ z8.unit U.toScheme.ringCatSheaf))
ec877 4
section
rc590
cc2
cc1
cc0
universe u
open CategoryTheory TopologicalSpace Opposite
cc3
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y: Scheme.{u}} (φ: X ⟶ Y)
section
variable {L: Y.Modules} {U: Y.Opens}
def pullbackLocalSection (s: Γ(L, U)): Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U):= ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s
ec877 7
namespace GoodReductionJacobian
namespace RelativeGroupLaw
ec877 2
namespace GoodReductionJacobian
namespace RelativeGroupLaw
ec877 2
namespace AlgebraicGeometry
namespace Scheme.IdealSheafData
ec877 3
namespace PresheafOfModules
namespace ExteriorPower
ec877 1
ec877 1
namespace PresheafOfModules
namespace ExteriorPower
ec877 1
ec877 1
namespace AlgebraicGeometry.Scheme.Modules
ec877 3
namespace AlgebraicGeometry.Scheme.Hom
ec877 3
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
namespace OmegaPull
namespace T0
ec877 2
namespace OmegaPull
ec877 3
namespace WeierstrassCurve.DrinfeldGlobal
ec877 2
section
rc590
cc2
open AlgebraicGeometry CategoryTheory
universe u
cc3
namespace ArithmeticThetaPullback
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
def pullback_unit_iso (X Y: Scheme.{u}) (p: X ⟶ Y): (zPB693 p).obj (z8.unit Y.ringCatSheaf) ≅ z8.unit X.ringCatSheaf:= by
  letI: (TopologicalSpace.Opens.map p.base).Final:= by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e:= asIso (z8.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
ec877 4
namespace ArithmeticThetaLineRoot
ec877 1
section
rc590
cc2
cc11
cc7
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
universe u
cc3
cc0
namespace ArithmeticThetaSheafTensor
variable (X: Scheme.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor: MonoidalCategory X.PresheafOfModules:=
  PresheafOfModulesOfCommRing.monoidalCategory (R:= X.presheaf)
def tensorPresheaf (H K: X.Modules): X.PresheafOfModules:= H.val ⊗ K.val
def sheafTensor (H K: X.Modules): X.Modules:= (z7.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)
def tensorUnitMap (H K: X.Modules): tensorPresheaf X H K ⟶ (sheafTensor X H K).val:= (z7.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _
def tensorSection (H K: X.Modules) (U: X.Opens) (s: Γ(H, U)) (t: Γ(K, U)): Γ(sheafTensor X H K, U):= (tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X, U)] t)
ec877 4
section
rc590
cc2
cc42
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor
universe u
cc3
namespace ArithmeticThetaTensorPower
def tensorPower (X: Scheme.{u}) (H: X.Modules): ℕ → X.Modules | 0 => z8.unit X.ringCatSheaf | n + 1 => sheafTensor X (tensorPower X H n) H
ec877 4
namespace ArithmeticThetaPullback
ec877 1
section
rc590
cc2
cc43
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
universe u
cc3
cc0
cc7
namespace ArithmeticThetaPullback
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor (X: Scheme.{u}): MonoidalCategory X.PresheafOfModules:=
  PresheafOfModulesOfCommRing.monoidalCategory (R:= X.presheaf)
def sheafTensorMap (X: Scheme.{u}) {H H' K K': X.Modules} (f: H ⟶ H') (g: K ⟶ K'): sheafTensor X H K ⟶ sheafTensor X H' K':= (z7.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)
def sheafTensorCongr (X: Scheme.{u}) {H H' K K': X.Modules} (e: H ≅ H') (d: K ≅ K'): sheafTensor X H K ≅ sheafTensor X H' K':= (z7.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (tensorIso ((z8.forget _).mapIso e) ((z8.forget _).mapIso d))
def pullback_sheafTensor_iso (X Y: Scheme.{u}) (p: X ⟶ Y) (H K: Y.Modules): (zPB693 p).obj (sheafTensor Y H K) ≅ sheafTensor X ((zPB693 p).obj H) ((zPB693 p).obj K):= by sorry
run_cmd Lean.modifyEnv fun env => Lean.setDefHeightOverride env `ArithmeticThetaPullback.pullback_sheafTensor_iso 34
def pullback_tensorPower_iso (X Y: Scheme.{u}) (p: X ⟶ Y) (H: Y.Modules): (n: ℕ) → (zPB693 p).obj (tensorPower Y H n) ≅ tensorPower X ((zPB693 p).obj H) n | 0 => pullback_unit_iso X Y p | n + 1 => pullback_sheafTensor_iso X Y p (tensorPower Y H n) H ≪≫ sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)
ec877 4
namespace ArithmeticThetaNormalizedSections
ec877 1
namespace ArithmeticThetaCurveDegree
ec877 1
namespace ArithmeticThetaSectionOrder
ec877 1
namespace ArithmeticThetaNodeCharts
ec877 1
namespace ArithmeticThetaNodeCharts
ec877 1
namespace ArithmeticThetaScaledTateBridgeR0046
ec877 1
namespace ArithmeticThetaScaledAnnularR0050
ec877 1
namespace ArithmeticThetaAnnularTorsionPrereqR0053
ec877 1
namespace ArithmeticThetaIndexedOverlapsR0058
ec877 1
namespace ArithmeticThetaIndexedOverlapsR0058
ec877 1
namespace ArithmeticThetaInfinitesimalPolygonR0129
ec877 1
namespace ArithmeticThetaProjectiveEffectivityR0135
ec877 1
namespace ArithmeticThetaTateSeries
ec877 1
namespace ArithmeticThetaCubicModelR0144
ec877 1
namespace WeierstrassCurve.DrinfeldGlobal
ec877 2
namespace ArithmeticThetaCompactifiedDifferentialR0145
ec877 1
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace ProjectiveCubicChart
ec877 2
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace GlobalNormalizedDifferential
ec877 2
namespace ArithmeticThetaRelativeKatoR0169
ec877 1
namespace ArithmeticThetaRelativeDiscriminantR0171
ec877 1
namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
ec877 2
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
ec877 3
namespace ArithmeticThetaLocalWeierstrassR0203
ec877 1
namespace ArithmeticThetaFullLevelCoverR0175
ec877 1
namespace ArithmeticThetaLegendreAtlasR0176
ec877 1
namespace ArithmeticThetaLegendreComparisonR0177
ec877 1
namespace ArithmeticThetaCompatibleLevelR0178
ec877 1
namespace ArithmeticThetaSchemeLevelR0204
ec877 1
namespace ArithmeticThetaSchemeLevelR0204
ec877 1
namespace ArithmeticThetaSchemeLevelR0204
namespace CartesianFullMarking
ec877 2
namespace ArithmeticThetaSchemeLevelR0204
namespace GlobalSchemeClassifier
ec877 2
namespace ArithmeticThetaSchemeHodgeR0205
ec877 1
namespace ArithmeticThetaSchemeHodgeR0205
ec877 1
namespace ArithmeticThetaLevelCompactificationR0179
ec877 1
namespace ArithmeticThetaOpenHodgeR0180
ec877 1
namespace ArithmeticThetaTateCuspsR0181
ec877 1
namespace ArithmeticThetaUnaryProduct
ec877 1
namespace ArithmeticThetaBoundaryHodgeR0182
ec877 1
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
ec877 2
namespace ArithmeticThetaCompactUnaryR0183
ec877 1
namespace ArithmeticThetaComponentDegreeR0184
ec877 1
namespace ArithmeticThetaCommonHalfHodgeR0185
ec877 1
namespace ArithmeticThetaSimultaneousUnaryR0187
ec877 1
namespace ArithmeticThetaOrthogonalAlgorithm
ec877 1
namespace ArithmeticThetaEnumeration
ec877 1
namespace ArithmeticThetaElimination
ec877 1
namespace ArithmeticThetaComputed
ec877 1
namespace ArithmeticThetaOrthogonalConsumerR0127
ec877 1
namespace ArithmeticThetaLatticeSectionsR0188
ec877 1
section
rc590
cc2
cc29
universe u
cc3
namespace ArithmeticThetaCoverComparison
def tensorPowerMap {X: Scheme.{u}} {H J: X.Modules} (a: H ⟶ J): (n: ℕ) → ArithmeticThetaTensorPower.tensorPower X H n ⟶ ArithmeticThetaTensorPower.tensorPower X J n | 0 => 𝟙 _ | n + 1 => ArithmeticThetaPullback.sheafTensorMap X (tensorPowerMap a n) a
ec877 4
namespace ArithmeticThetaCoverComparison
ec877 1
section
rc590
cc2
cc1
cc0
cc5
cc3
namespace ArithmeticThetaSquareLinesR0192
cc4
cc15
open ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
cc9
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaGlobalFourTorsionR0190
structure SquareLine (Z: Scheme) (W: Z.Modules) where (line: Z.Modules) (invertible: Scheme.Modules.IsInvertible line) (square: tensorPower Z line 2 ≅ W)
def squarePull {Z Y: Scheme} {W: Z.Modules} (f: Y ⟶ Z) (A: SquareLine Z W): tensorPower Y ((zPB693 f).obj A.line) 2 ≅ (zPB693 f).obj W:= (pullback_tensorPower_iso Y Z f A.line 2).symm ≪≫ (zPB693 f).mapIso A.square
ec877 4
namespace ArithmeticThetaSharpCoverR0194
ec877 1
namespace ArithmeticThetaSharpKernelR0195
ec877 1
namespace ArithmeticThetaMetaplecticTestsR0196
ec877 1
namespace ArithmeticThetaRootDescentR0197
ec877 1
namespace ArithmeticThetaRootStackR0198
ec877 1
namespace ArithmeticThetaRootStackR0198
namespace RootModuliPseudofunctorR0198
ec877 2
namespace ArithmeticThetaMetaplecticComparisonR0206
ec877 1
namespace ArithmeticThetaMetaplecticComparisonR0206
ec877 1
namespace ArithmeticThetaMetaplecticComparisonR0206
ec877 1
namespace ArithmeticThetaMetaplecticComparisonR0206
namespace FiberEquivalenceProof
ec877 2
namespace ArithmeticThetaMetaplecticStackR0207
ec877 1
namespace ArithmeticThetaMetaplecticStackR0207
namespace ActualFamilyFPQCDescentProof
ec877 2
namespace ArithmeticThetaStackLevelR0199
ec877 1
namespace ArithmeticThetaStackLevelR0199
namespace RootClassifyingMapR0199
ec877 2
namespace PalomarClassifier667
ec877 1
namespace ArithmeticThetaActualLevelR0208
ec877 1
namespace ArithmeticThetaCompactModularityR0209
ec877 1
namespace ArithmeticThetaArithmeticFieldR0231
ec877 1
namespace ArithmeticThetaFieldImageR0233
ec877 1
namespace PalomarCyclotomic669
ec877 1
namespace PalomarConormal673
ec877 1
namespace PalomarPullback678
ec877 1
section
universe u
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSheafTensor ArithmeticThetaPullback
namespace PalomarTensor688
variable {X Y: Scheme.{u}} (f: X ⟶ Y) (H K: Y.Modules)
theorem normalized_iff_original (q: (zPB693 f).obj (sheafTensor Y H K) ≅ sheafTensor X ((zPB693 f).obj H) ((zPB693 f).obj K)): (∀ (U: Y.Opens) (s: Γ(H,U)) (t: Γ(K,U)), q.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t)) = tensorSection X ((zPB693 f).obj H) ((zPB693 f).obj K) (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) (Scheme.Modules.pullbackLocalSection f t)) ↔ q = pullback_sheafTensor_iso X Y f H K:= by sorry
ec877 2
namespace PalomarZero694
ec877 1
namespace ArithmeticThetaCompactUnaryR0183
ec877 1
namespace ArithmeticThetaComputed
ec877 1
namespace ArithmeticThetaLatticeSectionsR0188
ec877 1
namespace ArithmeticThetaConservativeKernelR0189
ec877 1
namespace ArithmeticThetaLevelCount
ec877 1
namespace PalomarRemaining861
ec877 1
namespace ArithmeticThetaOrthogonalAlgorithm
ec877 1
namespace ArithmeticThetaLDLEnumerationR0229
ec877 1
namespace ArithmeticThetaAdaptiveSolverR0230
ec877 1
namespace ArithmeticThetaArithmeticFieldR0231
ec877 1
namespace ArithmeticThetaScalarExtensionR0240
ec877 1
namespace ArithmeticThetaExtendedMetaplecticR0241
ec877 1
namespace PalomarRemaining861
ec877 1
@[expose] public section
noncomputable section

namespace PalomarSquare918
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaActualLevelR0208 ArithmeticThetaExtendedMetaplecticR0241
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196
def SquareTriangle : Prop :=
∀ {X Y Y' Z : Scheme.{0}}
    (a : X ⟶ Y) (g : Y ⟶ Z) (b : X ⟶ Y') (j : Y' ⟶ Z)
    (h : a ≫ g = b ≫ j) {W : Z.Modules} (A : SquareLine Z W),
    tensorPowerMap (((Scheme.Modules.pullbackComp a g).app A.line ≪≫
      (Scheme.Modules.pullbackCongr h).app A.line ≪≫
      ((Scheme.Modules.pullbackComp b j).app A.line).symm).inv) 2 ≫
      (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback a).map (squarePull g A).hom ≫
      ((Scheme.Modules.pullbackComp a g).app W ≪≫
        (Scheme.Modules.pullbackCongr h).app W ≪≫
        ((Scheme.Modules.pullbackComp b j).app W).symm).hom =
    (pullback_tensorPower_iso X Y' b ((Scheme.Modules.pullback j).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback b).map (squarePull j A).hom
theorem square_triangle : SquareTriangle := by sorry
end PalomarSquare918
end
