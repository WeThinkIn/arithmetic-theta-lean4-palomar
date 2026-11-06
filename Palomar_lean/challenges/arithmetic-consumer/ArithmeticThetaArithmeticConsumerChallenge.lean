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
namespace AlgebraicGeometry
ec877 1
namespace AlgebraicGeometry.Scheme.Modules
ec877 3
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
namespace ArithmeticThetaPullback
ec877 1
namespace ArithmeticThetaLineRoot
ec877 1
namespace ArithmeticThetaSheafTensor
ec877 1
namespace ArithmeticThetaTensorPower
ec877 1
namespace ArithmeticThetaPullback
ec877 1
namespace ArithmeticThetaPullback
ec877 1
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
section
rc590
cc2
namespace ArithmeticThetaUnaryProduct
open scoped PowerSeries.WithPiTopology
noncomputable def clearedUnaryTheta (m: ℕ) (ν: ℤ): z4 ℤ:= z4.mk (fun n => ∑ k ∈ Finset.Icc (-(n: ℤ)) ((n: ℤ)+1), if 12*((m: ℤ)*k+ν)^2=(n: ℤ) then (1: ℤ) else 0)
ec877 3
namespace ArithmeticThetaBoundaryHodgeR0182
ec877 1
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
ec877 2
section
rc590
cc2
cc1
cc0
cc3
namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
cc39
cc20
open ArithmeticThetaBoundaryHodgeR0182
abbrev level (N: ℕ): ℕ:= 24*N^2
ec877 4
namespace ArithmeticThetaComponentDegreeR0184
ec877 1
namespace ArithmeticThetaCommonHalfHodgeR0185
ec877 1
section
rc590
cc2
cc1
cc0
cc8
cc3
namespace ArithmeticThetaSimultaneousUnaryR0187
cc4
cc41
open ArithmeticThetaPullback ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
cc52
def unarySeries (k: Type) [z1 k] (N m: ℕ) (ν: ℤ): z4 k:= z4.map (Int.castRingHom k) (z4.subst (z4.X ^ (N^2/m)) (ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν))
ec877 4
section
rc590
cc2
namespace ArithmeticThetaOrthogonalAlgorithm
def pairing {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (x y: Fin n → ℤ): ℤ:= ∑ i: Fin n, ∑ j: Fin n, x i * A i j * y j
def project {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (b v: Fin n → ℤ): Fin n → ℤ:= fun i => pairing A b b * v i - pairing A b v * b i
def step {n: ℕ} (A C: Matrix (Fin n) (Fin n) ℤ) (k: Fin n): Matrix (Fin n) (Fin n) ℤ:= Matrix.of (fun i j => if k < j then project A (fun a => C a k) (fun a => C a j) i else C i j)
def runPrefix {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (k: ℕ): Matrix (Fin n) (Fin n) ℤ:= ((List.finRange n).take k).foldl (step A) 1
def basisMatrix {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ): Matrix (Fin n) (Fin n) ℤ:= runPrefix A n
def norms {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (j: Fin n): ℤ:= pairing A (fun i => basisMatrix A i j) (fun i => basisMatrix A i j)
def naturalNorms {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (j: Fin n): ℕ:= (norms A j).toNat
ec877 3
section
rc590
cc2
namespace ArithmeticThetaEnumeration
def normNumerator {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (x: Fin n → ℤ): ℤ:= ∑ i: Fin n, ∑ j: Fin n, x i * A i j * x j
def coordinateRadius {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (m: ℕ) (j: Fin n): ℕ:= Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs)
def integerInterval (R: ℕ): Finset ℤ:= (Finset.range (2 * R + 1)).image (fun k: ℕ => (k: ℤ) - (R: ℤ))
def searchBox {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (m: ℕ): Finset (Fin n → ℤ):= Fintype.piFinset (fun j => integerInterval (coordinateRadius A m j))
def coefficientsUpTo {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (B: ℕ): List ℕ:=
  let box:= searchBox A B
  List.ofFn (fun m: Fin (B + 1) =>
    (box.filter (fun x => normNumerator A x = 2 * (m.val: ℤ))).card)
ec877 3
section
rc590
cc2
namespace ArithmeticThetaElimination
def findPivot {m h: ℕ} (M: Matrix (Fin m) (Fin h) ℚ) (r: ℕ) (c: Fin h): Option (Fin m):= (List.finRange m).find? (fun i => r ≤ i.val && M i c != 0)
def swapRows {m k: ℕ} (M: Matrix (Fin m) (Fin k) ℚ) (r s: Fin m): Matrix (Fin m) (Fin k) ℚ:= Matrix.of (fun i j => if i = r then M s j else if i = s then M r j else M i j)
def pivotOperation {m h k: ℕ} (M: Matrix (Fin m) (Fin h) ℚ) (N: Matrix (Fin m) (Fin k) ℚ) (r s: Fin m) (c: Fin h): Matrix (Fin m) (Fin k) ℚ:=
  let S:= swapRows M r s
  let T:= swapRows N r s
  Matrix.of (fun i j => if i = r then T r j / S r c
    else T i j - S i c * (T r j / S r c))
structure State (m h: ℕ) where (reduced: Matrix (Fin m) (Fin h) ℚ) (transform: Matrix (Fin m) (Fin m) ℚ) (nextRow: ℕ) (pivots: List (Fin m × Fin h))
def initial {m h: ℕ} (A: Matrix (Fin m) (Fin h) ℚ): State m h:= ⟨A, 1, 0, []⟩
def step {m h: ℕ} (s: State m h) (c: Fin h): State m h:=
  if hr: s.nextRow < m then
    match findPivot s.reduced s.nextRow c with
    | none => s
    | some t =>
      { reduced:= pivotOperation s.reduced s.reduced ⟨s.nextRow, hr⟩ t c
        transform:= pivotOperation s.reduced s.transform ⟨s.nextRow, hr⟩ t c
        nextRow:= s.nextRow + 1
        pivots:= s.pivots ++ [(⟨s.nextRow, hr⟩, c)]}
  else s
def run {m h: ℕ} (A: Matrix (Fin m) (Fin h) ℚ): State m h:= (List.finRange h).foldl step (initial A)
def pivotRow {m h: ℕ} (s: State m h) (j: Fin h): Option (Fin m):= (s.pivots.find? (fun p => p.2 == j)).map Prod.fst
def pivotColumns {m h: ℕ} (s: State m h): List (Fin h):= s.pivots.map Prod.snd
def freeColumns {m h: ℕ} (s: State m h): List (Fin h):= (List.finRange h).filter (fun j => !(pivotColumns s).contains j)
def nullVector {m h : ℕ} (s : State m h) (f : Fin h) (j : Fin h) : ℚ :=
  if j = f then 1 else
    match pivotRow s j with
    | none => 0
    | some i => -s.reduced i f
def nullBasis {m h: ℕ} (A: Matrix (Fin m) (Fin h) ℚ): Fin (freeColumns (run A)).length → (Fin h → ℚ):= fun f => nullVector (run A) ((freeColumns (run A)).get f)
def columnCoordinates {m h: ℕ} (A: Matrix (Fin m) (Fin h) ℚ) (j: Fin h): Fin (run A).pivots.length → ℚ:= fun t => (run A).reduced (((run A).pivots.get t).1) j
ec877 3
section
rc590
cc2
namespace ArithmeticThetaComputed
def validGram {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ): Prop:= A.IsSymm ∧ (∀ i, Even (A i i)) ∧ ((1 / 2: ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ): z4 ℂ:= z4.mk (fun m => (Nat.card {x: Fin n → ℤ // ((1 / 2: ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') (fun i => (x i: ℚ)) = (m: ℚ)}: ℂ))
def coefficientMatrix {n h: ℕ} (A: Fin h → Matrix (Fin n) (Fin n) ℤ) (B: ℕ): Matrix (Fin (B+1)) (Fin h) ℚ:= fun a i => ((ArithmeticThetaEnumeration.coefficientsUpTo (A i) B).getD a.val 0: ℚ)
def selectedIndex {n h: ℕ} (A: Fin h → Matrix (Fin n) (Fin n) ℤ) (B: ℕ) (t: Fin (ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.length): Fin h:= ((ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.get t).2
ec877 3
section
rc590
cc2
cc1
cc3
universe u
namespace ArithmeticThetaOrthogonalConsumerR0127
def castVec (n: ℕ): (Fin n → ℤ) →+ (Fin n → ℚ) where
  toFun x:= fun j => (x j: ℚ)
  map_zero':= by ext j; simp
  map_add':= by intro x y; ext j; simp
def integerVectors (n: ℕ): AddSubgroup (Fin n → ℚ):= (castVec n).range
def preimageLattice {n: ℕ} (B: Matrix (Fin n) (Fin n) ℤ): AddSubgroup (Fin n → ℚ):= (integerVectors n).comap (B.map (Int.castRingHom ℚ)).mulVecLin.toAddMonoidHom
def periods {n: ℕ} (B: Matrix (Fin n) (Fin n) ℤ): AddSubgroup (preimageLattice B):= (integerVectors n).comap (preimageLattice B).subtype
abbrev RationalCosets {n: ℕ} (B: Matrix (Fin n) (Fin n) ℤ):= (preimageLattice B) ⧸ periods B
def cosetClass {n: ℕ} (B: Matrix (Fin n) (Fin n) ℤ) (t: preimageLattice B): RationalCosets B:= QuotientAddGroup.mk t
def Representatives {n: ℕ} (B: Matrix (Fin n) (Fin n) ℤ) (t: Fin B.det.natAbs → preimageLattice B): Prop:= Function.Bijective (fun i => cosetClass B (t i))
ec877 4
section
rc590
cc2
cc1
cc0
cc8
cc3
namespace ArithmeticThetaLatticeSectionsR0188
cc4
open ArithmeticThetaOrthogonalAlgorithm ArithmeticThetaOrthogonalConsumerR0127
cc22
open ArithmeticThetaNormalizedSections ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaPullback
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
cc52
abbrev Matrices (n h: ℕ):= Fin h → Matrix (Fin n) (Fin n) ℤ
abbrev Cosets {n h: ℕ} (A: Matrices n h) (i: Fin h):= Fin (basisMatrix (A i)).det.natAbs
def commonN {n h: ℕ} (A: Matrices n h): ℕ:= Finset.univ.lcm (fun ij: Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def centered (m: ℕ) (a: Fin m): ℤ:= if 2 * a.val < m then (a.val: ℤ) else (a.val: ℤ) - (m: ℤ)
structure Indexing {n h: ℕ} (A: Matrices n h) where (representatives: (i: Fin h) → Cosets A i → preimageLattice (basisMatrix (A i))) (residue: (i: Fin h) → Cosets A i → (j: Fin n) → Fin (naturalNorms (A i) j)) (count: ℕ) (pair: Fin count → ℕ × ℤ) (index: (i: Fin h) → Cosets A i → Fin n → Fin count)
def Indexed {n h: ℕ} (A: Matrices n h) (U: Indexing A): Prop:= (∀ i, Representatives (basisMatrix (A i)) (U.representatives i)) ∧ (∀ i a j, ∃ z: ℤ, (naturalNorms (A i) j: ℚ) * (U.representatives i a).val j = ((U.residue i a j).val: ℚ) + (naturalNorms (A i) j: ℚ) * (z: ℚ)) ∧ Function.Injective U.pair ∧ (∀ i a j, U.pair (U.index i a j) = (naturalNorms (A i) j, centered (naturalNorms (A i) j) (U.residue i a j))) ∧ (∀ z: Fin U.count, ∃ i a j, U.index i a j = z)
ec877 4
namespace ArithmeticThetaCoverComparison
ec877 1
namespace ArithmeticThetaCoverComparison
ec877 1
namespace ArithmeticThetaSquareLinesR0192
ec877 1
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
namespace PalomarTensor688
ec877 1
namespace PalomarZero694
ec877 1
@[expose] public section
noncomputable section
open scoped BigOperators
rc590
namespace ArithmeticThetaCompactUnaryR0183
abbrev exponent (N: ℕ): ℕ:= (1+12*N)^2-1
ec877 1
rc590
namespace ArithmeticThetaComputed
noncomputable def thetaMap {n h: ℕ} (A: Fin h → Matrix (Fin n) (Fin n) ℤ): (Fin h → ℂ) →ₗ[ℂ] z4 ℂ:= ∑ i, (z10.proj i: (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
ec877 1
rc590
rc590
namespace ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaSimultaneousUnaryR0187
def expanded {n h: ℕ} (A: Matrices n h) (c: Fin h → ℂ): z4 ℂ:= z4.subst (z4.X ^ ArithmeticThetaCompactUnaryR0183.level (commonN A)) (ArithmeticThetaComputed.thetaMap A c)
def FormalIdentity {n h: ℕ} (A: Matrices n h) (U: Indexing A): Prop:= ∀ c: Fin h → ℂ, expanded A c = ∑ i: Fin h, c i • (∑ a: Cosets A i, ∏ j: Fin n, unarySeries ℂ (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2)
ec877 1
rc590
namespace ArithmeticThetaConservativeKernelR0189
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
def cutoff {n h: ℕ} (A: Matrices n h) (U: Indexing A): ℕ:= n * (exponent (commonN A)) ^ U.count * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) / 48
ec877 1
rc590
namespace ArithmeticThetaLevelCount
def levelIndex (L: ℕ): ℚ:= (L: ℚ) ^ 3 * ∏ p ∈ L.primeFactors, (1 - (p: ℚ)⁻¹ ^ 2)
ec877 1
namespace PalomarRemaining861
ec877 2
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
namespace PalomarConsumer897
open AlgebraicGeometry ArithmeticThetaCompactModularityR0209
def ConsumerCore : Prop :=
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ B : ℕ, (if n = 0 then B = 0 else ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ B = ArithmeticThetaConservativeKernelR0189.cutoff A U ∧ (B : ℚ) = (n : ℚ) * ((ArithmeticThetaCompactUnaryR0183.exponent (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℕ) : ℚ)^U.count * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / 48) ∧ (∀ B' : ℕ, B ≤ B' → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) ∧ (∀ B' : ℕ, B ≤ B' → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j)
theorem consumer_core : ConsumerCore := by sorry
end PalomarConsumer897
end
