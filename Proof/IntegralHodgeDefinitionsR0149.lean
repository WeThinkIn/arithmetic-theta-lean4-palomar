module

public import ActualFourTorsionHodgeRootR0147
public import MultiplicationFiniteEtaleDegreeR0148
public import TateMarkedRootIdentity
public import AllHalfFormalRegularityR0108
public import HodgeFourTorsionDefinitionsR0147

@[expose] public section

/-! The integral identity Hodge sheaf and its prescribed generic restriction.
Every object and scalar map comes from the same algebraized polygon model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIntegralHodgeR0149
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

abbrev IntegralHodge (M : Model k T) (s : baseScheme k ⟶ M.X) :=
  (Scheme.Modules.pullback s).obj M.p.kaehler

abbrev IntegralFrame (M : Model k T) (s : baseScheme k ⟶ M.X) :=
  (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules) ≅
    IntegralHodge k M s

abbrev IntegralSection (M : Model k T) (s : baseScheme k ⟶ M.X) :=
  (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules) ⟶
    IntegralHodge k M s

abbrev GenericComparison (M : Model k T) :=
  (Scheme.Modules.pullback (genericInclusion k M)).obj M.p.kaehler ≅
    (genericStructure k M).kaehler

/-- This specifies the canonical base-change map on every differential generator. -/
def IsGenericComparison (M : Model k T) (b : GenericComparison k M) : Prop :=
  ∀ (U : M.X.Opens) (a : M.X.presheaf.obj (Opposite.op U)),
    b.hom.app ((genericInclusion k M) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection (genericInclusion k M) (relativeD M.p U a)) =
    differentialAt k M ((genericInclusion k M) ⁻¹ᵁ U)
      ((genericInclusion k M).app U a)

/-- The actual commuting-square comparison followed by relative differential base change. -/
def fiberComparison (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (b : GenericComparison k M) :
    (Scheme.Modules.pullback (genericBase k)).obj (IntegralHodge k M s) ≅
      Hodge k M s hs :=
  squareIso (genericInclusion k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M s hs) s (genericBase k)
    (by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericInclusion]) M.p.kaehler ≪≫
    (Scheme.Modules.pullback (ArithmeticThetaGenericEvaluationR0140.genericPoint k M s hs)).mapIso b

def ExtendsFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (b : GenericComparison k M)
    (E : IntegralFrame k M s) (δ : Frame k M) : Prop :=
  (Scheme.Modules.pullback (genericBase k)).map E.hom ≫ (fiberComparison k M s hs b).hom =
    unitPullback (genericBase k) ≫ (hodgeFrame k M s hs δ).hom

def genericRestriction (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (b : GenericComparison k M)
    (q : IntegralSection k M s) : Γ(Hodge k M s hs, ⊤) :=
  letI := unitPullback_isIso (genericBase k)
  let qg := inv (unitPullback (genericBase k)) ≫
    (Scheme.Modules.pullback (genericBase k)).map q ≫ (fiberComparison k M s hs b).hom
  qg.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv 1)

def coefficient (M : Model k T) (s : baseScheme k ⟶ M.X)
    (E : IntegralFrame k M s) (q : IntegralSection k M s) : PowerSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    (Scheme.Modules.Hom.app (q ≫ E.inv) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv 1))

/-- Fixed labelled two-torsion marks: -1, t^(r/2), -t^(r/2). -/
def torsionIndex (r : ℕ) (hr : 0 < r) (j : Fin 3) : Fin r :=
  if j = 0 then zeroIndex r hr else halfIndex r hr

def torsionUnit (j : Fin 3) : kˣ := if j = 1 then 1 else -1

def quarterIndex (r : ℕ) (hr : 0 < r) : Fin r :=
  ⟨r / 4, Nat.div_lt_self hr (by decide)⟩

def permutedCoefficient (r : ℕ) (σ : Equiv.Perm (Fin 3)) (x y : LaurentSeries k) :=
  2 * ArithmeticThetaFourTorsion.rootExpression
    (root k r (σ 0)) (root k r (σ 1)) (root k r (σ 2)) x y

def permutedAlpha (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (δ : Frame k M)
    (σ : Equiv.Perm (Fin 3)) (x y : LaurentSeries k) : Γ(Hodge k M s hs, ⊤) :=
  hodgeSection k M s hs δ (permutedCoefficient k r σ x y)

/-- Literal theta after the source substitution q=t^(r/2). -/
def thetaAt (r : ℕ) : PowerSeries k :=
  PowerSeries.subst (PowerSeries.X ^ (r / 2)) (ArithmeticThetaTateSeries.theta k)

end ArithmeticThetaIntegralHodgeR0149
