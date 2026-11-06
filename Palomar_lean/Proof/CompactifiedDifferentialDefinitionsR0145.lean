module

public import GenericAffineCubicIsomorphismR0144
public import LogarithmicCoordinateDerivativeR0144
public import Definitions.Def_WeierstrassCurve_PointChart
public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Definitions.Def_AlgebraicGeometry_KaehlerModule
public import CubicModelDefinitionsR0144

@[expose] public section

/-! The projective cubic and genuine relative differential of the same actual
generic model. These are ordinary definitions, with no asserted existence. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompactifiedDifferentialR0145
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaPolygonCartierR0133

variable (k : Type u) [Field k] [CharZero k]

def root (r : ℕ) (j : Fin 3) : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k r j)

def curve (r : ℕ) : WeierstrassCurve (LaurentSeries k) where
  a₁ := 0
  a₂ := -(root k r 0 + root k r 1 + root k r 2)
  a₃ := 0
  a₄ := root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2
  a₆ := -(root k r 0 * root k r 1 * root k r 2)

abbrev projectiveCurve (r : ℕ) : Scheme.{u} :=
  WeierstrassProjModel.projModelCR (curve k r).toProjective

def projectiveStructure (r : ℕ) :
    projectiveCurve k r ⟶ Spec (CommRingCat.of (LaurentSeries k)) :=
  WeierstrassProjModel.projModelStrCR (curve k r).toProjective

abbrev ChartRing (r : ℕ) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing (curve k r).toProjective

def chartInclusion (r : ℕ) : Spec (CommRingCat.of (ChartRing k r)) ⟶ projectiveCurve k r :=
  WeierstrassCurve.DrinfeldGlobal.zChartι (curve k r).toProjective

def origin (r : ℕ) : Spec (CommRingCat.of (LaurentSeries k)) ⟶ projectiveCurve k r :=
  (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (curve k r)).val

/-- Identifies the actual two coordinate classes and the structural morphism. -/
def IsChartIso (r : ℕ)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) : Prop :=
  c.hom ≫ chartInclusion k r ≫ projectiveStructure k r = cubicStructure k r ∧
  (∀ odd : Bool,
    c.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv
      (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
       else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)) =
    (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv (cubicCoordinate k r odd))

def cubicDerivative (r : ℕ) : CubicRing k r :=
  3 * cubicCoordinate k r false ^ 2 -
    2 * algebraMap (LaurentSeries k) (CubicRing k r)
      (root k r 0 + root k r 1 + root k r 2) * cubicCoordinate k r false +
    algebraMap (LaurentSeries k) (CubicRing k r)
      (root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2)

abbrev DifferentialFrame (F B : Type u) [CommRing F] [CommRing B] [Algebra F B] :=
  B ≃ₗ[B] KaehlerDifferential F B

def NormalizedAffineFrame (F B : Type u) [CommRing F] [CommRing B] [Algebra F B]
    (x y dp : B) (e : DifferentialFrame F B) : Prop :=
  KaehlerDifferential.D F B x = (2 * y) • e 1 ∧
  KaehlerDifferential.D F B y = dp • e 1

def IsAffineDifferentialFrame (r : ℕ)
    (e : DifferentialFrame (LaurentSeries k) (CubicRing k r)) : Prop :=
  NormalizedAffineFrame (LaurentSeries k) (CubicRing k r)
    (cubicCoordinate k r false) (cubicCoordinate k r true) (cubicDerivative k r) e

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def IsCompactificationIso (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k))
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (e : genericScheme k M ≅ projectiveCurve k r) : Prop :=
  e.hom ≫ projectiveStructure k r = genericStructure k M ∧
  (complement k M s).ι ≫ e.hom = a.hom ≫ c.hom ≫ chartInclusion k r ∧
  genericPoint k M s hs ≫ e.hom = origin k r

def genericIdealInclusion (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :
    genericPower k M s d ⟶
      (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) :=
  (Scheme.Modules.pullback (genericInclusion k M)).map
    (GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ d)) ≫
      unitPullback (genericInclusion k M)

/-- Universal relative derivation for the particular structural ring map. -/
def relativeD {F : Type u} [CommRing F] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens)
    (a : C.presheaf.obj (Opposite.op U)) : Γ(f.kaehler, U) :=
  letI : Algebra F (C.presheaf.obj (Opposite.op U)) := f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (Opposite.op U)) a)

def differentialAt (M : Model k T) (U : (genericScheme k M).Opens)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    Γ((genericStructure k M).kaehler, U) :=
  relativeD (genericStructure k M) U a

/-- An isomorphism of the ACTUAL relative differential sheaf. The cleared
equation is d(X/a)=2(Y/b) delta; it is meaningful also at poles and zeros. -/
def IsGlobalDifferentialFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
      (genericStructure k M).kaehler) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (a : Γ(genericPower k M s 2, U))
    (b : Γ(genericPower k M s 3, U)),
    let ja : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (genericIdealInclusion k M s 2).app U a
    let jb : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (genericIdealInclusion k M s 3).app U b
    let xa : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (restrictDual k M s 2 X).app U a
    let yb : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (restrictDual k M s 3 Y).app U b
    jb • (ja • differentialAt k M U xa - xa • differentialAt k M U ja) =
      (2 * yb * ja^2) • Scheme.Modules.Hom.app e.hom U
        (1 : (genericScheme k M).presheaf.obj (Opposite.op U))

end ArithmeticThetaCompactifiedDifferentialR0145
