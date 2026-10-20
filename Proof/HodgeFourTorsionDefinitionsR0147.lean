module

public import ActualInverseComparisonR0146
public import SplitMarkedTorsionCompletenessR0146
public import FourTorsionRoot
public import FourTorsionCovariance

@[expose] public section

/-! Actual group endomorphisms, differential pullback equations and the Hodge
fiber at the specified identity. No new existence theorem is selected here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

abbrev Point (M : Model k T) :=
  SchemeHomOver (𝟙 (Spec (CommRingCat.of (LaurentSeries k)))) (genericStructure k M)

abbrev Frame (M : Model k T) :=
  (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
    (genericStructure k M).kaehler

def universalPoint (M : Model k T) :
    SchemeHomOver (genericStructure k M) (genericStructure k M) :=
  ⟨𝟙 _, Category.id_comp _⟩

def constantPoint (M : Model k T) (p : Point k M) :
    SchemeHomOver (genericStructure k M) (genericStructure k M) :=
  ⟨genericStructure k M ≫ p.val,
    by rw [Category.assoc, p.property, Category.comp_id]⟩

def translation (M : Model k T) (G : Law k M) (p : Point k M) :
    genericScheme k M ⟶ genericScheme k M :=
  (G.mul (genericStructure k M) (universalPoint k M) (constantPoint k M p)).val

def inverse (M : Model k T) (G : Law k M) :
    genericScheme k M ⟶ genericScheme k M :=
  (G.inv (genericStructure k M) (universalPoint k M)).val

def multiplication (M : Model k T) (G : Law k M) (n : ℕ) :
    genericScheme k M ⟶ genericScheme k M :=
  (G.nsmul (genericStructure k M) n (universalPoint k M)).val

/-- The coefficient of da in the actual normalized differential frame. -/
def frameDerivative (M : Model k T) (e : Frame k M)
    (U : (genericScheme k M).Opens) (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    (genericScheme k M).presheaf.obj (Opposite.op U) :=
  Scheme.Modules.Hom.app e.inv U (differentialAt k M U a)

/-- The local chain rule equivalent to f*delta = c delta, on ALL opens and
ALL functions, using the ring map of this actual scheme morphism. -/
def DifferentialWeight (M : Model k T) (e : Frame k M)
    (f : genericScheme k M ⟶ genericScheme k M) (c : LaurentSeries k) : Prop :=
  f ≫ genericStructure k M = genericStructure k M ∧
  ∀ (U : (genericScheme k M).Opens)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
    frameDerivative k M e (f ⁻¹ᵁ U) (f.app U a) =
      scalarAt k M (f ⁻¹ᵁ U) c * f.app U (frameDerivative k M e U a)

def halfIndex (r : ℕ) (hr : 0 < r) : Fin r :=
  ⟨r/2, Nat.div_lt_self hr (by decide)⟩

/-- Coordinates through the SPECIFIED projective compactification, including
its actual affine chart factorization and the actual Laurent scalar map. -/
def HasCoordinates (M : Model k T)
    (e : genericScheme k M ≅ projectiveCurve k r) (P : Point k M)
    (x y : LaurentSeries k) : Prop :=
  ∃ χ : ChartRing k r →+* LaurentSeries k,
    P.val ≫ e.hom = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r ∧
    χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) = x ∧
    χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective) = y

abbrev Hodge (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) :=
  (Scheme.Modules.pullback (genericPoint k M s hs)).obj (genericStructure k M).kaehler

def hodgeFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (e : Frame k M) :
    (SheafOfModules.unit (Spec (CommRingCat.of (LaurentSeries k))).ringCatSheaf :
      (Spec (CommRingCat.of (LaurentSeries k))).Modules) ≅ Hodge k M s hs :=
  letI := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unitPullback_isIso (genericPoint k M s hs)
  (asIso (unitPullback (genericPoint k M s hs))).symm ≪≫
    (Scheme.Modules.pullback (genericPoint k M s hs)).mapIso e

def hodgeSection (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (e : Frame k M) (c : LaurentSeries k) :
    Γ(Hodge k M s hs, ⊤) :=
  Scheme.Modules.Hom.app (hodgeFrame k M s hs e).hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c)

def alpha (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (e : Frame k M) (x y : LaurentSeries k) :
    Γ(Hodge k M s hs, ⊤) :=
  hodgeSection k M s hs e
    (2 * ArithmeticThetaFourTorsion.rootExpression (root k r 0) (root k r 1) (root k r 2) x y)

/-- Squaring in the actual sheaf tensor product of the Hodge fiber. -/
def HodgeSquare (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (e : Frame k M)
    (a : Γ(Hodge k M s hs, ⊤)) (c : LaurentSeries k) : Prop :=
  ArithmeticThetaSheafTensor.tensorSection (Spec (CommRingCat.of (LaurentSeries k)))
    (Hodge k M s hs) (Hodge k M s hs) ⊤ a a =
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c •
    ArithmeticThetaSheafTensor.tensorSection (Spec (CommRingCat.of (LaurentSeries k)))
      (Hodge k M s hs) (Hodge k M s hs) ⊤
      (hodgeSection k M s hs e 1) (hodgeSection k M s hs e 1)

end ArithmeticThetaHodgeFourTorsionR0147
