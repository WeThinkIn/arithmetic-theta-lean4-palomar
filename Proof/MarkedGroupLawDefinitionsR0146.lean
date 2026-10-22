module

public import CompactifiedCoordinateIsomorphismR0145
public import GlobalNormalizedDifferentialR0145
public import GeometricThetaLiftsDefinitionsR0141
public import CompactifiedDifferentialDefinitionsR0145
public import GenericAffineCubicIsomorphismR0144

@[expose] public section

/-! Group laws and translation comparisons on the actual algebraized generic
curve. These definitions assert no existence or torsion theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

abbrev Law (M : Model k T) :=
  WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (genericStructure k M)

/-- Every test scheme uses the same specified structural map. -/
def pointOver (M : Model k T) {V : Scheme.{u}}
    (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) :
    SchemeHomOver t (genericStructure k M) :=
  ⟨t ≫ genericPoint k M s hs, by rw [Category.assoc, genericPoint_structure, Category.comp_id]⟩

/-- The group axioms and functoriality belong to RelativeGroupLaw; these are
its prescribed identity and commutativity, not arbitrary proposition fields. -/
def IsOriginLaw (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k))),
    G.one t = pointOver k M t s hs) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (x y : SchemeHomOver t (genericStructure k M)), G.mul t x y = G.mul t y x)

/-- Equality for every test scheme, hence an actual morphism comparison. -/
def IsTranslation (M : Model k T) (G : Law k M)
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 (baseScheme k))
    (f : genericScheme k M ⟶ genericScheme k M) : Prop :=
  ∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (x : SchemeHomOver t (genericStructure k M)),
    (G.mul t x (pointOver k M t p hp)).val = x.val ≫ f

def rotationMap (M : Model k T) (rot : M.X ≅ M.X)
    (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) : genericScheme k M ⟶ genericScheme k M :=
  genericMap k M rot.hom (modelOver k M (next r hr) 1 false rot ha.1)

def sumIndex (i j : Fin r) : Fin r := ⟨(i.val + j.val) % r, Nat.mod_lt _ hr⟩

def extensionBase (F : Type u) [Field F] [Algebra (LaurentSeries k) F] :
    Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (LaurentSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) F))

open ArithmeticThetaCompactifiedDifferentialR0145

abbrev PointEvaluation (r : ℕ) :=
  ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F],
    SchemeHomOver (extensionBase k F) (projectiveStructure k r) ≃
      ((curve k r).toProjective.baseChange F).toAffine.Point

/-- Actual projective-chart evaluation, with addition and Galois compatibility.
The coordinate condition rules out an arbitrary abstract group equivalence. -/
def IsCoordinateEvaluation (r : ℕ)
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) : Prop :=
  WeierstrassProjModel.IsPointsEval (curve k r).toProjective G ev ∧
  ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F]
    (P : SchemeHomOver (extensionBase k F) (projectiveStructure k r))
    (χ : ChartRing k r →+* F),
    P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r →
    ∃ hxy : ((curve k r).toProjective.baseChange F).toAffine.Nonsingular
        (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective))
        (χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective)),
      ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy

end ArithmeticThetaMarkedGroupLawR0146
