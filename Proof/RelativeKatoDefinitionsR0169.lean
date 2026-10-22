module

public import GeneralKatoBaseChangeR0168
public import GeneralKatoUnitLocusR0168
public import GeneralEllipticKatoDefinitionsR0168

@[expose] public section

/-! Relative Kato functions over normal integral rational algebras.
All predicates refer to the same projective Weierstrass scheme and its actual
multiplication maps. No existence, orders or regularity are assumed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable (R : Type u) [CommRing R]

abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} :=
  WeierstrassProjModel.projModelCR W.toProjective

def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) :=
  WeierstrassProjModel.projModelStrCR W.toProjective

def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W :=
  (WeierstrassProjModel.kwZeroSect R W).val

abbrev Law (W : WeierstrassCurve R) :=
  WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)

def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)),
    (G.one t).val = t ≫ origin R W) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (structureMap R W)), G.mul t x y = G.mul t y x)

variable [IsDomain R]

abbrev GenericCurve (W : WeierstrassCurve R) : Scheme.{u} :=
  ArithmeticThetaGeneralEllipticKatoR0168.Curve (FractionRing R)
    (W.map (algebraMap R (FractionRing R)))

/-- The generic comparison includes its actual Cartesian scheme map and the
induced function-field isomorphism, not a freely chosen coefficient action. -/
structure GenericComparison (W : WeierstrassCurve R) (G : Law R W)
    [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)] where
  law : ArithmeticThetaGeneralEllipticKatoR0168.Law (FractionRing R)
    (W.map (algebraMap R (FractionRing R)))
  originLaw : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (FractionRing R)
    (W.map (algebraMap R (FractionRing R))) law
  map : GenericCurve R W ⟶ Curve R W
  cartesian : IsPullback map
    (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (FractionRing R)
      (W.map (algebraMap R (FractionRing R))))
    (structureMap R W) (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  origin_eq : ArithmeticThetaGeneralEllipticKatoR0168.origin (FractionRing R)
    (W.map (algebraMap R (FractionRing R))) ≫ map =
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ origin R W
  multiplication_eq : ∀ n : ℕ, law.schemeNsmul n ≫ map = map ≫ G.schemeNsmul n
  field : (Curve R W).functionField ≃+* (GenericCurve R W).functionField
  field_eq : ArithmeticThetaGeometricNormR0150.IsFieldMap map field.toRingHom

/-- This coefficient is used only at codimension-one points. At higher
codimension, membership in the identity section is not a divisor coefficient. -/
def katoOrder (W : WeierstrassCurve R) (G : Law R W) (c : ℕ)
    (x : Curve R W) : ℤ := by
  classical
  exact (if x ∈ Set.range (origin R W) then (c : ℤ)^2 else 0) -
    (if G.schemeNsmul c x ∈ Set.range (origin R W) then 1 else 0)

variable (W : WeierstrassCurve R) (G : Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]

/-- Normalization uses determinant norms for the actual multiplication maps. -/
def IsRelativeKato (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  g ≠ 0 ∧
  (∀ x : Curve R W, Order.coheight x = 1 → Scheme.ord g x = katoOrder R W G c x) ∧
  (∀ d : ℕ, 0 < d → Nat.Coprime c d →
    ∀ φ : (Curve R W).functionField →+* (Curve R W).functionField,
      ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ →
      ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g)

/-- Genuine sections of the structure sheaf on every torsion-free open,
with their actual generic restriction. -/
def UnitOnComplement (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  ∀ (U : (Curve R W).Opens) [Nonempty U],
    (∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W)) →
    ∃! a : (Curve R W).presheaf.obj (Opposite.op U),
      (Curve R W).germToFunctionField U a = g ∧ IsUnit a

end ArithmeticThetaRelativeKatoR0169
