module

public import MarkedLegendreAtlasLocalCoverageR0177
public import OrderedLegendreParameterRigidityR0177
public import LegendreComparisonDefinitionsR0177

@[expose] public section

/-! The actual even-level compatibility locus and its classifying maps.
These are construction targets. No moduli universal property is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompatibleLevelR0178
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177

variable (k : Type u) [Field k] [CharZero k] (L : ℕ) (A : LegendreAtlas k L)

abbrev TwoMarking := FullLevel (LegendreRing k) (legendre k) A.law 2
  (𝟙 (Base (LegendreRing k)))

def CanonicalTwo (B : TwoMarking k L A) : Prop :=
  HasCoordinates (LegendreRing k) (legendre k) B.x.val 0 0 ∧
  HasCoordinates (LegendreRing k) (legendre k) B.y.val 1 0

/-- Both labels, as scheme maps on every test scheme, must reduce to the
canonical ordered two-torsion labels. -/
def CompatibleAt (B : TwoMarking k L A) {T : Scheme.{u}}
    (a : T ⟶ A.level.space) : Prop :=
  a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.x).val =
    (a ≫ A.level.projection) ≫ B.x.val ∧
  a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.y).val =
    (a ≫ A.level.projection) ≫ B.y.val

/-- The represented equalizer locus, with its actual degree over the Legendre
parameter base. It is not an arbitrarily selected union of components. -/
structure CompatibleCover (B : TwoMarking k L A) where
  space : Scheme.{u}
  inclusion : space ⟶ A.level.space
  openImmersion : IsOpenImmersion inclusion
  closedImmersion : IsClosedImmersion inclusion
  compatible : CompatibleAt k L A B inclusion
  represents : ∀ (T : Scheme.{u}) (a : T ⟶ A.level.space),
    CompatibleAt k L A B a ↔ ∃! b : T ⟶ space, b ≫ inclusion = a
  finite : IsFinite (inclusion ≫ A.level.projection)
  etale : Etale (inclusion ≫ A.level.projection)
  surjective : Surjective (inclusion ≫ A.level.projection)
  degree : ∀ z, (inclusion ≫ A.level.projection).finrank z = levelDegree L / 6

/-- Restrict the actual simultaneous-sign quotient to the compatibility locus.
Its image is an actual open-and-closed subscheme of the accepted quotient. -/
structure CompatibleQuotient (B : TwoMarking k L A) (C : CompatibleCover k L A B) where
  sign : C.space ⟶ C.space
  sign_eq : sign ≫ C.inclusion = C.inclusion ≫ A.sign.map
  sign_square : sign ≫ sign = 𝟙 _
  sign_free : IsEmpty (equalizer sign (𝟙 C.space) : Scheme.{u})
  quotient : SignQuotient k (C.inclusion ≫ A.level.projection ≫ legendreBaseMap k) sign
  inclusion : Base quotient.ring ⟶ Base A.quotient.ring
  cartesian : IsPullback C.inclusion quotient.q A.quotient.q inclusion
  openImmersion : IsOpenImmersion inclusion
  closedImmersion : IsClosedImmersion inclusion
  over_eq : inclusion ≫ Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k quotient.ring))

/-- Cartesian comparison with the SAME descended family, preserving the origin
and both full labels. The base map is required to respect the specified k-map. -/
def Classifies (B : TwoMarking k L A) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C)
    (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (b : Base R ⟶ Base Q.quotient.ring)
    (f : Curve R W ⟶ A.descent.family.curve) : Prop :=
  b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
  IsPullback f (structureMap R W) A.descent.family.projection (b ≫ Q.inclusion) ∧
  origin R W ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val ∧
  M.x.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.x.val ∧
  M.y.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.y.val

/-- The existing local comparison, now landing in the specified compatibility
quotient. The extension and comparison are constructed, not presumed. -/
structure LocalComparison (B : TwoMarking k L A) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C)
    (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R))) where
  comparison : AtlasComparison k R W G M A
  base : Base comparison.ring ⟶ Base Q.quotient.ring
  factorization : base ≫ Q.inclusion = comparison.base
  over_eq : base ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k comparison.ring))

/-- Actual inversion map, with no unrelated choice of an endomorphism. -/
def inversion (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) :
    Curve R W ⟶ Curve R W :=
  (G.inv (structureMap R W) ⟨𝟙 _, Category.id_comp _⟩).val

end ArithmeticThetaCompatibleLevelR0178
