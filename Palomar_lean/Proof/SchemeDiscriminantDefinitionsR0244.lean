module

public import ArbitraryDiscriminantNaturalityR0243
public import SchemeLocalWeierstrassR0203
public import CartesianIdentityIdealR0205
public import SchemeCotangentCoherenceR0205
public import AffineConormalHodgeNaturalityR0205
public import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
public import ArbitraryDiscriminantDefinitionsR0243

@[expose] public section

/-! The actual identity cotangent, its canonical Cartesian comparison, and
normalization by every affine Weierstrass test. No new existence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeDiscriminantR0244
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171 hiding Base
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

abbrev Power {S : Scheme.{u}} (E : Family S) :=
  ArithmeticThetaTensorPower.tensorPower S (Cotangent E) 24

abbrev Sections {S : Scheme.{u}} (E : Family S) :=
  (Power E).presheaf.obj (Opposite.op ⊤)

/-- The comparison carries only actual geometric maps and their equations. -/
structure Comparison {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) where
  map : F.curve ⟶ E.curve
  cartesian : IsPullback map F.p E.p b
  pointed : F.zero ≫ map = b ≫ E.zero

def cotangentIso {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :
    (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F :=
  cotangentComparison E F b C.map C.pointed
    (cartesian_identity_ideal S T E F b C.map C.cartesian C.pointed).exists.choose

def powerIso {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :
    (Scheme.Modules.pullback b).obj (Power E) ≅ Power F :=
  tensorComparison b (Cotangent E) (Cotangent F) (cotangentIso C) 24

def pull {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) (d : Sections E) : Sections F :=
  res (Power F) (by simp)
    ((powerIso C).hom.app _ (Scheme.Modules.pullbackLocalSection b d))

/-- The existing Weierstrass curve and law, with its actual elliptic geometry. -/
def weierstrassFamily (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : Family (Base R) where
  curve := Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul
           mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel
           mul_natural := G.mul_natural, mul_comm := hG.2 }
  proper := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  dimension := WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  connected := by
    letI : GeometricallyIntegral (structureMap R W) := WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
    exact GeometricallyIrreducible.geometricallyConnected (structureMap R W)

/-- The conormal derivative, transported by the proved identity equation. -/
def weierstrassHodgeIso (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    Cotangent (weierstrassFamily R W G hG) ≅ Hodge R W := by
  let F := weierstrassFamily R W G hG
  letI := AffineConormalHodgeNaturality.differential_isIso F
  have hz : F.zero = origin R W := by
    change (G.one (𝟙 (Base R))).val = origin R W
    simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))
  exact asIso (affineDifferential F) ≪≫ pullbackEqIso hz (structureMap R W).kaehler

def weierstrassValue (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (d : Sections (weierstrassFamily R W G hG)) :
    ArithmeticThetaArbitraryDiscriminantR0243.Sections (HodgePower R W 24) :=
  (powerCongr (Base R) (weierstrassHodgeIso R W G hG) 24).hom.app ⊤ d

/-- Tests include arbitrary rational algebras, not just reduced or normal rings.
The field k fixes the characteristic-zero base and the actual structure maps. -/
def IsD2 (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S) (d : Sections E) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (b : Base R ⟶ S), b ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    ∀ C : Comparison E (weierstrassFamily R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W
        (weierstrassValue R W G hG (pull C d))

end ArithmeticThetaSchemeDiscriminantR0244
