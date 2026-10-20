module

public import GlobalFamilyDiscriminantR0180
public import ArbitraryFramedPresentationR0203

@[expose] public section

/-! Normal models specify actual pointed Cartesian maps. The target coefficient
ring is arbitrary, including nonreduced rings. No independence or existence
of these models is included as an assumption in the discriminant predicate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryDiscriminantR0243
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

abbrev Sections {X : Scheme.{u}} (M : X.Modules) :=
  M.presheaf.obj (Opposite.op ⊤)

/-- A comparison uses the actual pointed Cartesian square, with no prescribed
section or equality of discriminant values. -/
structure Comparison (R S : Type u) [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (ι : R →+* S) where
  map : Curve S V ⟶ Curve R W
  cartesian : IsPullback map (structureMap S V) (structureMap R W)
    (Spec.map (CommRingCat.ofHom ι))
  pointed : origin S V ≫ map = Spec.map (CommRingCat.ofHom ι) ≫ origin R W

def comparisonHodge {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj
      (Hodge R W) ≅ Hodge S V := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact pointedDifferentialIso (structureMap R W) (structureMap S V)
    C.map C.cartesian (origin R W) (origin S V) C.pointed

def comparisonPower {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj
      (HodgePower R W 24) ≅ HodgePower S V 24 :=
  tensorComparison _ (Hodge R W) (Hodge S V) (comparisonHodge C) 24

/-- Pullback retains the literal differential comparison of the given map. -/
def pull {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι)
    (d : Sections (HodgePower R W 24)) : Sections (HodgePower S V 24) :=
  res (HodgePower S V 24) (by simp)
    ((comparisonPower C).hom.app _
      (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι)) d))

/-- The normal source has all the hypotheses of the accepted Kato initial-term
provider. The target has only its actual rational-algebra and ellipticity data. -/
structure NormalModel (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  equation : WeierstrassCurve ring
  [elliptic : equation.IsElliptic]
  [integral : IsIntegral (Curve ring equation)]
  [locallyNoetherian : IsLocallyNoetherian (Curve ring equation)]
  [genericIntegral : IsIntegral (GenericCurve ring equation)]
  [genericLocallyNoetherian : IsLocallyNoetherian (GenericCurve ring equation)]
  law : Law ring equation
  originLaw : IsOriginLaw ring equation law
  scalar : ring →ₐ[ℚ] R
  comparison : Comparison ring R equation W scalar.toRingHom

attribute [instance] NormalModel.commRing NormalModel.domain NormalModel.noetherian
  NormalModel.normal NormalModel.rational NormalModel.elliptic NormalModel.integral
  NormalModel.locallyNoetherian NormalModel.genericIntegral NormalModel.genericLocallyNoetherian

def value {R : Type u} [CommRing R] [Algebra ℚ R] {W : WeierstrassCurve R}
    (M : NormalModel R W) : Sections (HodgePower R W 24) :=
  pull M.comparison
    (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.localD
      M.ring M.equation M.law M.originLaw)

/-- Universal normal-source normalization, including maps into nonreduced
bases. Existence of a model and independence of its value are separate targets. -/
def IsD2 {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (d : Sections (HodgePower R W 24)) : Prop :=
  ∀ M : NormalModel R W, d = value M

end ArithmeticThetaArbitraryDiscriminantR0243
