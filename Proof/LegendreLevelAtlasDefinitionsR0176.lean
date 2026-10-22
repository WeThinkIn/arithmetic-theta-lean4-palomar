module

public import FullLevelBaseChangeR0175
public import FullLevelCoverGeometryR0175
public import NormalAffineLevelExtensionR0175
public import QuotientTargetFullLevelR0175
public import Mathlib.RingTheory.Localization.Away.Basic
public import FullLevelCoverDefinitionsR0175
public import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

@[expose] public section

/-! Definitions for a Legendre full-level atlas and actual sign descent.
The quotient and descended family occur only as construction targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

abbrev LegendreRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X * (Polynomial.X - 1) : Polynomial k)

def parameter (k : Type u) [Field k] : LegendreRing k :=
  algebraMap (Polynomial k) (LegendreRing k) Polynomial.X

def legendre (k : Type u) [Field k] : WeierstrassCurve (LegendreRing k) where
  a₁ := 0
  a₂ := -(parameter k + 1)
  a₃ := 0
  a₄ := parameter k
  a₆ := 0

def legendreBaseMap (k : Type u) [Field k] : Base (LegendreRing k) ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LegendreRing k)))

/-- The sign action is specified on both actual universal sections. Freeness
means an empty scheme equalizer, not absence of fixed underlying generic points. -/
structure SignAction (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L) where
  map : Z.space ⟶ Z.space
  over_eq : map ≫ Z.projection = Z.projection
  square : map ≫ map = 𝟙 _
  x_eq : map ≫ Z.level.x.val = (G.inv Z.projection Z.level.x).val
  y_eq : map ≫ Z.level.y.val = (G.inv Z.projection Z.level.y).val
  free : IsEmpty (equalizer map (𝟙 Z.space) : Scheme.{u})

/-- An affine degree-two quotient with its actual orbit relation and categorical
universal property. No quotient object is supplied to its existence theorem. -/
structure SignQuotient (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Base k) (σ : X ⟶ X) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  q : X ⟶ Base ring
  over_eq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k ring)) = p
  invariant : σ ≫ q = q
  finite : IsFinite q
  etale : Etale q
  surjective : Surjective q
  degree : ∀ x, q.finrank x = 2
  smooth : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k ring)))
  relation : (X ⨿ X) ≅ pullback q q
  left_fst : coprod.inl ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  left_snd : coprod.inl ≫ relation.hom ≫ pullback.snd q q = 𝟙 X
  right_fst : coprod.inr ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  right_snd : coprod.inr ≫ relation.hom ≫ pullback.snd q q = σ
  universal : ∀ (T : Scheme.{u}) (a : X ⟶ T), σ ≫ a = a →
    ∃! b : Base ring ⟶ T, q ≫ b = a

attribute [instance] SignQuotient.commRing SignQuotient.algebra

abbrev coverCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback (structureMap R W) Z.projection

abbrev coverToCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback.fst (structureMap R W) Z.projection

abbrev coverToLevel (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback.snd (structureMap R W) Z.projection

def coverSection (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L)
    (s : SchemeHomOver Z.projection (structureMap R W)) :
    Z.space ⟶ coverCurve R W Z :=
  pullback.lift s.val (𝟙 _) (by simpa using s.property)

/-- A genuine elliptic family over the quotient ring. The law is on all
scheme-valued points, and smoothness/properness concern its actual structure map. -/
structure EllipticFamily (S : Type u) [CommRing S] where
  curve : Scheme.{u}
  projection : curve ⟶ Base S
  law : GoodReductionJacobian.RelativeGroupLaw S projection
  commutative : law.IsCommutative
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  connected : GeometricallyConnected projection

structure FamilyLevel (S : Type u) [CommRing S] (E : EllipticFamily S) (L : ℕ) where
  x : SchemeHomOver (𝟙 (Base S)) E.projection
  y : SchemeHomOver (𝟙 (Base S)) E.projection
  killed_x : x.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  killed_y : y.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i.val x)
      (E.law.nsmul (𝟙 _) j.val y)).val) (Set.range (E.law.one (𝟙 _)).val)

/-- Rigidity of the actual descended marked family, as equality of scheme maps. -/
def FamilyRigid (S : Type u) [CommRing S] (E : EllipticFamily S) {L : ℕ}
    (M : FamilyLevel S E L) : Prop :=
  ∀ e : E.curve ≅ E.curve,
    e.hom ≫ E.projection = E.projection →
    (E.law.one (𝟙 _)).val ≫ e.hom = (E.law.one (𝟙 _)).val →
    M.x.val ≫ e.hom = M.x.val → M.y.val ≫ e.hom = M.y.val →
    e.hom = 𝟙 E.curve

/-- Descent of the SAME pullback family with the diagonal (negation,sign)
action. The Cartesian comparison and identity are part of the output. -/
structure FamilyDescent (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L)
    (σ : SignAction R W G Z)
    (Q : SignQuotient k (Z.projection ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map) where
  family : EllipticFamily Q.ring
  comparison : coverCurve R W Z ⟶ family.curve
  cartesian : IsPullback comparison (coverToLevel R W Z) family.projection Q.q
  origin_eq : coverSection R W Z (G.one Z.projection) ≫ comparison =
    Q.q ≫ (family.law.one (𝟙 _)).val
  action : coverCurve R W Z ⟶ coverCurve R W Z
  action_level : action ≫ coverToLevel R W Z = coverToLevel R W Z ≫ σ.map
  action_curve : action ≫ coverToCurve R W Z =
    (G.inv (coverToLevel R W Z ≫ Z.projection)
      ⟨coverToCurve R W Z, pullback.condition⟩).val
  invariant : action ≫ comparison = comparison

/-- Actual affine level atlas, with a family and full marking descended to its
sign quotient. Identification with a fine moduli scheme is deliberately not a
field of this construction and remains a separate theorem. -/
structure LegendreAtlas (k : Type u) [Field k] (L : ℕ) where
  law : Law (LegendreRing k) (legendre k)
  originLaw : IsOriginLaw (LegendreRing k) (legendre k) law
  level : LevelScheme (LegendreRing k) (legendre k) law L
  represents : Represents (LegendreRing k) (legendre k) law level
  sign : SignAction (LegendreRing k) (legendre k) law level
  quotient : SignQuotient k (level.projection ≫ legendreBaseMap k) sign.map
  descent : FamilyDescent k (LegendreRing k) (legendre k) law level sign quotient
  marking : FamilyLevel quotient.ring descent.family L
  rigid : FamilyRigid quotient.ring descent.family marking
  x_eq : coverSection (LegendreRing k) (legendre k) level level.level.x ≫
    descent.comparison = quotient.q ≫ marking.x.val
  y_eq : coverSection (LegendreRing k) (legendre k) level level.level.y ≫
    descent.comparison = quotient.q ≫ marking.y.val

end ArithmeticThetaLegendreAtlasR0176
