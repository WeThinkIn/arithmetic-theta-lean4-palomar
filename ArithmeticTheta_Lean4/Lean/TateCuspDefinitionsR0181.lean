import OpenLevelNormalizedHodgePowerR0180
import MarkedPointAdditionR0146
import LevelBoundaryGeometryR0179
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! Tate tests of the actual compatible full-level compactification.
The marked points, classifying morphisms, disk maps and completion comparisons
below are construction targets. No cusp uniformization is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLevelCompactificationR0179

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)

abbrev TateCurve := ArithmeticThetaCompactifiedDifferentialR0145.curve k L
abbrev Disk := Base (PowerSeries k)
abbrev Puncture := Base (LaurentSeries k)
def genericInclusion : Puncture k ⟶ Disk k :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
def diskStructure : Disk k ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))
def closedPoint : Disk k := ⟨IsLocalRing.maximalIdeal (PowerSeries k), inferInstance⟩

/-- Full marking on the specific split cubic for period q=t^L. -/
structure TateLevel where
  elliptic : (TateCurve k L).IsElliptic
  law : Law (LaurentSeries k) (TateCurve k L)
  originLaw : IsOriginLaw (LaurentSeries k) (TateCurve k L) law
  marking : FullLevel (LaurentSeries k) (TateCurve k L) law L (𝟙 (Puncture k))

/-- Every nonidentity combination is the actual point with the literal Tate
coordinates of z=zeta^i*t^j. The excluded pair is the group identity. -/
def CanonicalMarking (ζ : k) (E : TateLevel k L) : Prop :=
  ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k)
      (TateCurve k L)
      (coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking i j)
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L j.val (ζ ^ i.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L j.val (ζ ^ i.val)))

/-- The actual invariant of the fixed cubic; division takes place in k((t)). -/
def tateJ : LaurentSeries k := (TateCurve k L).c₄ ^ 3 / (TateCurve k L).Δ

/-- Actual Legendre invariant pulled along the prescribed geometric maps. -/
def pulledParameter (D : LevelData k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k))
    (b : Puncture k ⟶ OpenBase k L D) : LaurentSeries k :=
  (Spec.preimage (b ≫ p)).hom (parameter k)
def legendreJ (a : LaurentSeries k) : LaurentSeries k :=
  256 * (1-a+a^2)^3 / (a^2*(1-a)^2)

def ClassifiesTate (D : LevelData k L) (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) : Prop :=
  ∃ f : Curve (LaurentSeries k) (TateCurve k L) ⟶ D.atlas.descent.family.curve,
    Classifies k L D.atlas D.two D.cover D.quotient
      (LaurentSeries k) (TateCurve k L) E.law E.marking b f

/-- The period is q=t^L in the very cubic used by ClassifiesTate. No free
parameter or unrelated map to the compact curve enters this extension. -/
def Extends (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space) : Prop :=
  d ≫ X.projection = diskStructure k ∧
  genericInclusion k ≫ d = b ≫ X.inclusion ∧
  d (closedPoint k) ∈ boundary k L D X

abbrev CuspStalk (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) := X.space.presheaf.stalk (d (closedPoint k))
def diskGerm : PowerSeries k →+* (Disk k).presheaf.stalk (closedPoint k) :=
  ((Disk k).presheaf.germ ⊤ (closedPoint k) (by trivial)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom

/-- The completion isomorphism must extend the actual map on local rings
induced by d. This excludes an arbitrary abstract power-series isomorphism. -/
def IsCompletedParameter (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) : Prop :=
  ∃ f : CuspStalk k L D X d →+* PowerSeries k,
    (diskGerm k).comp f = (d.stalkMap (closedPoint k)).hom ∧
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
        (CuspStalk k L D X d) ≃+* PowerSeries k,
      ∀ a, e (AdicCompletion.of (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
        (CuspStalk k L D X d) a) = f a

end ArithmeticThetaTateCuspsR0181
