module

public import LocalizedRingFamilyConstant
public import NormalDomainIntersection
public import LocalizedRingModuleNaturality
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-! Rational functions on the actual completed affine charts of a proper model.
No fraction fields of possibly empty overlaps are introduced. Compatibility is
the ordinary cross-multiplied equality under the constructed restriction maps.
The equivalence with regular overlap equality is a proof obligation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaProperNoPoleR0089
open ArithmeticThetaFormalConstants
variable (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
  (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))

abbrev Completed (U : X.Opens) := RingCompleted (PowerSeries k) X f PowerSeries.X U
abbrev Generic (U : X.Opens) := LocalizedRing (PowerSeries k) X f PowerSeries.X U
abbrev Fractions (U : X.Opens) := FractionRing (Generic k X f U)
def toFraction (U : X.Opens) : Generic k X f U →+* Fractions k X f U := algebraMap _ _

/-- The source normality/noetherianity and parameter-torsion-free hypotheses
on the actual completed rings. For a domain, the last condition is equivalent
to injectivity of multiplication by the structural parameter. -/
def ChartConditions (C : X.OrderedAffineCover) : Prop :=
  ∀ i : C.ι, IsDomain (Completed k X f (C.U i)) ∧
    IsNoetherianRing (Completed k X f (C.U i)) ∧
    IsIntegrallyClosed (Completed k X f (C.U i)) ∧
    ringParameter (PowerSeries k) X f PowerSeries.X (C.U i) ≠ 0

def restriction {U V : X.Opens} (h : V ≤ U) :
    Generic k X f U →+* Generic k X f V :=
  localizedRingRestriction (PowerSeries k) X f PowerSeries.X h
    (Classical.choose (completed_ring_restrictions (PowerSeries k) X f PowerSeries.X U V h))
    (Classical.choose_spec (completed_ring_restrictions (PowerSeries k) X f PowerSeries.X U V h)).1

abbrev RationalFamily (C : X.OrderedAffineCover) := ∀ i : C.ι, Fractions k X f (C.U i)
def embedFamily (C : X.OrderedAffineCover)
    (z : RingFamily (PowerSeries k) X f PowerSeries.X C) : RationalFamily k X f C :=
  fun i => toFraction k X f (C.U i) (z i)

/-- Equality of every pair of fraction presentations in the actual completed
overlap ring. The denominators are arbitrary nonzero chart elements; the
definition does not assert regularity, no-pole conditions, or constancy. -/
def RationalCompatible (C : X.OrderedAffineCover) (v : RationalFamily k X f C) : Prop :=
  ∀ (i j : C.ι) (a b : Generic k X f (C.U i)) (a' b' : Generic k X f (C.U j)),
    b ≠ 0 → b' ≠ 0 →
    v i * toFraction k X f (C.U i) b = toFraction k X f (C.U i) a →
    v j * toFraction k X f (C.U j) b' = toFraction k X f (C.U j) a' →
    restriction k X f (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) a *
      restriction k X f (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) b' =
    restriction k X f (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) a' *
      restriction k X f (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) b

def NoPole (C : X.OrderedAffineCover) (v : RationalFamily k X f C) : Prop :=
  ∀ (i : C.ι) (p : Ideal (Generic k X f (C.U i))), p.IsPrime → p.height = 1 →
    ∃ a b : Generic k X f (C.U i), b ∉ p ∧
      v i * toFraction k X f (C.U i) b = toFraction k X f (C.U i) a

/-- A scalar equation in the actual chart fraction fields. The same numerator
and parameter denominator represent the Laurent series and every chart value.
This is a predicate to be proved, never a hypothesis of the main theorem. -/
def FractionConstant (C : X.OrderedAffineCover) (v : RationalFamily k X f C)
    (c : LaurentSeries k) : Prop :=
  ∃ (n : ℕ) (r : PowerSeries k),
    algebraMap (PowerSeries k) (LaurentSeries k) r =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X ^ n) * c ∧
    ∀ i : C.ι,
      toFraction k X f (C.U i)
        (localizedOf (PowerSeries k) X f PowerSeries.X (C.U i)
          (ringOf (PowerSeries k) X f PowerSeries.X (C.U i)
            (structuralMap (PowerSeries k) X f (C.U i) r))) =
      (toFraction k X f (C.U i)
        (localizedOf (PowerSeries k) X f PowerSeries.X (C.U i)
          (ringParameter (PowerSeries k) X f PowerSeries.X (C.U i)))) ^ n * v i

end ArithmeticThetaProperNoPoleR0089
