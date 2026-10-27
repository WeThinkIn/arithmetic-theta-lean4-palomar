import ProperRationalOverlapsR0089
import ProperFractionScalarsR0089

open AlgebraicGeometry CategoryTheory
universe u
noncomputable section
namespace ArithmeticThetaProperNoPoleR0089
open ArithmeticThetaFormalConstants

set_option autoImplicit false

/-- Height-one regularity on the actual localized completed charts yields a
unique structural Laurent scalar for a rationally compatible family. -/
theorem proper_model_no_pole_constant :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [CharZero k] [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f]
      [AlgebraicGeometry.Smooth (genericStructure k X f)]
      [AlgebraicGeometry.GeometricallyConnected (genericStructure k X f)]
      (C : X.OrderedAffineCover),
      ChartConditions k X f C →
      ∀ v : RationalFamily k X f C,
        RationalCompatible k X f C v → NoPole k X f C v →
          ∃! c : LaurentSeries k, FractionConstant k X f C v c := by
  intro k _ X f _ _ _ _ _ C hC v hcompat hnopole
  classical
  have hreg : ∀ i : C.ι, ∃ a : Generic k X f (C.U i),
      toFraction k X f (C.U i) a = v i := by
    intro i
    letI : IsDomain (Completed k X f (C.U i)) := (hC i).1
    letI : IsNoetherianRing (Completed k X f (C.U i)) := (hC i).2.1
    letI : IsIntegrallyClosed (Completed k X f (C.U i)) := (hC i).2.2.1
    letI : IsDomain (Generic k X f (C.U i)) :=
      Localization.Away.isDomain (hC i).2.2.2
    letI : IsNoetherianRing (Generic k X f (C.U i)) :=
      IsLocalization.isNoetherianRing
        (Submonoid.powers (ringParameter (PowerSeries k) X f PowerSeries.X (C.U i)))
        _ inferInstance
    letI : IsIntegrallyClosed (Generic k X f (C.U i)) :=
      isIntegrallyClosed_of_isLocalization _ _
        (powers_le_nonZeroDivisors_of_noZeroDivisors (hC i).2.2.2)
    exact ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
      (Generic k X f (C.U i)) (Fractions k X f (C.U i)) (v i)
      (hnopole i)
  let z : RingFamily (PowerSeries k) X f PowerSeries.X C :=
    fun i => Classical.choose (hreg i)
  have hv : embedFamily k X f C z = v := by
    funext i
    exact Classical.choose_spec (hreg i)
  have hz : RingCompatible (PowerSeries k) X f PowerSeries.X C z :=
    (regular_rational_overlap_equivalence k X f C hC z).mp
      (hv ▸ hcompat)
  obtain ⟨c, hc, hu⟩ := localized_ring_family_constant k X f C z hz
  refine ⟨c, ?_, ?_⟩
  · rw [← hv]
    exact (fraction_structural_scalar_equivalence k X f C hC z c).mpr hc
  · intro d hd
    apply hu d
    rw [← hv] at hd
    exact (fraction_structural_scalar_equivalence k X f C hC z d).mp hd

end ArithmeticThetaProperNoPoleR0089
