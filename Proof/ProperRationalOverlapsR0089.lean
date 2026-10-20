module

public import ProperNoPoleDefinitionsR0089

@[expose] public section

/-! Equivalence of rational overlap equations and regular gluing on the actual
localized completed charts. Overlap rings need not be domains or nontrivial. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaProperNoPoleR0089
open ArithmeticThetaFormalConstants
variable (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
  (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))

/-- Every extension appearing in regular compatibility is the chosen actual
restriction. This uses uniqueness at both completion and localization. -/
lemma restriction_eq_of_extends {U V : X.Opens} (h : V ≤ U)
    (phi : Completed k X f U →+* Completed k X f V)
    (psi : Generic k X f U →+* Generic k X f V)
    (hphi : ExtendsRestriction (PowerSeries k) X f PowerSeries.X h phi)
    (hpsi : ExtendsLocalization (PowerSeries k) X f PowerSeries.X phi psi) :
    psi = restriction k X f h := by
  have hphi_eq := (Classical.choose_spec
    (completed_ring_restrictions (PowerSeries k) X f PowerSeries.X U V h)).2 phi hphi
  subst phi
  exact localizedRingRestriction_unique (PowerSeries k) X f PowerSeries.X _ _ _ hpsi
    (localizedRingRestriction_extends (PowerSeries k) X f PowerSeries.X h _ _)

/-- The universal extension formulation is equivalent to equality under the
canonical, uniquely constructed restriction maps. -/
lemma ringCompatible_iff_restriction (C : X.OrderedAffineCover)
    (z : RingFamily (PowerSeries k) X f PowerSeries.X C) :
    RingCompatible (PowerSeries k) X f PowerSeries.X C z ↔
      ∀ i j, restriction k X f (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) (z i) =
        restriction k X f (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) (z j) := by
  constructor
  · intro hz i j
    exact hz i j _ _ _ _
      (Classical.choose_spec (completed_ring_restrictions (PowerSeries k) X f
        PowerSeries.X (C.U i) (C.U i ⊓ C.U j) inf_le_left)).1
      (Classical.choose_spec (completed_ring_restrictions (PowerSeries k) X f
        PowerSeries.X (C.U j) (C.U i ⊓ C.U j) inf_le_right)).1
      (localizedRingRestriction_extends (PowerSeries k) X f PowerSeries.X inf_le_left _ _)
      (localizedRingRestriction_extends (PowerSeries k) X f PowerSeries.X inf_le_right _ _)
  · intro hz i j phi phi' psi psi' hphi hphi' hpsi hpsi'
    rw [restriction_eq_of_extends k X f inf_le_left phi psi hphi hpsi,
      restriction_eq_of_extends k X f inf_le_right phi' psi' hphi' hpsi']
    exact hz i j

/-- Cross-multiplied rational compatibility agrees exactly with regular gluing.
No cancellation or nonzero-denominator assertion is needed in overlap rings. -/
theorem regular_rational_overlap_equivalence
    (C : X.OrderedAffineCover) (hC : ChartConditions k X f C)
    (z : RingFamily (PowerSeries k) X f PowerSeries.X C) :
    RationalCompatible k X f C (embedFamily k X f C z) ↔
      RingCompatible (PowerSeries k) X f PowerSeries.X C z := by
  rw [ringCompatible_iff_restriction]
  constructor
  · intro hz i j
    let : IsDomain (Completed k X f (C.U i)) := (hC i).1
    let : IsDomain (Completed k X f (C.U j)) := (hC j).1
    let : IsDomain (Generic k X f (C.U i)) :=
      Localization.Away.isDomain (hC i).2.2.2
    let : IsDomain (Generic k X f (C.U j)) :=
      Localization.Away.isDomain (hC j).2.2.2
    simpa only [map_one, mul_one] using
      hz i j (z i) 1 (z j) 1 one_ne_zero one_ne_zero
        (by simp [embedFamily]) (by simp [embedFamily])
  · intro hz i j a b a' b' _hb _hb' hi hj
    have hi' : z i * b = a := by
      apply IsFractionRing.injective (Generic k X f (C.U i)) (Fractions k X f (C.U i))
      simpa only [embedFamily, toFraction, map_mul] using hi
    have hj' : z j * b' = a' := by
      apply IsFractionRing.injective (Generic k X f (C.U j)) (Fractions k X f (C.U j))
      simpa only [embedFamily, toFraction, map_mul] using hj
    rw [← hi', ← hj', map_mul, map_mul, hz i j]
    exact mul_right_comm _ _ _

end ArithmeticThetaProperNoPoleR0089
