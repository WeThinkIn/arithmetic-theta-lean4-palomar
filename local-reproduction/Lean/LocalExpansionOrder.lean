import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Formal expansion order in a discrete valuation ring

The comparison uses the factorization of a nonzero element as a unit times a
power of the specified irreducible uniformizer. Both orders take values in ℕ∞.
-/

universe u v

namespace ArithmeticThetaFormalOrder

/-- An expansion carrying a uniformizer to order one preserves quotient-length order. -/
theorem expansion_order
    (R : Type u) (k : Type v) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k]
    (φ : R →+* PowerSeries k) (π : R)
    (hπ : Irreducible π) (horder : (φ π).order = 1) (a : R) :
    (φ a).order = Ring.ord R a := by
  by_cases ha : a = 0
  · subst a
    simp [Ring.ord_eq_addVal]
  · obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hunit : (φ (u : R)).order = 0 :=
      PowerSeries.order_zero_of_unit (u.isUnit.map φ)
    have hregular : π ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero
    rw [map_mul, map_pow, PowerSeries.order_mul, hunit,
      PowerSeries.order_pow, horder, zero_add,
      Ring.ord_mul_of_isUnit_left u.isUnit,
      Ring.ord_pow hregular, Ring.ord_of_irreducible hπ]

/-- The order comparison implies that the expansion map is injective. -/
theorem expansion_injective
    (R : Type u) (k : Type v) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k]
    (φ : R →+* PowerSeries k) (π : R)
    (hπ : Irreducible π) (horder : (φ π).order = 1) :
    Function.Injective φ := by
  have hkernel : ∀ a : R, φ a = 0 → a = 0 := by
    intro a ha
    by_contra hnonzero
    have hfinite : Ring.ord R a ≠ ⊤ :=
      Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero)
    apply hfinite
    rw [← expansion_order R k φ π hπ horder a, ha, PowerSeries.order_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hab, sub_self]

end ArithmeticThetaFormalOrder
