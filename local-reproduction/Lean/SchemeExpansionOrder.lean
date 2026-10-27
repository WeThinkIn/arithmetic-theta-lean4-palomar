import LocalExpansionOrder
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Geometric order and coefficient prefixes

The stalk and its map to the function field are Mathlib's actual scheme objects.
The local DVR comparison is supplied by the accepted dependency module.
-/

universe u v

namespace ArithmeticThetaFormalOrder

open AlgebraicGeometry

/-- Geometric order of a nonzero stalk germ equals its formal expansion order. -/
theorem scheme_expansion_order
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) (k : Type v) [Field k]
    (φ : X.presheaf.stalk x →+* PowerSeries k) (π : X.presheaf.stalk x)
    (hπ : Irreducible π) (horder : (φ π).order = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x =
      ((φ a).order.toNat : ℤ) := by
  rw [expansion_order (X.presheaf.stalk x) k φ π hπ horder a]
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  simp only [Scheme.ordHom, Ring.ordFrac_eq_ord _ ha]
  rw [Ring.ordMonoidWithZeroHom_eq_coe _
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
    (ENat.natCast_toNat_eq_self.mpr
      (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha))).symm]
  rfl

/-- Vanishing through an inclusive coefficient bound forces greater geometric order. -/
theorem scheme_prefix_order
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) (k : Type v) [Field k]
    (φ : X.presheaf.stalk x →+* PowerSeries k) (π : X.presheaf.stalk x)
    (hπ : Irreducible π) (horder : (φ π).order = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) (B : ℕ)
    (hcoeff : ∀ n : ℕ, n ≤ B → PowerSeries.coeff n (φ a) = 0) :
    (B : ℤ) < Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  have hφa : φ a ≠ 0 := by
    intro hz
    apply ha
    exact expansion_injective (X.presheaf.stalk x) k φ π hπ horder
      (hz.trans φ.map_zero.symm)
  have hbound : B < (φ a).order.toNat := by
    by_contra h
    exact PowerSeries.coeff_order hφa (hcoeff _ (Nat.le_of_not_gt h))
  rw [scheme_expansion_order X x hx k φ π hπ horder a ha]
  exact_mod_cast hbound

/-- Under substitution by a positive power, the prefix bound is multiplied by that power. -/
theorem scheme_ramified_prefix_order
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) (k : Type v) [Field k]
    (φ : X.presheaf.stalk x →+* PowerSeries k) (π : X.presheaf.stalk x)
    (hπ : Irreducible π) (horder : (φ π).order = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) (B w : ℕ) (hw : 0 < w)
    (f : PowerSeries k) (hexpand : φ a = PowerSeries.expand w (Nat.ne_of_gt hw) f)
    (hcoeff : ∀ n : ℕ, n ≤ B → PowerSeries.coeff n f = 0) :
    ((w * (B + 1) : ℕ) : ℤ) ≤
      Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  have hφa : φ a ≠ 0 := by
    intro hz
    apply ha
    exact expansion_injective (X.presheaf.stalk x) k φ π hπ horder
      (hz.trans φ.map_zero.symm)
  have hf : f ≠ 0 := by
    intro hz
    apply hφa
    simpa [hz] using hexpand
  have hbound : B + 1 ≤ f.order.toNat := by
    apply Nat.succ_le_of_lt
    by_contra h
    exact PowerSeries.coeff_order hf (hcoeff _ (Nat.le_of_not_gt h))
  rw [scheme_expansion_order X x hx k φ π hπ horder a ha,
    hexpand, PowerSeries.order_expand, nsmul_eq_mul, ENat.toNat_mul]
  simpa using (show ((w * (B + 1) : ℕ) : ℤ) ≤ (w * f.order.toNat : ℕ) by
    exact_mod_cast Nat.mul_le_mul_left w hbound)

end ArithmeticThetaFormalOrder
