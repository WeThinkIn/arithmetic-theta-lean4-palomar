import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Tactic

open AlgebraicGeometry

universe u

namespace ArithmeticThetaGeometry

/- The value of `Scheme.ord` at the unit is zero, including at points that are
   not codimension one.  This is the base case for multiplicativity. -/
private theorem function_order_one
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    Scheme.ord (1 : X.functionField) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · simp [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, WithZero.unzeroD]
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx 1

theorem function_order_pow
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (f : X.functionField) (hf : f ≠ 0) (n : ℕ) :
    Scheme.ord (f ^ n) x = (n : ℤ) * Scheme.ord f x := by
  induction n with
  | zero => simp [function_order_one]
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

theorem function_order_nonneg_of_pow
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (f : X.functionField) (hf : f ≠ 0)
    (n : ℕ) (hn : 0 < n) (hpow : 0 ≤ Scheme.ord (f ^ n) x) :
    0 ≤ Scheme.ord f x := by
  rw [function_order_pow X x f hf n] at hpow
  exact nonneg_of_mul_nonneg_right hpow (by exact_mod_cast hn)

end ArithmeticThetaGeometry

#print axioms ArithmeticThetaGeometry.function_order_pow
#print axioms ArithmeticThetaGeometry.function_order_nonneg_of_pow
