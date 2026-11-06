module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The universal Miller phase algebra

These are the two conditional field identities of the frozen `proof_5` scope.
No identification of the rational expression with a Weil pairing is asserted.
-/

namespace ArithmeticThetaFourTorsion

universe u

/-- Clear the Miller numerator using an explicit polynomial certificate. -/
theorem miller_cleared_identity :
    ∀ (k : Type u) [Field k] [CharZero k] (a b u v t : k),
      a ≠ 0 → b ≠ 0 → a ≠ b → v^2 = a*b →
      u^2+2*a*u+a*b = 0 →
      t^2*u*(u+a)*(u+b) = v*(v+a)*(v+b) →
      (v+a)*(v+b)*(u+a)^2*(v-t*u)^2 -
        u*v^2*(u+b)*t*((u+a)*t-v-a)^2 = 0 := by
  intro k _ _ a b u v t ha hb hab hv hu ht
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    exact mul_ne_zero ha hb (by simpa using hu)
  have hua : u + a ≠ 0 := by
    intro h
    have he : u = -a := eq_neg_of_add_eq_zero_left h
    rw [he] at hu
    have hz : a * (b - a) = 0 := by linear_combination hu
    exact mul_ne_zero ha (sub_ne_zero.mpr (Ne.symm hab)) hz
  have hub : u + b ≠ 0 := by
    intro h
    have he : u = -b := eq_neg_of_add_eq_zero_left h
    rw [he] at hu
    have hz : b * (b - a) = 0 := by linear_combination hu
    exact mul_ne_zero hb (sub_ne_zero.mpr (Ne.symm hab)) hz
  have hD : u * (u+a) * (u+b) ≠ 0 := mul_ne_zero (mul_ne_zero hu0 hua) hub
  apply (mul_eq_zero.mp (show u*(u+a)*(u+b) *
      ((v+a)*(v+b)*(u+a)^2*(v-t*u)^2 -
        u*v^2*(u+b)*t*((u+a)*t-v-a)^2) = 0 from ?_)).resolve_left hD
  linear_combination
    (u^2*(u+a)^2*(v+a)*(v+b) +
      2*u*v^2*(u+b)*(u+a)*(v+a) - u*v^2*(u+b)*(u+a)^2*t) * ht +
    (u*v*(a+u)*(a+v)*(b+v)*(a*b+a*v+2*b*v+u*v+v^2) -
      t*u*v*(a+u)*(a+v)*(b+u)*(a*v+2*b*u+2*u*v+v^2)) * hu +
    (u*v*(a+u)*(a+v)*(b+v)*(a+2*v)*(b+u) -
      t*u*v*(a+u)*(a+v)*(b+u)*(-2*a*u+a*v+2*b*u+u*v)) * hv

/-- Divide the cleared identity only at the explicitly nonzero factors. -/
theorem miller_rational_identity :
    ∀ (k : Type u) [Field k] [CharZero k] (a b u v t : k),
      a ≠ 0 → b ≠ 0 → a ≠ b → v^2 = a*b →
      u^2+2*a*u+a*b = 0 →
      t^2*u*(u+a)*(u+b) = v*(v+a)*(v+b) →
      u ≠ 0 → v ≠ 0 → v+b ≠ 0 → (u+a)*t-v-a ≠ 0 →
      (v+a)*(u+a)^2*(v-t*u)^2 / (u*v^2*((u+a)*t-v-a)^2) =
        (u+b)*t/(v+b) := by
  intro k _ _ a b u v t ha hb hab hv hu ht hu0 hv0 hvb hL
  have h := miller_cleared_identity k a b u v t ha hb hab hv hu ht
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hu0 (pow_ne_zero 2 hv0))
    (pow_ne_zero 2 hL)) hvb).2
  linear_combination h

end ArithmeticThetaFourTorsion
