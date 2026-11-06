module
public import Mathlib
public import RankZero
public import NormExponentAlgebra

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarFoundations269Elementary


/-- Independent exact target: accepted-000. -/
theorem rank_zero_coefficients :
  ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ, Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0 := by
  exact ArithmeticThetaElementary.rank_zero_coefficients

/-- Independent exact target: accepted-001. -/
theorem rank_zero_kernel :
  ∀ (h : ℕ) (c : Fin h → ℂ), (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = 0 ↔ (∑ i : Fin h, c i) = 0 := by
  exact ArithmeticThetaElementary.rank_zero_kernel

/-- Independent exact target: accepted-002. -/
theorem rank_zero_image :
  ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ, (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔ ∃ z : ℂ, f = PowerSeries.C z := by
  exact ArithmeticThetaElementary.rank_zero_image

/-- Independent exact target: accepted-090. -/
theorem norm_exponent_identities :
  ∀ (c d : ℚ), (d - 1) * (-c * (c - 1) / 2) + c * ((c - 1) * (d - 1) / 2) = 0 ∧ (d ^ 2 - 1) * (c ^ 2 - 1) / 12 + (-c * (c - 1) / 2) * d * (d - 1) / 2 + ((c ^ 2 - 1) * (d - 1) * (2 * d - 1) / 12 - d * (c - 1) * (d - 1) / 4) = 0 ∧ (d ^ 2 - 1) * (-c * (c - 1) / 2) + (c - 1) * (d - 1) / 2 = (c - 1) * (d - 1) * (1 - c * (d + 1)) / 2 := by
  exact ArithmeticThetaElementary.norm_exponent_identities

/-- Independent exact target: accepted-091. -/
theorem norm_sign_exponent_even :
  ∀ (c d : ℤ), Odd c → Even ((c - 1) * (d - 1) * (1 - c * (d + 1)) / 2) := by
  exact ArithmeticThetaElementary.norm_sign_exponent_even

end ArithmeticThetaPalomarFoundations269Elementary
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_coefficients
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_kernel
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_image
#print axioms ArithmeticThetaPalomarFoundations269Elementary.norm_exponent_identities
#print axioms ArithmeticThetaPalomarFoundations269Elementary.norm_sign_exponent_even
