module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Jacobi

namespace Hadamard
noncomputable def a : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ)} : ℤ))
noncomputable def b : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 0} : ℤ) -
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 1} : ℤ))
noncomputable def c : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // (2 * r + 1) ^ 2 = (m : ℤ)} : ℤ))

end Hadamard

namespace Durfee
noncomputable def normalizedFiniteProduct (N : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  (1 + PowerSeries.C (LaurentPolynomial.T 1)) *
    ∏ j ∈ Finset.range N,
      (1 - PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j+1))


end Durfee


/-- Exact independent target: accepted-007. -/
theorem formal_jacobi_triple_product :
  (PowerSeries.mk (fun e => PowerSeries.coeff e ((1 + PowerSeries.C (LaurentPolynomial.T 1)) * ∏ j ∈ Finset.range e, (1 - PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j + 1)) : PowerSeries (LaurentPolynomial ℤ)))) = PowerSeries.mk (fun d => ∑ k ∈ Finset.Icc (-(d : ℤ)) ((d : ℤ) + 1), if k * (k - 1) = 2 * (d : ℤ) then (LaurentPolynomial.T k : LaurentPolynomial ℤ) else 0) := by
  sorry

/-- Exact independent target: accepted-009. -/
theorem jacobi_formal :
  ArithmeticThetaPalomarFormal261Jacobi.Hadamard.a ^ 4 = ArithmeticThetaPalomarFormal261Jacobi.Hadamard.b ^ 4 + ArithmeticThetaPalomarFormal261Jacobi.Hadamard.c ^ 4 := by
  sorry

/-- Exact independent target: support-normalized-product-stability. -/
theorem normalized_partial_stable :
  ∀ (d N : ℕ), d ≤ N → PowerSeries.coeff d (ArithmeticThetaPalomarFormal261Jacobi.Durfee.normalizedFiniteProduct N) = PowerSeries.coeff d (ArithmeticThetaPalomarFormal261Jacobi.Durfee.normalizedFiniteProduct d) := by
  sorry

end ArithmeticThetaPalomarFormal261Jacobi
