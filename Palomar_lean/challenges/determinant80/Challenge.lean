module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarExamples258Det80


def gram (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2*a, b; b, 2*c]

def gramContent (a b c : ℤ) : ℕ := Nat.gcd (Int.gcd (2*a) b) (Int.natAbs (2*c))

def shear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, k; 0, 1]

def forms : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![gram 1 0 20, gram 3 2 7, gram 4 0 5]

def value (j : Fin 3) (x : Fin 2 → ℤ) : ℤ :=
  (![x 0 ^ 2 + 20*x 1 ^ 2, 3*x 0 ^ 2 + 2*x 0*x 1 + 7*x 1 ^ 2,
    4*x 0 ^ 2 + 5*x 1 ^ 2] : Fin 3 → ℤ) j

def embeddings : Fin 3 → Matrix (Fin 2) (Fin 2) ℚ :=
  ![1, !![3, 1; 0, 1], !![2, 0; 0, 1/2]]

def sameLocalSmith (a b c : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ U V : Matrix (Fin 2) (Fin 2) (PadicInt p),
    IsUnit U.det ∧ IsUnit V.det ∧
      U * (gram a b c).map (Int.castRingHom (PadicInt p)) * V =
        (gram 1 0 20).map (Int.castRingHom (PadicInt p))


/-- Independent exact target: accepted-004. -/
theorem actual_coefficient_matrix :
  ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = ![![1, 1, 1], ![2, 0, 0], ![0, 2, 0]] := by
  sorry

/-- Independent exact target: accepted-005. -/
theorem actual_minor_determinant :
  Matrix.det ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 4 := by
  sorry

/-- Independent exact target: accepted-006. -/
theorem actual_theta_kernel_zero :
  LinearMap.ker (∑ j : Fin 3, (LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight (PowerSeries.mk (fun m : ℕ => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} : ℂ)) : PowerSeries ℂ)) = ⊥ := by
  sorry

/-- Independent exact target: accepted-010. -/
theorem all_positive_classes :
  ∀ a b c : ℤ, 0 < a → 4*a*c-b^2 = 80 → gramContent a b c = 2 → ∃ (j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ), IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  sorry

/-- Independent exact target: accepted-011. -/
theorem similarity_distinct :
  ∀ (i j : Fin 3), i ≠ j → ¬ ∃ (s : ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (forms j).map (Int.castRingHom ℚ) := by
  sorry

/-- Independent exact target: accepted-012. -/
theorem ambient_realization :
  ∀ j : Fin 3, (embeddings j).det ≠ 0 ∧ (embeddings j).transpose * (forms 0).map (Int.castRingHom ℚ) * embeddings j = (![1,3,1] : Fin 3 → ℚ) j • (forms j).map (Int.castRingHom ℚ) := by
  sorry

/-- Independent exact target: accepted-013. -/
theorem same_order_classes :
  ∀ a b c : ℤ, 0 < a → 0 < 4*a*c-b^2 → sameLocalSmith a b c → ∃! j : Fin 3, ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  sorry

/-- Independent exact target: support-representation-finiteness. -/
theorem representation_finiteness :
  ∀ (j : Fin 3) (m : ℕ), Set.Finite {v : ℤ × ℤ |
      (![v.1 ^ 2 + 20 * v.2 ^ 2,
        3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
        4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} := by
  sorry

end ArithmeticThetaPalomarExamples258Det80
