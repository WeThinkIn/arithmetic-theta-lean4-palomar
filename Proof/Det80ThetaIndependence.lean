module

public import Mathlib
public import Det80CoefficientMinor

@[expose] public section
open scoped BigOperators
noncomputable section
namespace ArithmeticThetaDet80
private def rep (j : Fin 3) (n : ℕ) : Type := {v : ℤ × ℤ //
  (![v.1 ^ 2 + 20 * v.2 ^ 2,
    3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
    4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (n : ℤ)}
private def theta (j : Fin 3) : PowerSeries ℂ :=
  PowerSeries.mk (fun m : ℕ => (Nat.card (rep j m) : ℂ))
private lemma c00 : (Nat.card (rep (0 : Fin 3) 0) : ℂ) = 1 := by
  have h := congrFun (congrFun actual_coefficient_matrix (0 : Fin 3)) (0 : Fin 3)
  have h' : (Nat.card (rep (0 : Fin 3) 0) : ℤ) = 1 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c01 : (Nat.card (rep (1 : Fin 3) 0) : ℂ) = 1 := by
  have h := congrFun (congrFun actual_coefficient_matrix (0 : Fin 3)) (1 : Fin 3)
  have h' : (Nat.card (rep (1 : Fin 3) 0) : ℤ) = 1 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c02 : (Nat.card (rep (2 : Fin 3) 0) : ℂ) = 1 := by
  have h := congrFun (congrFun actual_coefficient_matrix (0 : Fin 3)) (2 : Fin 3)
  have h' : (Nat.card (rep (2 : Fin 3) 0) : ℤ) = 1 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c10 : (Nat.card (rep (0 : Fin 3) 1) : ℂ) = 2 := by
  have h := congrFun (congrFun actual_coefficient_matrix (1 : Fin 3)) (0 : Fin 3)
  have h' : (Nat.card (rep (0 : Fin 3) 1) : ℤ) = 2 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c11 : (Nat.card (rep (1 : Fin 3) 1) : ℂ) = 0 := by
  have h := congrFun (congrFun actual_coefficient_matrix (1 : Fin 3)) (1 : Fin 3)
  have h' : (Nat.card (rep (1 : Fin 3) 1) : ℤ) = 0 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c12 : (Nat.card (rep (2 : Fin 3) 1) : ℂ) = 0 := by
  have h := congrFun (congrFun actual_coefficient_matrix (1 : Fin 3)) (2 : Fin 3)
  have h' : (Nat.card (rep (2 : Fin 3) 1) : ℤ) = 0 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c30 : (Nat.card (rep (0 : Fin 3) 3) : ℂ) = 0 := by
  have h := congrFun (congrFun actual_coefficient_matrix (2 : Fin 3)) (0 : Fin 3)
  have h' : (Nat.card (rep (0 : Fin 3) 3) : ℤ) = 0 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c31 : (Nat.card (rep (1 : Fin 3) 3) : ℂ) = 2 := by
  have h := congrFun (congrFun actual_coefficient_matrix (2 : Fin 3)) (1 : Fin 3)
  have h' : (Nat.card (rep (1 : Fin 3) 3) : ℤ) = 2 := by
    simpa [rep] using h
  exact_mod_cast h'
private lemma c32 : (Nat.card (rep (2 : Fin 3) 3) : ℂ) = 0 := by
  have h := congrFun (congrFun actual_coefficient_matrix (2 : Fin 3)) (2 : Fin 3)
  have h' : (Nat.card (rep (2 : Fin 3) 3) : ℤ) = 0 := by
    simpa [rep] using h
  exact_mod_cast h'
 theorem full_theta_independent : LinearIndependent ℂ (fun j : Fin 3 => (PowerSeries.mk (fun m : ℕ => (Nat.card {v : ℤ × ℤ //
    (![v.1 ^ 2 + 20 * v.2 ^ 2,
      3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
      4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} : ℂ)) : PowerSeries ℂ)) := by
  change LinearIndependent ℂ theta
  rw [Fintype.linearIndependent_iff]
  intro c h i
  have h0 := congrArg (PowerSeries.coeff 0) h
  have h1 := congrArg (PowerSeries.coeff 1) h
  have h3 := congrArg (PowerSeries.coeff 3) h
  have e0 : c 0 + c 1 + c 2 = 0 := by
    simpa [theta, Fin.sum_univ_three, c00, c01, c02] using h0
  have e1 : 2 * c 0 = 0 := by
    simpa [theta, Fin.sum_univ_three, c10, c11, c12] using h1
  have e3 : 2 * c 1 = 0 := by
    simpa [theta, Fin.sum_univ_three, c30, c31, c32] using h3
  have hc0 : c 0 = 0 := by linear_combination e1 / 2
  have hc1 : c 1 = 0 := by linear_combination e3 / 2
  have hc2 : c 2 = 0 := by linear_combination e0 - e1 / 2 - e3 / 2
  fin_cases i <;> simp_all
 theorem actual_theta_kernel_zero : LinearMap.ker
    (∑ j : Fin 3, (LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight
      (PowerSeries.mk (fun m : ℕ => (Nat.card {v : ℤ × ℤ //
        (![v.1 ^ 2 + 20 * v.2 ^ 2,
          3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
          4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} : ℂ)) : PowerSeries ℂ)) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have hxy' : (∑ j : Fin 3, x j • theta j) = ∑ j : Fin 3, y j • theta j := by
    simpa [theta, rep, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply] using hxy
  have hzero : (∑ j : Fin 3, (x j - y j) • theta j) = 0 := by
    calc
      (∑ j : Fin 3, (x j - y j) • theta j) =
          ∑ j : Fin 3, (x j • theta j - y j • theta j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [sub_smul]
      _ = (∑ j : Fin 3, x j • theta j) - ∑ j : Fin 3, y j • theta j :=
        by simp only [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hxy'
  have hc : ∀ i : Fin 3, x i - y i = 0 :=
    (Fintype.linearIndependent_iff.mp (show LinearIndependent ℂ theta from full_theta_independent))
      (fun i => x i - y i) hzero
  funext i
  exact sub_eq_zero.mp (hc i)

end ArithmeticThetaDet80
