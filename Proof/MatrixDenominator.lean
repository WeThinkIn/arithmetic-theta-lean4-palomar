module

public import Mathlib

@[expose] public section
open scoped BigOperators

namespace ArithmeticThetaLattice

theorem matrix_common_denominator : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℚ), ∃ D : ℕ, 0 < D ∧ ∃ Z : Matrix (Fin n) (Fin m) ℤ, ∀ i j, (Z i j : ℚ) = (D : ℚ) * A i j := by
  intro n m A
  let D : ℕ := ∏ i : Fin n, ∏ j : Fin m, (A i j).den
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact Rat.den_pos _
  refine ⟨D, hD, ?_⟩
  let Z : Matrix (Fin n) (Fin m) ℤ := fun i j => ((D / (A i j).den : ℕ) : ℤ) * (A i j).num
  refine ⟨Z, ?_⟩
  intro i j
  dsimp [Z]
  have hden : (A i j).den ∣ D := by
    dsimp [D]
    have hj' : (A i j).den ∣ ∏ j : Fin m, (A i j).den :=
      Finset.dvd_prod_of_mem (fun j : Fin m => (A i j).den) (Finset.mem_univ j)
    exact dvd_trans hj' (Finset.dvd_prod_of_mem (fun i : Fin n => ∏ j : Fin m, (A i j).den) (Finset.mem_univ i))
  change ((((D / (A i j).den : ℕ) : ℤ) * (A i j).num : ℤ) : ℚ) = (D : ℚ) * A i j
  rw [Int.cast_mul, Int.cast_natCast]
  have hcastdiv : ((D / (A i j).den : ℕ) : ℚ) = (D : ℚ) / (A i j).den := by
    rw [Nat.cast_div hden]
    exact_mod_cast (Rat.den_nz (A i j))
  rw [hcastdiv]
  calc
    (D : ℚ) / (A i j).den * (A i j).num = (D : ℚ) * ((A i j).num / (A i j).den) := by ring
    _ = (D : ℚ) * A i j := by rw [Rat.num_div_den]


end ArithmeticThetaLattice
