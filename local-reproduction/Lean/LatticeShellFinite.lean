import RationalOrthogonalBasis

open scoped BigOperators

namespace ArithmeticThetaLattice

theorem coordinate_box_bound :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      ∀ C : ℚ, ∃ R : ℕ, ∀ x : Fin n → ℤ,
        Q (fun i => (x i : ℚ)) ≤ C →
          ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ) := by
  intro n Q hQ C
  obtain ⟨b, _horth, hw, hcoord⟩ := rational_orthogonal_basis n Q hQ
  let K : Fin n → ℚ := fun i => |C| / Q (b i) + 1
  have hK : ∀ i, 0 ≤ K i := by
    intro i
    dsimp [K]
    exact add_nonneg (div_nonneg (abs_nonneg C) (le_of_lt (hw i))) (by norm_num)
  let T : Fin n → ℚ := fun j => ∑ i, |b i j| * K i
  have hT : ∀ j, 0 ≤ T j := by
    intro j
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hK i))
  obtain ⟨R, hR⟩ := exists_nat_gt (∑ j, T j)
  refine ⟨R, ?_⟩
  intro x hx j
  let v : Fin n → ℚ := fun i => (x i : ℚ)
  have hy : ∀ i, |b.repr v i| ≤ K i := by
    intro i
    have hterm : Q (b i) * (b.repr v i) ^ 2 ≤ |C| := by
      calc
        Q (b i) * (b.repr v i) ^ 2 ≤ ∑ k, Q (b k) * (b.repr v k) ^ 2 :=
          Finset.single_le_sum (fun k _ => mul_nonneg (le_of_lt (hw k)) (sq_nonneg _))
            (Finset.mem_univ i)
        _ = Q v := (hcoord v).symm
        _ ≤ C := hx
        _ ≤ |C| := le_abs_self C
    have hs : (b.repr v i) ^ 2 ≤ |C| / Q (b i) :=
      (le_div_iff₀ (hw i)).2 (by nlinarith [hterm])
    have habs : |b.repr v i| ≤ (b.repr v i) ^ 2 + 1 := by
      have ha := sq_nonneg (|b.repr v i| - 1)
      nlinarith [sq_abs (b.repr v i), sq_nonneg (b.repr v i)]
    dsimp [K]
    linarith
  have hrepr : v j = ∑ i, b.repr v i * b i j := by
    have h := congrFun (b.sum_repr v) j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  have hj : |(x j : ℚ)| ≤ (R : ℚ) := by
    calc
      |(x j : ℚ)| = |∑ i, b.repr v i * b i j| := congrArg abs hrepr
      _ ≤ ∑ i, |b.repr v i * b i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ T j := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
      _ ≤ ∑ k, T k := Finset.single_le_sum (fun k _ => hT k) (Finset.mem_univ j)
      _ ≤ (R : ℚ) := le_of_lt hR
  have hbounds := abs_le.mp hj
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

theorem bounded_shell_finite :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      ∀ C : ℚ, Set.Finite {x : Fin n → ℤ | Q (fun i => (x i : ℚ)) ≤ C} := by
  intro n Q hQ C
  obtain ⟨R, hR⟩ := coordinate_box_bound n Q hQ C
  have hbox : Set.Finite {x : Fin n → ℤ | ∀ i, x i ∈ Set.Icc (-(R : ℤ)) (R : ℤ)} :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  exact hbox.subset (fun x hx i => hR x hx i)

theorem exact_shell_finite :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      ∀ C : ℚ, Set.Finite {x : Fin n → ℤ | Q (fun i => (x i : ℚ)) = C} := by
  intro n Q hQ C
  exact (bounded_shell_finite n Q hQ C).subset (fun _ hx => le_of_eq hx)

end ArithmeticThetaLattice
