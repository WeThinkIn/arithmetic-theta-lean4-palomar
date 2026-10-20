module

public import BinaryDefinitions
public import Det80ReducedClassification

@[expose] public section

/-! Exact minima and similarity rigidity for the three determinant-80 forms.
The imported support snapshots are immutable; only this module is owned by proof_4. -/

namespace ArithmeticThetaBinary

theorem actual_minima : ∀ j : Fin 3,
    (∀ x : Fin 2 → ℤ, x ≠ 0 → (![1,3,4] : Fin 3 → ℤ) j ≤ value j x) ∧
    ∃ x : Fin 2 → ℤ, x ≠ 0 ∧ value j x = (![1,3,4] : Fin 3 → ℤ) j := by
  intro j
  have nz (x : Fin 2 → ℤ) (hx : x ≠ 0) : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp_all
  have sqone (z : ℤ) (hz : z ≠ 0) : 1 ≤ z ^ 2 := by
    have : z ≤ -1 ∨ 1 ≤ z := by omega
    rcases this with h | h <;> nlinarith
  fin_cases j
  all_goals
    constructor
    · intro x hx
      have hh := nz x hx
      norm_num [value]
      by_cases hy : x 1 = 0
      · have hx0 : x 0 ≠ 0 := hh.resolve_right (not_not.mpr hy)
        have hsq := sqone _ hx0
        simp only [hy, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
        nlinarith
      · have hsq := sqone _ hy
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 + x 1)]
    · refine ⟨![1,0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        norm_num at this
      · norm_num [value]

end ArithmeticThetaBinary

namespace ArithmeticThetaBinary

lemma forms_det (j : Fin 3) : (forms j).det = 80 := by
  fin_cases j <;> norm_num [forms, gram, Matrix.det_fin_two]

theorem similarity_scale (i j : Fin 3) (s : ℚ) (hs : 0 < s)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hu : IsUnit U.det)
    (h : (U.map (Int.castRingHom ℚ)).transpose *
      (forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) =
        s • (forms j).map (Int.castRingHom ℚ)) : s = 1 := by
  have hd := congrArg Matrix.det h
  have hu2 : U.det = 1 ∨ U.det = -1 := Int.isUnit_iff.mp hu
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul,
    Fintype.card_fin] at hd
  simp only [Int.coe_castRingHom, ← Int.cast_det, forms_det] at hd
  rcases hu2 with hu | hu <;> rw [hu] at hd <;> norm_num at hd <;> rcases hd with hd | hd <;> linarith

lemma value_gram (j : Fin 3) (x : Fin 2 → ℤ) :
    dotProduct x ((forms j).mulVec x) = 2 * value j x := by
  fin_cases j <;> simp [forms, gram, value, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two] <;> ring

lemma integral_congruence (i j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (U.map (Int.castRingHom ℚ)).transpose *
      (forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) =
        (forms j).map (Int.castRingHom ℚ)) :
    U.transpose * forms i * U = forms j := by
  apply Matrix.map_injective (Int.cast_injective (α := ℚ))
  change (U.transpose * forms i * U).map (Int.castRingHom ℚ) =
    (forms j).map (Int.castRingHom ℚ)
  simpa only [Matrix.map_mul, Matrix.transpose_map] using h

lemma congruence_value (i j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ)
    (h : U.transpose * forms i * U = forms j) (x : Fin 2 → ℤ) :
    value i (U.mulVec x) = value j x := by
  have hv := congrArg (fun M => dotProduct x (M.mulVec x)) h
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at hv
  rw [value_gram, value_gram] at hv
  omega

theorem similarity_distinct (i j : Fin 3) (hij : i ≠ j) :
    ¬ ∃ (s : ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ), 0 < s ∧ IsUnit U.det ∧
      (U.map (Int.castRingHom ℚ)).transpose * (forms i).map (Int.castRingHom ℚ) *
        U.map (Int.castRingHom ℚ) = s • (forms j).map (Int.castRingHom ℚ) := by
  rintro ⟨s,U,hs,hu,h⟩
  have hs1 := similarity_scale i j s hs U hu h
  subst s
  rw [one_smul] at h
  have hc := integral_congruence i j U h
  have hui : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr hu
  have hinj := Matrix.mulVec_injective_of_isUnit hui
  have hsur := Matrix.mulVec_surjective_iff_isUnit.mpr hui
  obtain ⟨x,hx,hxmin⟩ := (actual_minima j).2
  have hux : U.mulVec x ≠ 0 := by
    intro hz
    apply hx
    apply hinj
    simpa using hz
  have hle := (actual_minima i).1 _ hux
  rw [congruence_value i j U hc, hxmin] at hle
  obtain ⟨y,hy,hymin⟩ := (actual_minima i).2
  obtain ⟨z,hz⟩ := hsur y
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [Matrix.mulVec_zero] at hz
    exact hy hz.symm
  have hge := (actual_minima j).1 z hz0
  have hval := congruence_value i j U hc z
  rw [hz, hymin] at hval
  rw [← hval] at hge
  fin_cases i <;> fin_cases j <;> simp_all

end ArithmeticThetaBinary
