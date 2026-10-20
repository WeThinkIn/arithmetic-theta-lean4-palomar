module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace ArithmeticThetaLinearAlgebra

theorem rational_matrix_rank (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    (A.map (algebraMap ℚ ℂ)).rank = A.rank := by
  classical
  let C := A.map (algebraMap ℚ ℂ)
  apply Nat.le_antisymm
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ C.col
    let : Fintype κ := Fintype.ofInjective a ha
    have hq : LinearIndependent ℚ (A.col ∘ a) := by
      exact (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
        (v := A.col ∘ a)).mp hli
    calc
      C.rank = Module.finrank ℂ (Submodule.span ℂ (Set.range (C.col ∘ a))) := by
        rw [Matrix.rank_eq_finrank_span_cols, hspan]
      _ = Fintype.card κ := finrank_span_eq_card hli
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (A.col ∘ a))) :=
        (finrank_span_eq_card hq).symm
      _ ≤ A.rank := by
        rw [Matrix.rank_eq_finrank_span_cols]
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨a i, rfl⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ A.col
    let : Fintype κ := Fintype.ofInjective a ha
    have hc : LinearIndependent ℂ (C.col ∘ a) := by
      exact (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
        (v := A.col ∘ a)).mpr hli
    calc
      A.rank = Module.finrank ℚ (Submodule.span ℚ (Set.range (A.col ∘ a))) := by
        rw [Matrix.rank_eq_finrank_span_cols, hspan]
      _ = Fintype.card κ := finrank_span_eq_card hli
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (C.col ∘ a))) :=
        (finrank_span_eq_card hc).symm
      _ ≤ C.rank := by
        rw [Matrix.rank_eq_finrank_span_cols]
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨a i, rfl⟩

private theorem cast_mulVec (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ)
    (v : Fin h → ℚ) :
    (A.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun a => (A.mulVec v a : ℂ) := by
  ext a
  simp [Matrix.mulVec, dotProduct]

private theorem cast_kernel_span_le (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    Submodule.span ℂ ((fun v : Fin h → ℚ => fun j => (v j : ℂ)) ''
      {v : Fin h → ℚ | A.mulVec v = 0}) ≤
      LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change (A.map (algebraMap ℚ ℂ)).mulVec (fun j => (v j : ℂ)) = 0
  rw [cast_mulVec, hv]
  ext j
  simp

private theorem rational_nullity (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    Module.finrank ℚ (LinearMap.ker A.mulVecLin) = h - A.rank := by
  have hn := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + Module.finrank ℚ (LinearMap.ker A.mulVecLin) = _ at hn
  simp only [Module.finrank_pi, Fintype.card_fin] at hn
  omega

private theorem complex_nullity_from_rank (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ)
    (hr : (A.map (algebraMap ℚ ℂ)).rank = A.rank) :
    Module.finrank ℂ (LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin) = h - A.rank := by
  have hn := (A.map (algebraMap ℚ ℂ)).mulVecLin.finrank_range_add_finrank_ker
  change (A.map (algebraMap ℚ ℂ)).rank +
    Module.finrank ℂ (LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin) = _ at hn
  rw [hr] at hn
  simp only [Module.finrank_pi, Fintype.card_fin] at hn
  omega

theorem rational_matrix_kernel_span (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin =
      Submodule.span ℂ ((fun v : Fin h → ℚ => fun j => (v j : ℂ)) ''
        {v : Fin h → ℚ | A.mulVec v = 0}) := by
  classical
  let K := LinearMap.ker A.mulVecLin
  let b := Module.finBasis ℚ K
  let v := fun i => (b i : Fin h → ℚ)
  have hv : LinearIndependent ℚ v :=
    b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  have hc : LinearIndependent ℂ (fun i => fun j => (v i j : ℂ)) := by
    simpa [Function.comp_def] using
      (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ) (v := v)).mpr hv
  have hs : Submodule.span ℂ (Set.range (fun i => fun j => (v i j : ℂ))) ≤
      Submodule.span ℂ ((fun v : Fin h → ℚ => fun j => (v j : ℂ)) ''
        {v : Fin h → ℚ | A.mulVec v = 0}) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, (b i).property, rfl⟩
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le (cast_kernel_span_le m h A)
  calc
    Module.finrank ℂ (LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin)
        = Module.finrank ℚ K := by
          rw [complex_nullity_from_rank m h A (rational_matrix_rank m h A),
            rational_nullity m h A]
    _ = Module.finrank ℂ (Submodule.span ℂ
        (Set.range (fun i => fun j => (v i j : ℂ)))) := by
          rw [finrank_span_eq_card hc, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hs

theorem rational_matrix_nullity (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    Module.finrank ℂ (LinearMap.ker (A.map (algebraMap ℚ ℂ)).mulVecLin) = h - A.rank := by
  exact complex_nullity_from_rank m h A (rational_matrix_rank m h A)

end ArithmeticThetaLinearAlgebra
