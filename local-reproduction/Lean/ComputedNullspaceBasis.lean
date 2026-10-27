import EliminationReduction

namespace ArithmeticThetaElimination

lemma mem_free_iff {m h : ℕ} (s : State m h) (j : Fin h) :
    j ∈ freeColumns s ↔ j ∉ pivotColumns s := by
  simp [freeColumns]

lemma pivot_column_mem {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (t : Fin (run A).pivots.length) : ((run A).pivots.get t).2 ∈ pivotColumns (run A) := by
  exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩

lemma free_columns_injective {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Function.Injective (freeColumns (run A)).get := by
  apply List.nodup_iff_injective_get.mp
  exact (List.nodup_finRange h).filter _

lemma free_ne_pivot {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f : Fin (freeColumns (run A)).length) (t : Fin (run A).pivots.length) :
    (freeColumns (run A)).get f ≠ ((run A).pivots.get t).2 := by
  have hf := (mem_free_iff _ _).mp (List.get_mem _ f)
  intro he
  exact hf (he ▸ pivot_column_mem A t)

def columnIndex {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Fin (run A).pivots.length ⊕ Fin (freeColumns (run A)).length → Fin h :=
  Sum.elim (fun t => ((run A).pivots.get t).2) (freeColumns (run A)).get

lemma columnIndex_bijective {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Function.Bijective (columnIndex A) := by
  constructor
  · intro x y he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl ((run_pivot_metadata m h A).2.2.1.injective he)
    · exact (free_ne_pivot A y x he.symm).elim
    · exact (free_ne_pivot A x y he).elim
    · exact congrArg Sum.inr (free_columns_injective A he)
  · intro j
    by_cases hj : j ∈ pivotColumns (run A)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      obtain ⟨t, rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨Sum.inl t, rfl⟩
    · have hf := (mem_free_iff (run A) j).mpr hj
      obtain ⟨f, rfl⟩ := List.mem_iff_get.mp hf
      exact ⟨Sum.inr f, rfl⟩

lemma column_sum_partition {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (g : Fin h → ℚ) :
    ∑ j : Fin h, g j =
      (∑ t : Fin (run A).pivots.length, g (((run A).pivots.get t).2)) +
      ∑ f : Fin (freeColumns (run A)).length, g ((freeColumns (run A)).get f) := by
  let e := Equiv.ofBijective (columnIndex A) (columnIndex_bijective A)
  have he := e.sum_comp g
  simpa [e, columnIndex, Fintype.sum_sum_type] using he.symm

lemma pivotRow_recorded {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (t : Fin (run A).pivots.length) :
    pivotRow (run A) (((run A).pivots.get t).2) = some (((run A).pivots.get t).1) := by
  have hf : (run A).pivots.find? (fun p => p.2 == ((run A).pivots.get t).2) =
      some ((run A).pivots.get t) := by
    apply find_unique _ _ _ (List.get_mem _ _)
    · simp
    · intro p hp he
      obtain ⟨u, rfl⟩ := List.mem_iff_get.mp hp
      have heq : ((run A).pivots.get u).2 = ((run A).pivots.get t).2 := by simpa using he
      exact congrArg (run A).pivots.get ((run_pivot_metadata m h A).2.2.1.injective heq)
  simp only [pivotRow, hf, Option.map_some]

lemma pivotRow_free {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f : Fin (freeColumns (run A)).length) :
    pivotRow (run A) ((freeColumns (run A)).get f) = none := by
  have hf := (mem_free_iff _ _).mp (List.get_mem (freeColumns (run A)) f)
  have hn : (run A).pivots.find? (fun p => p.2 == (freeColumns (run A)).get f) = none := by
    rw [List.find?_eq_none]
    intro p hp he
    apply hf
    exact List.mem_map.mpr ⟨p, hp, by simpa using he⟩
  simp only [pivotRow, hn, Option.map_none]

lemma nullBasis_free_entry {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f g : Fin (freeColumns (run A)).length) :
    nullBasis A f ((freeColumns (run A)).get g) = if g = f then 1 else 0 := by
  simp only [nullBasis, nullVector, pivotRow_free]
  simp only [(free_columns_injective A).eq_iff]

lemma nullBasis_pivot_entry {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f : Fin (freeColumns (run A)).length) (t : Fin (run A).pivots.length) :
    nullBasis A f (((run A).pivots.get t).2) =
      -(run A).reduced (((run A).pivots.get t).1) ((freeColumns (run A)).get f) := by
  simp only [nullBasis, nullVector, if_neg (free_ne_pivot A f t).symm, pivotRow_recorded]

lemma reduced_pivot_row_equation {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (v : Fin h → ℚ) (t : Fin (run A).pivots.length) :
    (run A).reduced.mulVec v (((run A).pivots.get t).1) =
      v (((run A).pivots.get t).2) +
      ∑ f : Fin (freeColumns (run A)).length,
        (run A).reduced (((run A).pivots.get t).1) ((freeColumns (run A)).get f) *
          v ((freeColumns (run A)).get f) := by
  change (∑ j, (run A).reduced (((run A).pivots.get t).1) j * v j) = _
  rw [column_sum_partition A]
  simp only [reduced_pivot_column, (pivot_rows_injective A).eq_iff]
  simp

lemma nullBasis_reduced_kernel {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f : Fin (freeColumns (run A)).length) : (run A).reduced.mulVec (nullBasis A f) = 0 := by
  ext i
  by_cases hi : i.val < (run A).nextRow
  · have ht : i.val < (run A).pivots.length := by rwa [(run_pivot_metadata m h A).1] at hi
    let t : Fin (run A).pivots.length := ⟨i.val, ht⟩
    have hti : ((run A).pivots.get t).1 = i := Fin.ext ((run_pivot_metadata m h A).2.2.2 t)
    rw [← hti, reduced_pivot_row_equation]
    simp only [nullBasis_pivot_entry, nullBasis_free_entry]
    simp
  · have hz : (run A).reduced i = 0 := by
      ext j
      exact (run_rowInvariant A).2.2 i (by omega) j j.isLt
    change (run A).reduced i ⬝ᵥ nullBasis A f = 0
    rw [hz]
    simp

lemma nullBasis_kernel {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (f : Fin (freeColumns (run A)).length) : A.mulVec (nullBasis A f) = 0 := by
  have hh : nullBasis A f ∈ LinearMap.ker (run A).reduced.mulVecLin := nullBasis_reduced_kernel A f
  rw [(run_kernel_rank m h A).1] at hh
  exact hh

end ArithmeticThetaElimination

namespace ArithmeticThetaElimination

lemma reduced_kernel_reconstruction {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (v : Fin h → ℚ) (hv : (run A).reduced.mulVec v = 0) :
    v = ∑ f : Fin (freeColumns (run A)).length,
      v ((freeColumns (run A)).get f) • nullBasis A f := by
  ext j
  obtain ⟨u, rfl⟩ := (columnIndex_bijective A).2 j
  rcases u with t | g
  · change v (((run A).pivots.get t).2) =
      (∑ f, v ((freeColumns (run A)).get f) • nullBasis A f) (((run A).pivots.get t).2)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, nullBasis_pivot_entry]
    have hrow := congrFun hv (((run A).pivots.get t).1)
    change (run A).reduced.mulVec v (((run A).pivots.get t).1) = 0 at hrow
    rw [reduced_pivot_row_equation] at hrow
    have heq : (∑ f : Fin (freeColumns (run A)).length,
        v ((freeColumns (run A)).get f) *
          (-(run A).reduced (((run A).pivots.get t).1) ((freeColumns (run A)).get f))) =
        -(∑ f : Fin (freeColumns (run A)).length,
          (run A).reduced (((run A).pivots.get t).1) ((freeColumns (run A)).get f) *
            v ((freeColumns (run A)).get f)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro f _
      ring
    rw [heq]
    linarith
  · change v ((freeColumns (run A)).get g) =
      (∑ f, v ((freeColumns (run A)).get f) • nullBasis A f) ((freeColumns (run A)).get g)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, nullBasis_free_entry]
    simp

lemma computed_nullspace_independent {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearIndependent ℚ (nullBasis A) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz f
  have he := congrFun hz ((freeColumns (run A)).get f)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, nullBasis_free_entry, Pi.zero_apply] at he
  simpa using he

theorem computed_nullspace_basis (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearIndependent ℚ (nullBasis A) ∧
    Submodule.span ℚ (Set.range (nullBasis A)) = LinearMap.ker A.mulVecLin ∧
    (freeColumns (run A)).length = h - A.rank := by
  refine ⟨computed_nullspace_independent A, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      obtain ⟨f, rfl⟩ := hv
      exact nullBasis_kernel A f
    · intro v hv
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun f => v ((freeColumns (run A)).get f), ?_⟩
      have hred : (run A).reduced.mulVec v = 0 := by
        have hh : v ∈ LinearMap.ker A.mulVecLin := hv
        rw [← (run_kernel_rank m h A).1] at hh
        exact hh
      exact (reduced_kernel_reconstruction A v hred).symm
  · let e := Equiv.ofBijective (columnIndex A) (columnIndex_bijective A)
    have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hr := (run_kernel_rank m h A).2
    omega

theorem computed_nullspace_reconstruction (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ)
    (v : Fin h → ℚ) : A.mulVec v = 0 ↔
      v = ∑ f : Fin (freeColumns (run A)).length,
        v ((freeColumns (run A)).get f) • nullBasis A f := by
  constructor
  · intro hv
    apply reduced_kernel_reconstruction A v
    have hh : v ∈ LinearMap.ker A.mulVecLin := hv
    rw [← (run_kernel_rank m h A).1] at hh
    exact hh
  · intro hv
    rw [hv, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, nullBasis_kernel]
    simp

end ArithmeticThetaElimination
