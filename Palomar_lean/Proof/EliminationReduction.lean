module

public import EliminationPrimitives
public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

@[expose] public section

namespace ArithmeticThetaElimination

lemma step_transformation {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (s : State m h) (c : Fin h)
    (hi : s.reduced = s.transform * A ∧ IsUnit s.transform.det) :
    (step s c).reduced = (step s c).transform * A ∧ IsUnit (step s c).transform.det := by
  by_cases hr : s.nextRow < m
  · cases hf : findPivot s.reduced s.nextRow c with
    | none => simpa [step, hr, hf] using hi
    | some t =>
      have hp := ((find_pivot_correct m h s.reduced s.nextRow c).2 t hf).2.1
      have he := pivot_operation_correct m h s.reduced ⟨s.nextRow, hr⟩ t c hp
      simp only [step, dif_pos hr, hf]
      constructor
      · rw [he.2.1 h s.reduced, he.2.1 m s.transform, hi.1, Matrix.mul_assoc]
      · rw [pivotOperation_left, Matrix.det_mul]
        exact he.1.mul hi.2
  · simpa [step, hr] using hi

lemma fold_transformation {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (l : List (Fin h)) (s : State m h)
    (hi : s.reduced = s.transform * A ∧ IsUnit s.transform.det) :
    (l.foldl step s).reduced = (l.foldl step s).transform * A ∧
      IsUnit (l.foldl step s).transform.det := by
  induction l generalizing s with
  | nil => exact hi
  | cons c l ih => exact ih (step s c) (step_transformation A s c hi)

theorem run_transformation (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    (run A).reduced = (run A).transform * A ∧ IsUnit (run A).transform.det := by
  apply fold_transformation
  simp [initial]

-- Metadata tracks the concrete list, its row indices, and its strict column ordering.
def Metadata {m h : ℕ} (s : State m h) (c : ℕ) : Prop :=
  s.nextRow = s.pivots.length ∧ s.nextRow ≤ m ∧
  (∀ t : Fin s.pivots.length, (s.pivots.get t).1.val = t.val) ∧
  s.pivots.Pairwise (fun p q => p.2 < q.2) ∧
  ∀ p ∈ s.pivots, p.2.val < c

lemma metadata_weaken {m h : ℕ} {s : State m h} {c d : ℕ}
    (hs : Metadata s c) (hcd : c ≤ d) : Metadata s d := by
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    fun p hp => lt_of_lt_of_le (hs.2.2.2.2 p hp) hcd⟩

lemma metadata_append {m h : ℕ} (s : State m h) (c : Fin h)
    (hs : Metadata s c.val) (hr : s.nextRow < m)
    (R : Matrix (Fin m) (Fin h) ℚ) (U : Matrix (Fin m) (Fin m) ℚ) :
    Metadata (⟨R, U, s.nextRow + 1, s.pivots ++ [(⟨s.nextRow, hr⟩, c)]⟩ : State m h)
      (c.val + 1) := by
  dsimp only [Metadata]
  rcases hs with ⟨hlen, hbound, hrows, hpair, hcols⟩
  refine ⟨by simp [hlen], by omega, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t.val < s.pivots.length
    · have hh := hrows ⟨t.val, ht⟩
      simpa [List.get_eq_getElem, List.getElem_append, ht] using hh
    · have htv : t.val = s.pivots.length := by
        have := t.isLt
        simp only [List.length_append, List.length_singleton] at this
        omega
      simp [List.get_eq_getElem, htv, hlen]
  · simp only [List.pairwise_append, List.pairwise_singleton]
    refine ⟨hpair, trivial, ?_⟩
    intro p hp q hq
    simp only [List.mem_singleton] at hq
    subst q
    exact hcols p hp
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact Nat.lt_succ_of_lt (hcols p hp)
    · simp

lemma step_metadata {m h : ℕ} (s : State m h) (c : Fin h)
    (hs : Metadata s c.val) : Metadata (step s c) (c.val + 1) := by
  by_cases hr : s.nextRow < m
  · cases hf : findPivot s.reduced s.nextRow c with
    | none => simpa [step, hr, hf] using metadata_weaken hs (Nat.le_succ _)
    | some t =>
      simpa only [step, dif_pos hr, hf] using
        metadata_append s c hs hr (pivotOperation s.reduced s.reduced ⟨s.nextRow, hr⟩ t c)
          (pivotOperation s.reduced s.transform ⟨s.nextRow, hr⟩ t c)
  · simpa [step, hr] using metadata_weaken hs (Nat.le_succ _)

def runPrefix {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (c : ℕ) : State m h :=
  ((List.finRange h).take c).foldl step (initial A)

lemma runPrefix_succ {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (c : ℕ) (hc : c < h) :
    runPrefix A (c + 1) = step (runPrefix A c) ⟨c, hc⟩ := by
  have ht := List.take_concat_get' (List.finRange h) c (by simpa using hc)
  simp only [runPrefix]
  rw [← ht, List.foldl_append]
  simp

lemma prefix_metadata {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (c : ℕ) (hc : c ≤ h) :
    Metadata (runPrefix A c) c := by
  induction c with
  | zero => simp [Metadata, runPrefix, initial]
  | succ c ih =>
    have hch : c < h := by omega
    rw [runPrefix_succ A c hch]
    exact step_metadata _ ⟨c, hch⟩ (ih (by omega))

lemma run_eq_prefix {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) : run A = runPrefix A h := by
  simp only [run, runPrefix]
  rw [List.take_of_length_le (by simp)]

theorem run_pivot_metadata (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    (run A).nextRow = (run A).pivots.length ∧ (run A).pivots.length ≤ m ∧
    StrictMono (fun t : Fin (run A).pivots.length => ((run A).pivots.get t).2) ∧
    ∀ t : Fin (run A).pivots.length, ((run A).pivots.get t).1.val = t.val := by
  have hm : Metadata (run A) h := by rw [run_eq_prefix]; exact prefix_metadata A h (le_refl h)
  refine ⟨hm.1, hm.1 ▸ hm.2.1, ?_, hm.2.2.1⟩
  intro i j hij
  exact hm.2.2.2.1.rel_get_of_lt hij

end ArithmeticThetaElimination

namespace ArithmeticThetaElimination

lemma pivotOperation_preserve_column {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) (c : Fin h) (j : Fin k)
    (hr : N r j = 0) (hs : N s j = 0) (i : Fin m) :
    pivotOperation M N r s c i j = N i j := by
  by_cases hir : i = r <;> by_cases his : i = s <;>
    simp_all [pivotOperation, swapRows]

def RowInvariant {m h : ℕ} (s : State m h) (c : ℕ) : Prop :=
  (∀ p ∈ s.pivots, ∀ i, s.reduced i p.2 = if i = p.1 then 1 else 0) ∧
  (∀ p ∈ s.pivots, ∀ j, j < p.2 → s.reduced p.1 j = 0) ∧
  ∀ i, s.nextRow ≤ i.val → ∀ j, j.val < c → s.reduced i j = 0

lemma step_rowInvariant {m h : ℕ} (s : State m h) (c : Fin h)
    (hm : Metadata s c.val) (hi : RowInvariant s c.val) :
    RowInvariant (step s c) (c.val + 1) := by
  by_cases hr : s.nextRow < m
  · cases hf : findPivot s.reduced s.nextRow c with
    | none =>
      have hz := (find_pivot_correct m h s.reduced s.nextRow c).1.mp hf
      simp only [step, dif_pos hr, hf]
      refine ⟨hi.1, hi.2.1, ?_⟩
      intro i hri j hj
      by_cases hjc : j = c
      · subst j
        exact hz i hri
      · apply hi.2.2 i hri j
        have hne : j.val ≠ c.val := fun hh => hjc (Fin.ext hh)
        omega
    | some t =>
      have hs := (find_pivot_correct m h s.reduced s.nextRow c).2 t hf
      have hunit := (pivot_operation_correct m h s.reduced ⟨s.nextRow, hr⟩ t c hs.2.1).2.2
      have hpres (i : Fin m) (j : Fin h) (hj : j.val < c.val) :
          pivotOperation s.reduced s.reduced ⟨s.nextRow, hr⟩ t c i j = s.reduced i j :=
        pivotOperation_preserve_column s.reduced s.reduced ⟨s.nextRow, hr⟩ t c j
          (hi.2.2 _ (le_refl _) j hj) (hi.2.2 t hs.1 j hj) i
      simp only [step, dif_pos hr, hf]
      dsimp only [RowInvariant]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp i
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · rw [hpres i p.2 (hm.2.2.2.2 p hp)]
          exact hi.1 p hp i
        · exact hunit i
      · intro p hp j hj
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · rw [hpres p.1 j (lt_trans hj (hm.2.2.2.2 p hp))]
          exact hi.2.1 p hp j hj
        · rw [hpres _ j hj]
          exact hi.2.2 _ (le_refl _) j hj
      · intro i hri j hj
        by_cases hjc : j = c
        · subst j
          rw [hunit]
          have hne : i ≠ ⟨s.nextRow, hr⟩ := by intro heq; subst i; simp at hri
          simp [hne]
        · have hne : j.val ≠ c.val := fun hh => hjc (Fin.ext hh)
          have hjlt : j.val < c.val := by omega
          rw [hpres i j hjlt]
          exact hi.2.2 i (by omega) j hjlt
  · simp only [step, dif_neg hr]
    refine ⟨hi.1, hi.2.1, ?_⟩
    intro i hri j hj
    have := i.isLt
    omega

lemma prefix_rowInvariant {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (c : ℕ) (hc : c ≤ h) :
    RowInvariant (runPrefix A c) c := by
  induction c with
  | zero =>
    simp only [runPrefix, List.take_zero, List.foldl_nil, RowInvariant, initial,
      List.not_mem_nil, false_implies, implies_true, true_and]
    intro i hi j hj
    omega
  | succ c ih =>
    have hch : c < h := by omega
    rw [runPrefix_succ A c hch]
    exact step_rowInvariant _ ⟨c, hch⟩ (prefix_metadata A c (by omega)) (ih (by omega))

lemma run_rowInvariant {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    RowInvariant (run A) h := by
  rw [run_eq_prefix]
  exact prefix_rowInvariant A h (le_refl h)

end ArithmeticThetaElimination

namespace ArithmeticThetaElimination

lemma find_unique {α : Type*} (l : List α) (p : α → Bool) (a : α)
    (ha : a ∈ l) (hpa : p a = true)
    (hu : ∀ b ∈ l, p b = true → b = a) : l.find? p = some a := by
  cases hf : l.find? p with
  | none => exact ((List.find?_eq_none.mp hf) a ha hpa).elim
  | some b => rw [hu b (List.mem_of_find?_eq_some hf) (List.find?_some hf)]

lemma metadata_row_lt {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (p : Fin m × Fin h) (hp : p ∈ s.pivots) : p.1.val < s.nextRow := by
  obtain ⟨t, rfl⟩ := List.mem_iff_get.mp hp
  rw [hm.2.2.1 t, hm.1]
  exact t.isLt

lemma metadata_row_unique {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (p q : Fin m × Fin h) (hp : p ∈ s.pivots) (hq : q ∈ s.pivots)
    (he : p.1 = q.1) : p = q := by
  obtain ⟨t, rfl⟩ := List.mem_iff_get.mp hp
  obtain ⟨u, rfl⟩ := List.mem_iff_get.mp hq
  have hv := congrArg Fin.val he
  rw [hm.2.2.1 t, hm.2.2.1 u] at hv
  exact congrArg s.pivots.get (Fin.ext hv)

lemma metadata_row_exists {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (i : Fin m) (hi : i.val < s.nextRow) :
    ∃ p ∈ s.pivots, p.1 = i := by
  have ht : i.val < s.pivots.length := by rwa [hm.1] at hi
  refine ⟨s.pivots.get ⟨i.val, ht⟩, List.get_mem _ _, ?_⟩
  apply Fin.ext
  exact hm.2.2.1 _

lemma pivotMap_recorded {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (p : Fin m × Fin h) (hp : p ∈ s.pivots) : pivotMap s p.1 = p.2 := by
  have hf : s.pivots.find? (fun q => q.1 == p.1) = some p := by
    apply find_unique _ _ _ hp
    · simp
    · intro q hq he
      exact metadata_row_unique hm q p hq hp (by simpa using he)
  simp [pivotMap, hf]

lemma pivotMap_unrecorded {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (i : Fin m) (hi : s.nextRow ≤ i.val) : pivotMap s i = ⊤ := by
  have hf : s.pivots.find? (fun p => p.1 == i) = none := by
    rw [List.find?_eq_none]
    intro p hp he
    have hpi : p.1 = i := by simpa using he
    have hlt := metadata_row_lt hm p hp
    rw [hpi] at hlt
    omega
  simp [pivotMap, hf]

lemma recorded_leading {m h : ℕ} {s : State m h} (hr : RowInvariant s h)
    (p : Fin m × Fin h) (hp : p ∈ s.pivots) : s.reduced.IsLeadingEntry p.1 p.2 := by
  refine ⟨hr.2.1 p hp, ?_⟩
  rw [hr.1 p hp]
  simp

lemma metadata_columns_lt {m h : ℕ} {s : State m h} {c : ℕ} (hm : Metadata s c)
    (p q : Fin m × Fin h) (hp : p ∈ s.pivots) (hq : q ∈ s.pivots)
    (hi : p.1 < q.1) : p.2 < q.2 := by
  obtain ⟨t, rfl⟩ := List.mem_iff_get.mp hp
  obtain ⟨u, rfl⟩ := List.mem_iff_get.mp hq
  apply hm.2.2.2.1.rel_get_of_lt
  have hv : (s.pivots.get t).1.val < (s.pivots.get u).1.val := hi
  rw [hm.2.2.1 t, hm.2.2.1 u] at hv
  exact hv

lemma invariant_row_echelon {m h : ℕ} {s : State m h}
    (hm : Metadata s h) (hr : RowInvariant s h) : s.reduced.IsRowEchelon := by
  intro i₁ i₂ hi j hz
  by_cases hi₂ : i₂.val < s.nextRow
  · obtain ⟨p₂, hp₂, he₂⟩ := metadata_row_exists hm i₂ hi₂
    obtain ⟨p₁, hp₁, he₁⟩ := metadata_row_exists hm i₁ (lt_trans hi hi₂)
    have hcols : p₁.2 < p₂.2 := metadata_columns_lt hm p₁ p₂ hp₁ hp₂ (by simpa [he₁, he₂] using hi)
    by_cases hj : j < p₂.2
    · simpa [he₂] using hr.2.1 p₂ hp₂ j hj
    · have hpj : p₁.2 < j := lt_of_lt_of_le hcols (le_of_not_gt hj)
      have hzero := hz p₁.2 hpj
      have hone := hr.1 p₁ hp₁ i₁
      simp [he₁, hzero] at hone
  · exact hr.2.2 i₂ (by omega) j j.isLt

lemma leading_recorded {m h : ℕ} {s : State m h}
    (hm : Metadata s h) (hr : RowInvariant s h) (i : Fin m) (c : Fin h)
    (hl : s.reduced.IsLeadingEntry i c) : ∃ p ∈ s.pivots, p.1 = i ∧ p.2 = c := by
  have hi : i.val < s.nextRow := by
    by_contra hni
    exact hl.2 (hr.2.2 i (by omega) c c.isLt)
  obtain ⟨p, hp, hpi⟩ := metadata_row_exists hm i hi
  refine ⟨p, hp, hpi, ?_⟩
  have hpLead := recorded_leading hr p hp
  rw [hpi] at hpLead
  exact hpLead.unique hl

lemma invariant_reduced_echelon {m h : ℕ} {s : State m h}
    (hm : Metadata s h) (hr : RowInvariant s h) :
    s.reduced.IsReducedRowEchelon ∧ s.reduced.IsPivotedBy (pivotMap s) := by
  have he := invariant_row_echelon hm hr
  constructor
  · refine ⟨he, ?_, ?_⟩
    · intro i c hl
      obtain ⟨p, hp, hpi, hpc⟩ := leading_recorded hm hr i c hl
      simpa [hpi, hpc] using hr.1 p hp i
    · intro i₁ i₂ c hi hl
      obtain ⟨p, hp, hpi, hpc⟩ := leading_recorded hm hr i₂ c hl
      simpa [hpi, hpc, ne_of_lt hi] using hr.1 p hp i₁
  · refine ⟨he, ?_⟩
    intro i
    by_cases hi : i.val < s.nextRow
    · obtain ⟨p, hp, hpi⟩ := metadata_row_exists hm i hi
      have hmap : pivotMap s i = p.2 := by rw [← hpi]; exact pivotMap_recorded hm p hp
      rw [hmap]
      constructor
      · intro j hj
        have hj' : j < p.2 := WithTop.coe_lt_coe.mp hj
        simpa [hpi] using hr.2.1 p hp j hj'
      · intro c hc
        have hpc : p.2 = c := WithTop.coe_injective hc
        have hone := hr.1 p hp i
        have hvalue : s.reduced i c = 1 := by simpa [hpi, hpc] using hone
        rw [hvalue]
        norm_num
    · rw [pivotMap_unrecorded hm i (by omega)]
      constructor
      · intro j _
        exact hr.2.2 i (by omega) j j.isLt
      · intro c hc
        exact (WithTop.top_ne_coe hc).elim

theorem run_reduced_echelon (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    (run A).reduced.IsReducedRowEchelon ∧ (run A).reduced.IsPivotedBy (pivotMap (run A)) := by
  apply invariant_reduced_echelon
  · rw [run_eq_prefix]
    exact prefix_metadata A h (le_refl h)
  · exact run_rowInvariant A

end ArithmeticThetaElimination

namespace ArithmeticThetaElimination

lemma pivotMap_ne_top_iff {m h : ℕ} {s : State m h} {c : ℕ}
    (hm : Metadata s c) (i : Fin m) : pivotMap s i ≠ ⊤ ↔ i.val < s.nextRow := by
  constructor
  · intro hn
    by_contra hi
    exact hn (pivotMap_unrecorded hm i (by omega))
  · intro hi
    obtain ⟨p, hp, hpi⟩ := metadata_row_exists hm i hi
    rw [← hpi, pivotMap_recorded hm p hp]
    exact WithTop.coe_ne_top

lemma finite_initial_segment_card (m r : ℕ) (hr : r ≤ m) :
    (Finset.univ.filter (fun i : Fin m => i.val < r)).card = r := by
  let e : {i : Fin m // i.val < r} ≃ Fin r :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hr⟩, i.isLt⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  have he := Fintype.card_congr e
  simpa [Fintype.card_subtype] using he

theorem run_kernel_rank (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearMap.ker (run A).reduced.mulVecLin = LinearMap.ker A.mulVecLin ∧
      (run A).pivots.length = A.rank := by
  have ht := run_transformation m h A
  have hm : Metadata (run A) h := by rw [run_eq_prefix]; exact prefix_metadata A h (le_refl h)
  constructor
  · have hinj := Matrix.mulVec_injective_of_isUnit
      ((run A).transform.isUnit_iff_isUnit_det.mpr ht.2)
    ext v
    change (run A).reduced.mulVec v = 0 ↔ A.mulVec v = 0
    rw [ht.1, ← Matrix.mulVec_mulVec]
    constructor
    · intro hv
      apply hinj
      simpa using hv
    · intro hv
      simp [hv]
  · have hrank := (run_reduced_echelon m h A).2.rank_eq
    have hcard : (Finset.univ.filter (fun i : Fin m => pivotMap (run A) i ≠ ⊤)).card =
        (run A).nextRow := by
      simp_rw [pivotMap_ne_top_iff hm]
      exact finite_initial_segment_card m _ hm.2.1
    rw [hcard] at hrank
    have hArank : (run A).reduced.rank = A.rank := by
      rw [ht.1]
      exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ht.2
    have hlen := hm.1
    omega

end ArithmeticThetaElimination

namespace ArithmeticThetaElimination

lemma pivot_rows_injective {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Function.Injective (fun t : Fin (run A).pivots.length => ((run A).pivots.get t).1) := by
  intro t u he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa only [(run_pivot_metadata m h A).2.2.2 t, (run_pivot_metadata m h A).2.2.2 u] using hv

lemma reduced_pivot_column {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (t : Fin (run A).pivots.length) (i : Fin m) :
    (run A).reduced i (((run A).pivots.get t).2) =
      if i = ((run A).pivots.get t).1 then 1 else 0 :=
  (run_rowInvariant A).1 _ (List.get_mem _ _) i


end ArithmeticThetaElimination
