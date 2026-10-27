import ComputedSharpCutoffR0230
import CappedDoublingScheduleR0230
import ExecutableRelationCertificateR0230
import CheckedBasisChangeRelationsR0230

/-! Successful adaptive execution, first-certified stopping, and the internally
checked input interface. All correctness data refer to the returned LDL matrix. -/
set_option autoImplicit false

namespace ArithmeticThetaAdaptiveSolverR0230
namespace AdaptiveUniversalSolver

private theorem find_before {p : ℕ → Bool} {xs : List ℕ} {B : ℕ}
    (hs : xs.Pairwise (fun a b => a < b)) (hf : xs.find? p = some B) :
    ∀ b ∈ xs, b < B → p b = false := by
  induction xs with
  | nil => simp at hf
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hs
    by_cases hp : p a = true
    · have he : a = B := by simpa [hp] using hf
      subst B
      intro b hb hlt
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := ha b hb
        omega
    · have hf' : xs.find? p = some B := by simpa [hp] using hf
      intro b hb hlt
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Bool.eq_false_iff.mpr hp
      · exact ih ht hf' b hb hlt

private theorem sharp_correct {n h : ℕ} (A : Matrices n h)
    (hv : ∀ i, ArithmeticThetaComputed.validGram (A i)) (hh : 0 < h)
    (B : ℕ) (hb : ArithmeticThetaSharpKernelR0195.cutoff A ≤ B) :
    Correct A (assemble A B) := by
  have he := (ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix
    n h B A hv).1
  have hk := (ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel n h hh A hv).1
    B hb
  have hd := ArithmeticThetaSharpKernelR0195.sharp_exact_image_data n h hh A hv
    B hb
  dsimp [Correct, assemble, nullVectors, pivotIndices, coordinates]
  rw [he]
  exact ⟨rfl, hk, hd⟩

end AdaptiveUniversalSolver

open AdaptiveUniversalSolver in
theorem adaptive_universal_solver :
    ∀ (n h d : ℕ) (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) → Relations A R → 0 < h →
      ∃ o : Result h, solve A R = some o ∧ o.cutoff ≤ bound A ∧ Correct A o ∧
        o.cutoff ∈ schedule (bound A) ∧
        (o.cutoff = bound A ∨ early A R o.cutoff = true) ∧
        ∀ b ∈ schedule (bound A), b < o.cutoff → early A R b = false := by
  intro n h d A R hv hR hh
  obtain ⟨_, ⟨xs, hx⟩, hs, hr, _⟩ := capped_doubling_schedule (bound A)
  have hcap : bound A ∈ schedule (bound A) := by simp [hx]
  let p : ℕ → Bool := fun B => early A R B || B == bound A
  have hfind : ∃ B, (schedule (bound A)).find? p = some B := by
    cases he : (schedule (bound A)).find? p with
    | none =>
      have hn := List.find?_eq_none.mp he (bound A) hcap
      simp [p] at hn
    | some B => exact ⟨B, rfl⟩
  obtain ⟨B, hB⟩ := hfind
  have hmem := List.mem_of_find?_eq_some hB
  have hgate : early A R B = true ∨ B = bound A := by
    simpa only [p, Bool.or_eq_true, beq_iff_eq] using List.find?_some hB
  refine ⟨assemble A B, ?_, hr B hmem, ?_, hmem, hgate.symm, ?_⟩
  · simp only [solve]
    rw [hB]
    rfl
  · rcases hgate with he | rfl
    · apply (executable_relation_certificate n h d A R hv hR B).2.1
      simp [certify, he]
    · exact sharp_correct A hv hh (bound A) (computed_sharp_cutoff n h A hv).1.ge
  · intro b hb hlt
    have hf := find_before hs hB b hb hlt
    exact (Bool.or_eq_false_iff.mp hf).1

theorem adaptive_checked_input :
    ∀ (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) → 0 < h →
      ∀ cs : List (Change n h), ∃ o : Result h,
        solveChanges A cs = some o ∧ o.cutoff ≤ bound A ∧ Correct A o := by
  intro n h A hv hh cs
  obtain ⟨o, ho, hb, hc, _⟩ := adaptive_universal_solver n h cs.length A
    (changeRelations A cs) hv (checked_basis_change_relations n h A hv cs) hh
  exact ⟨o, ho, hb, hc⟩

namespace AdaptiveUniversalSolver

private theorem singleton_early {n d : ℕ} (A : Matrices n 1)
    (hv : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (R : Matrix (Fin 1) (Fin d) ℚ) : early A R 0 = true := by
  have hc : PowerSeries.coeff 0 (ArithmeticThetaComputed.theta (A 0)) = 1 := by
    have h := (ArithmeticThetaCore.constant_one n _ (hv 0).2.2
      (ArithmeticThetaCore.even_gram_natural_values n (A 0)
        (hv 0).1 (hv 0).2.1 (hv 0).2.2)).2
    simpa [ArithmeticThetaComputed.theta, PowerSeries.coeff_map, PowerSeries.coeff_mk] using h
  have hm : ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A 0 =
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    rw [(ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix n 1 0 A hv).1]
    ext a i
    have ha : a = 0 := Fin.ext (by omega)
    have hi : i = 0 := Subsingleton.elim _ _
    subst a
    subst i
    have hc' := ArithmeticThetaComputed.computed_coefficient_matrix n 1 0 A hv 0 0
    change (ArithmeticThetaComputed.coefficientMatrix A 0 0 0 : ℂ) =
      PowerSeries.coeff 0 (ArithmeticThetaComputed.theta (A 0)) at hc'
    rw [hc] at hc'
    simpa using (show ArithmeticThetaComputed.coefficientMatrix A 0 0 0 = 1 by
      exact_mod_cast hc')
  have hr : (ArithmeticThetaElimination.run
      (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A 0)).pivots.length = 1 := by
    rw [(ArithmeticThetaElimination.run_kernel_rank 1 1 _).2, hm, Matrix.rank_one]
    simp
  simp [early, hr]

end AdaptiveUniversalSolver

open AdaptiveUniversalSolver in
theorem adaptive_singleton_zero :
    ∀ (n : ℕ) (A : Matrices n 1),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ cs : List (Change n 1),
        solveChanges A cs = some (assemble A 0) ∧ Correct A (assemble A 0) := by
  intro n A hv cs
  have he := singleton_early A hv (changeRelations A cs)
  constructor
  · have hh := (capped_doubling_schedule (bound A)).1
    obtain ⟨xs, hx⟩ : ∃ xs, schedule (bound A) = 0 :: xs := by
      cases hs : schedule (bound A) with
      | nil => simp [hs] at hh
      | cons b xs =>
        have hb : b = 0 := by simpa [hs] using hh
        exact ⟨xs, by simp [hb]⟩
    simp [solveChanges, solve, hx, he]
  · apply (executable_relation_certificate n 1 cs.length A (changeRelations A cs)
      hv (checked_basis_change_relations n 1 A hv cs) 0).2.1
    simp [certify, he]

end ArithmeticThetaAdaptiveSolverR0230

#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_universal_solver
#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_checked_input
#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_singleton_zero
