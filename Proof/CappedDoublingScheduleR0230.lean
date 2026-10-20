module

public import AdaptiveSolverDefinitionsR0230

@[expose] public section

/-! Correctness of the frozen capped doubling schedule, including its internal fuel. -/
set_option autoImplicit false
namespace ArithmeticThetaAdaptiveSolverR0230
namespace CappedDoublingScheduleR0230

private theorem next_bounds {cap b : ℕ} (h : b < cap) :
    b < next cap b ∧ next cap b ≤ cap := by
  unfold next
  constructor
  · omega
  · exact Nat.min_le_left _ _

private theorem aux_head (cap fuel b : ℕ) (hb : b ≤ cap) :
    (scheduleAux cap fuel b).head? = some b := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [scheduleAux]
    split
    · have h : cap = b := by omega
      simp [h]
    · rfl

private theorem aux_properties (cap fuel : ℕ) : ∀ b : ℕ, b ≤ cap → cap - b ≤ fuel →
    (∃ xs : List ℕ, scheduleAux cap fuel b = xs ++ [cap]) ∧
    (scheduleAux cap fuel b).Pairwise (fun a c => a < c) ∧
    (∀ c ∈ scheduleAux cap fuel b, b ≤ c ∧ c ≤ cap) ∧
    ∀ i : ℕ, i + 1 < (scheduleAux cap fuel b).length →
      (scheduleAux cap fuel b).getD (i+1) 0 =
        next cap ((scheduleAux cap fuel b).getD i 0) := by
  induction fuel with
  | zero =>
    intro b hb hf
    have hbc : b = cap := by omega
    subst b
    simp [scheduleAux]
  | succ fuel ih =>
    intro b hb hf
    by_cases hstop : cap ≤ b
    · have hbc : b = cap := by omega
      subst b
      simp [scheduleAux]
    · have hlt : b < cap := by omega
      obtain ⟨hinc, hcap⟩ := next_bounds hlt
      have hf' : cap - next cap b ≤ fuel := by omega
      obtain ⟨⟨xs, hxs⟩, hp, hr, ha⟩ := ih (next cap b) hcap hf'
      simp only [scheduleAux, if_neg hstop]
      refine ⟨⟨b :: xs, ?_⟩, ?_, ?_, ?_⟩
      · simp only [List.cons_append, hxs]
      · apply List.pairwise_cons.mpr
        exact ⟨fun c hc => lt_of_lt_of_le hinc (hr c hc).1, hp⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨le_rfl, hb⟩
        · exact ⟨le_trans (Nat.le_of_lt hinc) (hr c hc).1, (hr c hc).2⟩
      · intro i hi
        cases i with
        | zero =>
          simp only [Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
          rw [← List.headD_eq_getD, List.headD_eq_head?_getD,
            aux_head cap fuel (next cap b) hcap]
          rfl
        | succ i =>
          simp only [List.length_cons] at hi
          simpa only [List.getD_cons_succ] using ha i (by omega)

end CappedDoublingScheduleR0230

/-- The schedule starts at zero, reaches its cap without repetition, and takes
exactly the prescribed capped doubling step at each adjacent pair. -/
theorem capped_doubling_schedule :
    ∀ cap : ℕ, (schedule cap).head? = some 0 ∧
      (∃ xs : List ℕ, schedule cap = xs ++ [cap]) ∧
      (schedule cap).Pairwise (fun a b => a < b) ∧
      (∀ b ∈ schedule cap, b ≤ cap) ∧
      ∀ i : ℕ, i + 1 < (schedule cap).length →
        (schedule cap).getD (i+1) 0 = next cap ((schedule cap).getD i 0) := by
  intro cap
  obtain ⟨he, hp, hr, ha⟩ :=
    CappedDoublingScheduleR0230.aux_properties cap (cap+1) 0 (by omega) (by omega)
  exact ⟨CappedDoublingScheduleR0230.aux_head cap (cap+1) 0 (by omega),
    he, hp, fun b hb => (hr b hb).2, ha⟩

end ArithmeticThetaAdaptiveSolverR0230

#print axioms ArithmeticThetaAdaptiveSolverR0230.capped_doubling_schedule
