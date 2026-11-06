module

public import RationalSchurCompletionR0229
public import ShiftedIntegerIntervalR0229

@[expose] public section

/-! Exact membership in the dimension-recursive rational ellipsoid enumerator. -/
set_option autoImplicit false

namespace ArithmeticThetaLDLEnumerationR0229
namespace RecursiveEllipsoidEnumeration

private theorem cast_cons {n : ℕ} (z : ℤ) (y : Fin n → ℤ) :
    (fun i => ((Fin.cons z y : Fin (n+1) → ℤ) i : ℚ)) = Fin.cons (z : ℚ) (fun i => (y i : ℚ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem head_interval_iff {n : ℕ} (A : QMatrix (n+1))
    (hs : A.IsSymm) (hp : A.toQuadraticForm'.PosDef)
    (B : ℚ) (z : ℤ) (y : Fin n → ℤ) :
    z ∈ shiftedInterval (shift A y) (remainder A B y) ↔
      energy A (fun i => ((Fin.cons z y : Fin (n+1) → ℤ) i : ℚ)) ≤ B := by
  obtain ⟨ha, _, _, hc⟩ := rational_schur_completion n A hs hp
  rw [shifted_integer_interval, shift, remainder, cast_cons, hc,
    le_div_iff₀ ha]
  simp only [neg_div, sub_neg_eq_add]
  constructor <;> intro h <;> nlinarith only [h]

end RecursiveEllipsoidEnumeration

open RecursiveEllipsoidEnumeration in
/-- Soundness and completeness for every dimension and every rational bound. -/
theorem recursive_ellipsoid_enumeration :
    ∀ (n : ℕ) (A : QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef →
      ∀ (B : ℚ) (x : Fin n → ℤ),
        x ∈ enumerate n A B ↔ energy A (fun i => (x i : ℚ)) ≤ B := by
  intro n
  induction n with
  | zero =>
      intro A hs hp B x
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      by_cases hB : 0 ≤ B <;> simp [enumerate, energy, hB, hx]
  | succ n ih =>
      intro A hs hp B x
      obtain ⟨ha, hsym, hpos, hc⟩ := rational_schur_completion n A hs hp
      rw [enumerate, if_pos ha, Finset.mem_biUnion]
      constructor
      · rintro ⟨y, hy, hx⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        exact (head_interval_iff A hs hp B z y).mp hz
      · intro hx
        let y : Fin n → ℤ := fun i => x i.succ
        have hcons : Fin.cons (x 0) y = x := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        have henergy : energy A (fun i => (x i : ℚ)) =
            A 0 0 * ((x 0 : ℚ) + (∑ j, A 0 j.succ * (y j : ℚ)) / A 0 0)^2 +
              energy (schur A) (fun i => (y i : ℚ)) := by
          rw [← hcons, cast_cons]
          exact hc _ _
        have htail : energy (schur A) (fun i => (y i : ℚ)) ≤ B := by
          have hn := mul_nonneg (le_of_lt ha)
            (sq_nonneg ((x 0 : ℚ) + (∑ j, A 0 j.succ * (y j : ℚ)) / A 0 0))
          rw [henergy] at hx
          linarith
        refine ⟨y, (ih (schur A) hsym hpos B y).mpr htail, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨x 0, (head_interval_iff A hs hp B (x 0) y).mpr ?_, hcons⟩
        simpa only [hcons] using hx

end ArithmeticThetaLDLEnumerationR0229

#print axioms ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration
