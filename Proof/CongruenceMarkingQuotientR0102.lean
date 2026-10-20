module

public import IntegralPrimitiveLiftR0102
public import ScopedCuspDefinitionsR0102
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace ArithmeticThetaMarkingCuspsR0102

set_option backward.isDefEq.respectTransparency false in
/-- Lift the first column, then adjust the second column by an integral shear. -/
theorem reduction_surjective (L : ℕ) (hL : 3 ≤ L) :
    Function.Surjective (reduction L) := by
  have : NeZero L := ⟨by omega⟩
  intro B
  let v : ArithmeticThetaLevelCount.PrimitivePair L :=
    ⟨(B 0 0, B 1 0), Matrix.SpecialLinearGroup.isCoprime_col B 0⟩
  obtain ⟨A, hA⟩ := ArithmeticThetaIntegralCuspsR0102.integral_primitive_lift L hL v
  let C := reduction L A
  have h0 : C 0 0 = B 0 0 := congrArg (fun w => w.val.1) hA
  have h1 : C 1 0 = B 1 0 := congrArg (fun w => w.val.2) hA
  have hC : B 0 0 * C 1 1 - C 0 1 * B 1 0 = 1 := by
    have h := C.property
    rw [Matrix.det_fin_two] at h
    simpa only [h0, h1] using h
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.property
  let t : ZMod L := C 1 1 * B 0 1 - C 0 1 * B 1 1
  let T : IntegralMarking := ⟨!![1, (t.val : ℤ); 0, 1], by simp⟩
  have ht : ((t.val : ℤ) : ZMod L) = t := by simp
  refine ⟨A * T, ?_⟩
  rw [map_mul]
  change C * reduction L T = B
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · change C 0 0 * ((1 : ℤ) : ZMod L) + C 0 1 * ((0 : ℤ) : ZMod L) = B 0 0
    simpa using h0
  · change C 0 0 * ((t.val : ℤ) : ZMod L) + C 0 1 * ((1 : ℤ) : ZMod L) = B 0 1
    rw [ht, h0]
    simp only [Int.cast_one, mul_one]
    dsimp [t]
    linear_combination B 0 1 * hC - C 0 1 * hB
  · change C 1 0 * ((1 : ℤ) : ZMod L) + C 1 1 * ((0 : ℤ) : ZMod L) = B 1 0
    simpa using h1
  · change C 1 0 * ((t.val : ℤ) : ZMod L) + C 1 1 * ((1 : ℤ) : ZMod L) = B 1 1
    rw [ht, h1]
    simp only [Int.cast_one, mul_one]
    dsimp [t]
    linear_combination B 1 1 * hC - C 1 1 * hB

/-- The actual principal-congruence quotient, with its value on every marking. -/
theorem congruence_marking_quotient :
    ∀ L : ℕ, 3 ≤ L → Function.Surjective (reduction L) ∧
      ∃ e : CongruenceMarkings L ≃* FiniteMarking L,
        ∀ A : IntegralMarking, e (markingClass L A) = reduction L A := by
  intro L hL
  have hs := reduction_surjective L hL
  refine ⟨hs, QuotientGroup.quotientKerEquivOfSurjective (reduction L) hs, ?_⟩
  intro A
  rfl

end ArithmeticThetaMarkingCuspsR0102
