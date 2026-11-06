import PhaseSwitchDefinitionsR0218

/-! Matrix reversal and its action on the accepted even discriminant character. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace ArithmeticThetaPhaseSwitchR0218
open ArithmeticThetaFourTorsion

private theorem reversal_square : reversal * reversal = (1 : Mat4) := by
  decide

/-- The five properties of first-half reversal used by the phase comparison.

Reversal is an involution with determinant `-1`. Its conjugation preserves the
even stabilizer, negates the character exponent, and respects multiplication. -/
theorem reversal_character :
    reversal * reversal = (1 : Mat4) ∧
    reversal.det = -1 ∧
    (∀ A : Mat4, PreservesEven (conjugate A) ↔ PreservesEven A) ∧
    (∀ A : Mat4, PreservesEven A →
      characterExponent (conjugate A) = -characterExponent A) ∧
    (∀ A B : Mat4, conjugate (A * B) = conjugate A * conjugate B) := by
  refine ⟨reversal_square, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro A B
    simp only [conjugate]
    calc
      reversal * (A * B) * reversal =
          reversal * A * (reversal * reversal) * B * reversal := by
        rw [reversal_square]
        simp only [mul_one, mul_assoc]
      _ = reversal * A * reversal * (reversal * B * reversal) := by
        simp only [mul_assoc]

end ArithmeticThetaPhaseSwitchR0218

#print axioms ArithmeticThetaPhaseSwitchR0218.reversal_character
