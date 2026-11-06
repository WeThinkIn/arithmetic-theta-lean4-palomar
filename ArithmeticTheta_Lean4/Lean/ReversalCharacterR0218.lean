import PhaseSwitchDefinitionsR0218

/-! Matrix reversal and its action on the accepted even discriminant character. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace ArithmeticThetaPhaseSwitchR0218
open ArithmeticThetaFourTorsion

private theorem reversal_square : reversal * reversal = (1 : Mat4) := by
  decide

/-- First-half reversal preserves the even stabilizer and inverts its character. -/
theorem reversal_character :
    ArithmeticThetaPhaseSwitchR0218.reversal * ArithmeticThetaPhaseSwitchR0218.reversal = (1 : ArithmeticThetaFourTorsion.Mat4) ∧ ArithmeticThetaPhaseSwitchR0218.reversal.det = -1 ∧ (∀ A : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven (ArithmeticThetaPhaseSwitchR0218.conjugate A) ↔ ArithmeticThetaFourTorsion.PreservesEven A) ∧ (∀ A : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven A → ArithmeticThetaFourTorsion.characterExponent (ArithmeticThetaPhaseSwitchR0218.conjugate A) = -ArithmeticThetaFourTorsion.characterExponent A) ∧ (∀ A B : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaPhaseSwitchR0218.conjugate (A * B) = ArithmeticThetaPhaseSwitchR0218.conjugate A * ArithmeticThetaPhaseSwitchR0218.conjugate B) := by
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
