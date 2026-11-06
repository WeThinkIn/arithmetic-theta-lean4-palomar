import ExactKatoAnnularFormulaR0157
import FaithfulAnnularEvaluationR0156
import FullGammaEvaluationR0156
import RamifiedLiteralQuotientR0156
import CoefficientFunctionFieldExpansionR0157
import CoefficientGenericKatoSquareR0157
import LaurentGammaExistenceR0064

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158

/-- The coefficient map fixes the actual transcendental Laurent coordinate. -/
def IsCoefficientMap (k l : Type) [Field k] [Field l] (ι : k →+* l)
    (κ : ArithmeticThetaLaurentNormR0064.Coeff k →+* ArithmeticThetaLaurentNormR0064.Coeff l) : Prop :=
  (∀ a : k, κ (ArithmeticThetaLaurentNormR0064.scalar k a) = ArithmeticThetaLaurentNormR0064.scalar l (ι a)) ∧
  κ (ArithmeticThetaLaurentNormR0064.w k) = ArithmeticThetaLaurentNormR0064.w l

/-- The unsplit literal expansion uses full gamma limits at z=t^j w and z^c.
The functions are not assumed to be units in a completed annular ring. -/
def HasExpansion (k : Type) [Field k] [CharZero k] (r c j : ℕ)
    (v : ArithmeticThetaLaurentNormR0064.Series k) : Prop :=
  ∀ g h : ArithmeticThetaLaurentNormR0064.Series k,
    ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) r j (ArithmeticThetaLaurentNormR0064.w k) g →
    ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) r (c*j) (ArithmeticThetaLaurentNormR0064.w k ^ c) h →
    v = ArithmeticThetaLaurentNormR0064.fValue k c r
      (HahnSeries.C (ArithmeticThetaLaurentNormR0064.w k) * ArithmeticThetaLaurentNormR0064.t (ArithmeticThetaLaurentNormR0064.Coeff k) ^ j) g h

end ArithmeticThetaUnsplitExpansionR0158
