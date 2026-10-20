module

public import LocalComparisonFamilyR0067
public import ChartScalarExtensionProofR0076

@[expose] public section

/-! The graph of the Laurent scalar inclusion in the actual chart fraction field.
This is a denominator presentation, not a selected arbitrary field action.
The graph's realization by a ring homomorphism is a new proof obligation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaCyclicConstantsR0088
variable (k : Type u) [Field k] [CharZero k]
abbrev Chart := ArithmeticThetaRatioRegularityR0067.Chart k
abbrev FunctionField := ArithmeticThetaRatioRegularityR0067.FunctionField k
def scalarBase : PowerSeries k →+* FunctionField k :=
  (ArithmeticThetaLocalOrdersR0066.toFunctionField k).comp
    ((ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k).comp
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k))
def fieldParameter : FunctionField k := scalarBase k PowerSeries.X
/-- c = a/t^n in k((t)), and f is the same fraction in the concrete chart field. -/
def ScalarValue (c : LaurentSeries k) (f : FunctionField k) : Prop :=
  ∃ (n : ℕ) (a : PowerSeries k),
    c * (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n =
      algebraMap (PowerSeries k) (LaurentSeries k) a ∧
    f * fieldParameter k ^ n = scalarBase k a
end ArithmeticThetaCyclicConstantsR0088
