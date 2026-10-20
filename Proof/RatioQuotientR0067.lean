module

public import RatioRegularityDefinitionsR0067

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067
set_option synthInstance.maxHeartbeats 1600000
/-- Division in the actual chart fraction field. Naming this operation avoids
repeating expensive field-instance elaboration in the frozen type context. -/
def ratio (k : Type u) [Field k] [CharZero k]
    (f g : FunctionField k) : FunctionField k := f / g
end ArithmeticThetaRatioRegularityR0067
