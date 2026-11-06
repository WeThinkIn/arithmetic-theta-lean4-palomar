import OrthogonalConsumerDefinitionsR0127

set_option autoImplicit false
namespace ArithmeticThetaFullSourceR0268

def binaryGram : Matrix (Fin 2) (Fin 2) ℤ := ![![2, 1], ![1, 12]]
def binaryBasis : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![0, 2]]
def binaryNorms : Fin 2 → ℕ := ![2, 46]
def binaryRepresentatives : Fin 2 → Fin 2 → ℚ := ![![0, 0], ![1/2, 1/2]]
def binaryResidues : Fin 2 → Fin 2 → ℤ := ![![0, 0], ![1, 23]]

end ArithmeticThetaFullSourceR0268
