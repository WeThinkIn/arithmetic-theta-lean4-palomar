import Mathlib

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormQuotientsR0062

def quotient (c d i : ℕ) : ℕ := c * i / d
def residue (c d i : ℕ) : ℕ := c * i % d

def quotientSum (c d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range d, (quotient c d i : ℚ)

def weightedTerm (c d i : ℕ) : ℚ :=
  (residue c d i : ℚ) * (quotient c d i : ℚ) +
    (d : ℚ) * (quotient c d i : ℚ) * ((quotient c d i : ℚ) - 1) / 2

def weightedSum (c d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range d, weightedTerm c d i

end ArithmeticThetaNormQuotientsR0062
