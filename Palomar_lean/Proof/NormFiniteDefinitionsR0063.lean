module

public import NormQuotientDefinitionsR0062

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormFiniteR0063

def triangle (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) - 1) / 2

def p (c : ℕ) : ℤ := -triangle c

def K (c : ℕ) : ℤ := (c : ℤ) ^ 2 - 1

def S (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, (ArithmeticThetaNormQuotientsR0062.quotient c d i : ℤ)

def E (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d,
    ((ArithmeticThetaNormQuotientsR0062.residue c d i : ℤ) *
      (ArithmeticThetaNormQuotientsR0062.quotient c d i : ℤ) +
    (d : ℤ) * triangle (ArithmeticThetaNormQuotientsR0062.quotient c d i))

def signExponent (c d : ℕ) : ℤ :=
  ((d : ℤ) ^ 2 - 1) * p c + S c d

def zExponent (c d : ℕ) : ℤ :=
  ((d : ℤ) - 1) * p c + (c : ℤ) * S c d

def qExponent (c d : ℕ) : ℤ :=
  ((d : ℤ) ^ 2 - 1) * (K c / 12) + p c * triangle d + E c d

def correction {F : Type*} [Field F] (c d : ℕ) (z Q : F) : F :=
  (-1 : F) ^ signExponent c d * z ^ zExponent c d * Q ^ qExponent c d

end ArithmeticThetaNormFiniteR0063
