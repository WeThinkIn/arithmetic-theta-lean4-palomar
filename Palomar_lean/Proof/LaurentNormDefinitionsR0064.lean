module

public import FormalNormProduct
public import NormScalarCorrectionR0063
public import NormFiniteDefinitionsR0063
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.AffineMonoid.UniqueSums

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064

/-- The actual coefficientwise limit of the literal two-sided gamma product.
Agreement is uniform below each integer cutoff, including all negative degrees. -/
def Partial (F : Type) [Field F] (d m : ℕ) (a : F) (N : ℕ) : LaurentSeries F :=
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a * HahnSeries.single ((d : ℤ) * l + m) (1 : F))) *
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a⁻¹ * HahnSeries.single ((d : ℤ) * (l + 1) - m) (1 : F)))

def IsGamma (F : Type) [Field F] (d m : ℕ) (a : F) (g : LaurentSeries F) : Prop :=
  ∀ n : ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ e : ℤ, e ≤ n →
    (Partial F d m a N).coeff e = g.coeff e

def t (F : Type) [Field F] : LaurentSeries F := HahnSeries.single 1 1

abbrev Coeff (K : Type) [Field K] := FractionRing (LaurentPolynomial K)
abbrev Series (K : Type) [Field K] := LaurentSeries (Coeff K)

def w (K : Type) [Field K] : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.T 1)

def scalar (K : Type) [Field K] (a : K) : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.C a)

def a (K : Type) [Field K] (ζ : K) (j c : ℕ) : Coeff K :=
  scalar K ζ ^ (c * j) * w K ^ c

def point (K : Type) [Field K] (ζ : K) (i j : ℕ) : Series K :=
  HahnSeries.C (a K ζ j 1) * t (Coeff K) ^ i

def z (K : Type) [Field K] (d : ℕ) : Series K :=
  HahnSeries.C (w K ^ d)

def Q (K : Type) [Field K] (d : ℕ) : Series K := t (Coeff K) ^ d

def fValue (K : Type) [Field K] (c d : ℕ) (v g h : Series K) : Series K :=
  Q K d ^ (ArithmeticThetaNormFiniteR0063.K c / 12) *
    (-v) ^ ArithmeticThetaNormFiniteR0063.p c * g ^ (c ^ 2) / h

end ArithmeticThetaLaurentNormR0064
