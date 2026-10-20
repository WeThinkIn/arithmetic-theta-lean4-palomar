module
public import Mathlib
public import LaurentPoweredNormR0064

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Norm

namespace Quotients
def quotient (c d i : ℕ) : ℕ := c * i / d
def residue (c d i : ℕ) : ℕ := c * i % d


end Quotients

namespace FiniteNorm
def triangle (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) - 1) / 2

def p (c : ℕ) : ℤ := -triangle c

def K (c : ℕ) : ℤ := (c : ℤ) ^ 2 - 1

def S (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i : ℤ)

def E (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d,
    ((ArithmeticThetaPalomarFormal261Norm.Quotients.residue c d i : ℤ) *
      (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i : ℤ) +
    (d : ℤ) * triangle (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i))


end FiniteNorm

namespace LaurentNorm
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


end LaurentNorm


/-- Exact independent target: accepted-092. -/
theorem powered_gamma_norm :
  ∀ (K : Type) [Field K] [CharZero K] (c d : ℕ) (ζ : K), 1 < c → 0 < d → Nat.Coprime c d → IsPrimitiveRoot ζ d → ∀ (H : Fin d → Fin d → ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K) (b : ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K), (∀ i j : Fin d, ArithmeticThetaPalomarFormal261Norm.LaurentNorm.IsGamma (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Coeff K) d (c * i.val) (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.a K ζ j.val c) (H i j)) → ArithmeticThetaPalomarFormal261Norm.LaurentNorm.IsGamma (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Coeff K) d 0 (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.w K ^ (c * d)) b → (∏ i : Fin d, ∏ j : Fin d, H i j) = (-1 : ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K) ^ (-ArithmeticThetaPalomarFormal261Norm.FiniteNorm.S c d) * ArithmeticThetaPalomarFormal261Norm.LaurentNorm.z K d ^ (-(c : ℤ) * ArithmeticThetaPalomarFormal261Norm.FiniteNorm.S c d) * ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Q K d ^ (-ArithmeticThetaPalomarFormal261Norm.FiniteNorm.E c d) * b := by
  exact ArithmeticThetaLaurentNormR0064.powered_gamma_norm

end ArithmeticThetaPalomarFormal261Norm
#print axioms ArithmeticThetaPalomarFormal261Norm.powered_gamma_norm
