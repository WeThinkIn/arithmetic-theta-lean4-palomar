module

public import Mathlib

@[expose] public section

namespace ArithmeticThetaFormalNorm

noncomputable def partialGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) (N : ℕ) : PowerSeries R :=
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (d * r + i))) *
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C b * PowerSeries.X ^ (d * (r + 1) - i)))

noncomputable def fullGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) : PowerSeries R :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (partialGamma d i a b (n + 1)))

noncomputable def twistA {K : Type*} [Field K] (ζ : K) (j : ℕ) : LaurentPolynomial K :=
  LaurentPolynomial.C (ζ ^ j) * LaurentPolynomial.T 1

noncomputable def twistB {K : Type*} [Field K] (ζ : K) (j : ℕ) : LaurentPolynomial K :=
  LaurentPolynomial.C ((ζ⁻¹) ^ j) * LaurentPolynomial.T (-1)

/-- Genuine t-series for gamma_{t^d}(ζ^j t^i w), with Laurent-polynomial coefficients in w. -/
noncomputable def partialTwisted {K : Type*} [Field K] (d : ℕ) (ζ : K) (i j N : ℕ) :
    PowerSeries (LaurentPolynomial K) := partialGamma d i (twistA ζ j) (twistB ζ j) N

noncomputable def twisted {K : Type*} [Field K] (d : ℕ) (ζ : K) (i j : ℕ) :
    PowerSeries (LaurentPolynomial K) := fullGamma d i (twistA ζ j) (twistB ζ j)

/-- The target gamma_{t^d}(w^d), with precisely the same t and w variables. -/
noncomputable def partialBase (K : Type*) [Field K] (d N : ℕ) : PowerSeries (LaurentPolynomial K) :=
  partialGamma d 0 (LaurentPolynomial.T (d : ℤ)) (LaurentPolynomial.T (-(d : ℤ))) N

noncomputable def baseGamma (K : Type*) [Field K] (d : ℕ) : PowerSeries (LaurentPolynomial K) :=
  fullGamma d 0 (LaurentPolynomial.T (d : ℤ)) (LaurentPolynomial.T (-(d : ℤ)))

end ArithmeticThetaFormalNorm
