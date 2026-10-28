module

public import Mathlib

@[expose] public section

/-!
# Arithmetic theta: independent finite-determination statement

This is the first interface in the complete-scope Palomar migration. It states
finite determination for the actual lattice-shell theta series, for every
nonempty finite family and every rank, without assuming a coefficient bound
or a geometric provider. The explicit bounds, geometric constructions, image
coordinates, algorithms and examples remain separately tracked obligations in
`docs/Coverage.md`; this configuration alone does not cover the full paper.

The input is an even integral positive-definite Gram matrix. The quadratic
form is one half of its rational quadratic form. Its theta coefficients count
all integer vectors of the specified norm, using Nat.card; finite-shell
theorems in the Solution justify these cardinalities under validGram.
-/

namespace ArithmeticThetaPalomar

/-- Symmetric integral Gram matrix, even diagonal, positive-definite half norm. -/
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef

/-- Full theta series whose coefficients are actual integral lattice shell counts. -/
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))

/-- Complex linear map taking a coefficient vector to its full theta combination. -/
noncomputable def thetaMap {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))

/-- A finite prefix determines every full complex relation, at every larger cutoff.
The only input hypotheses are nonemptiness and valid Gram matrices; rank zero
and linearly dependent theta families are included. -/
theorem finiteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i, validGram (A i)) :
    ∃ B : ℕ, ∀ B' : ℕ, B ≤ B' → ∀ c : Fin h → ℂ,
      thetaMap A c = 0 ↔ ∀ m : ℕ, m ≤ B' →
        PowerSeries.coeff m (thetaMap A c) = 0 := by
  sorry

end ArithmeticThetaPalomar
