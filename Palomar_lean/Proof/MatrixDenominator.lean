module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Init

@[expose] public section
open scoped BigOperators

namespace ArithmeticThetaLattice

theorem matrix_common_denominator : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℚ), ∃ D : ℕ, 0 < D ∧ ∃ Z : Matrix (Fin n) (Fin m) ℤ, ∀ i j, (Z i j : ℚ) = (D : ℚ) * A i j := by
  intro n m A
  let D : ℕ := ∏ i : Fin n, ∏ j : Fin m, (A i j).den
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact Rat.den_pos _
  refine ⟨D, hD, ?_⟩
  let Z : Matrix (Fin n) (Fin m) ℤ := fun i j => ((D / (A i j).den : ℕ) : ℤ) * (A i j).num
  refine ⟨Z, ?_⟩
  intro i j
  dsimp [Z]
  have hden : (A i j).den ∣ D := by
    dsimp [D]
    have hj' : (A i j).den ∣ ∏ j : Fin m, (A i j).den :=
      Finset.dvd_prod_of_mem (fun j : Fin m => (A i j).den) (Finset.mem_univ j)
    exact dvd_trans hj' (Finset.dvd_prod_of_mem (fun i : Fin n => ∏ j : Fin m, (A i j).den) (Finset.mem_univ i))
  change ((((D / (A i j).den : ℕ) : ℤ) * (A i j).num : ℤ) : ℚ) = (D : ℚ) * A i j
  rw [Int.cast_mul, Int.cast_natCast]
  have hcastdiv : ((D / (A i j).den : ℕ) : ℚ) = (D : ℚ) / (A i j).den := by
    rw [Nat.cast_div hden]
    exact_mod_cast (Rat.den_nz (A i j))
  rw [hcastdiv]
  calc
    (D : ℚ) / (A i j).den * (A i j).num = (D : ℚ) * ((A i j).num / (A i j).den) := by ring
    _ = (D : ℚ) * A i j := by rw [Rat.num_div_den]


end ArithmeticThetaLattice
