module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Topology.Sheaves.Init

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Integrality of the `t`-power in the local numerator at `r = 2c`. -/
set_option autoImplicit false

namespace ArithmeticThetaLocalNormR0054

private theorem six_dvd_c_mul_square_sub_one (c : ℕ) (hc : 1 < c) :
    6 ∣ c * (c ^ 2 - 1) := by
  have h : (3 : ℕ).factorial ∣ (c + 1).descFactorial 3 :=
    Nat.factorial_dvd_descFactorial (c + 1) 3
  norm_num [Nat.descFactorial] at h
  have hc1 : 1 ≤ c := by omega
  have hone : 1 ≤ c ^ 2 := by nlinarith
  have hpoly : c ^ 2 - 1 = (c - 1) * (c + 1) := by
    apply Nat.cast_injective (R := Int)
    push_cast [Nat.cast_sub hone, Nat.cast_sub hc1]
    ring
  simpa [hpoly, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem norm_exponent_integral (c : ℕ) (hc : 1 < c) (_hcop : Nat.Coprime c 6) :
    12 ∣ 2 * c * (c ^ 2 - 1) ∧
      ((2 * c * (c ^ 2 - 1) / 12 : ℕ) : ℚ) =
        (2 * c : ℚ) * ((c : ℚ) ^ 2 - 1) / 12 := by
  have h6 : 6 ∣ c * (c ^ 2 - 1) := six_dvd_c_mul_square_sub_one c hc
  have h12 : 12 ∣ 2 * c * (c ^ 2 - 1) := by
    have h' : 2 * 6 ∣ 2 * (c * (c ^ 2 - 1)) := Nat.mul_dvd_mul_left 2 h6
    norm_num at h' ⊢
    simpa [Nat.mul_assoc] using h'
  constructor
  · exact h12
  · rw [Nat.cast_div h12 (by norm_num)]
    have hone : 1 ≤ c ^ 2 := by nlinarith
    push_cast [Nat.cast_sub hone]
    ring

end ArithmeticThetaLocalNormR0054
