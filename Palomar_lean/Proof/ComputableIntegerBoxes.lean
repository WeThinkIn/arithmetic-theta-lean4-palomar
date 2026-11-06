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
public import Mathlib.Topology.Sheaves.Init
public import EnumerationAlgorithm

@[expose] public section

namespace ArithmeticThetaEnumeration

theorem integerInterval_membership (R : ℕ) (x : ℤ) :
    x ∈ (Finset.range (2 * R + 1)).image (fun k : ℕ => (k : ℤ) - (R : ℤ)) ↔
      -(R : ℤ) ≤ x ∧ x ≤ (R : ℤ) := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨(x + (R : ℤ)).toNat, ?_, ?_⟩ <;> omega

theorem box_membership (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (m : ℕ) (x : Fin n → ℤ) :
    x ∈ Fintype.piFinset (fun j : Fin n =>
      (Finset.range (2 * Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) + 1)).image
        (fun k : ℕ => (k : ℤ) - (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ))) ↔
      ∀ j : Fin n,
        -(Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) ≤ x j ∧
        x j ≤ (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) := by
  simp only [Fintype.mem_piFinset, integerInterval_membership]

end ArithmeticThetaEnumeration
