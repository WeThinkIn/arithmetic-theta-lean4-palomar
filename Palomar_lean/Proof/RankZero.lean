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
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ArithmeticThetaElementary

theorem rank_zero_coefficients :
    ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ,
      Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0 := by
  intro Q hQ n
  have hx (x : Fin 0 → ℤ) : x = 0 := Subsingleton.elim _ _
  by_cases hn : n = 0
  · subst n
    have : Nonempty {x : Fin 0 → ℤ // Q x = 0} := ⟨⟨0, hQ⟩⟩
    rw [if_pos rfl]
    exact Nat.card_unique
  · have : IsEmpty {x : Fin 0 → ℤ // Q x = n} :=
      ⟨fun x => hn (x.property.symm.trans ((congrArg Q (hx x.val)).trans hQ))⟩
    simp [hn]

theorem sum_smul_one (h : ℕ) (c : Fin h → ℂ) :
    (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = PowerSeries.C (∑ i : Fin h, c i) := by
  simp [PowerSeries.smul_eq_C_mul, map_sum]

theorem rank_zero_kernel :
    ∀ (h : ℕ) (c : Fin h → ℂ),
      (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = 0 ↔ (∑ i : Fin h, c i) = 0 := by
  intro h c
  rw [sum_smul_one]
  exact map_eq_zero_iff _ PowerSeries.C_injective

theorem rank_zero_image :
    ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ,
      (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔
        ∃ z : ℂ, f = PowerSeries.C z := by
  intro h hh f
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨∑ i : Fin h, c i, hc.symm.trans (sum_smul_one h c)⟩
  · rintro ⟨z, rfl⟩
    let j : Fin h := ⟨0, hh⟩
    refine ⟨fun i => if i = j then z else 0, ?_⟩
    rw [sum_smul_one]
    simp

end ArithmeticThetaElementary
