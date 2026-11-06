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
public import P2M.Util

@[expose] public section
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal

set_option autoImplicit false

universe u

open IsLocalRing

theorem solution
    {S : Type u} [CommRing S] [IsLocalRing S] (a₁ a₂ a₃ a₄ a₆ x v v' : S)
    (hx : x ∈ maximalIdeal S) (hv : v ∈ maximalIdeal S) (hv' : v' ∈ maximalIdeal S)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by
  set B := 1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2) with hB
  have hprod : (v - v') * B = 0 := by rw [hB]; linear_combination h - h'
  have hBunit : IsUnit B := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hBm
    have h1 : B - 1 ∈ IsLocalRing.maximalIdeal S := by
      rw [hB]
      have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ a₁ hx)
        (Ideal.mul_mem_left _ a₃ (Ideal.add_mem _ hv hv')))
        (Submodule.neg_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (a₂ * x) hx)
          (Ideal.mul_mem_left _ (a₄ * x) (Ideal.add_mem _ hv hv')))
          (Ideal.mul_mem_left _ a₆ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ v hv) (Ideal.mul_mem_left _ v hv'))
            (Ideal.mul_mem_left _ v' hv')))))
      convert this using 1; ring
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ hBm h1; simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  exact sub_eq_zero.mp (hBunit.mul_left_eq_zero.mp hprod)
