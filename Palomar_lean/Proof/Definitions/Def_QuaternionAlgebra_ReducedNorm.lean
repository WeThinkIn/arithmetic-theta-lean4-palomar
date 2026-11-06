module

public import Mathlib.Tactic.ReduceModChar
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
public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Quaternion

namespace QuaternionAlgebra

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R := 2 * x.re

@[simp] theorem nrd_mk (x₀ x₁ x₂ x₃ : R) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := rfl

@[simp] theorem trd_mk (x₀ x₁ x₂ x₃ : R) :
    trd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = 2 * x₀ := rfl

@[simp] theorem nrd_zero : nrd (0 : ℍ[R, a, b]) = 0 := by simp [nrd]
@[simp] theorem nrd_one : nrd (1 : ℍ[R, a, b]) = 1 := by simp [nrd]
@[simp] theorem nrd_neg (x : ℍ[R, a, b]) : nrd (-x) = nrd x := by simp [nrd]
@[simp] theorem nrd_star (x : ℍ[R, a, b]) : nrd (star x) = nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp only [star_mk, nrd_mk]; ring
@[simp] theorem nrd_coe (r : R) : nrd ((r : R) : ℍ[R, a, b]) = r ^ 2 := by simp [nrd]

theorem mul_star_eq_coe_nrd (x : ℍ[R, a, b]) : x * star x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem star_mul_eq_coe_nrd (x : ℍ[R, a, b]) : star x * x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem add_star_eq_coe_trd (x : ℍ[R, a, b]) : x + star x = ((trd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_add_mk, trd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

end ReducedNorm

end QuaternionAlgebra
