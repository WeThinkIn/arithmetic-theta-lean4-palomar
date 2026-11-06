module

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
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)

def smulNumerator (a d : ℕ) (h : T[X]) : T[X] :=
  ∑ i ∈ Finset.range (d + 1), C (h.coeff i) * W.Φ a ^ i * W.ΨSq a ^ (d - i)

structure IsCyclicKernel (N : ℕ) (h : T[X]) : Prop where

  natDegree_le : h.natDegree ≤ (N - 1) / 2

  coeff_eq_one : h.coeff ((N - 1) / 2) = 1

  dvd_preΨ : h ∣ W.preΨ N

  dvd_smulNumerator : ∀ a : ℕ, 2 ≤ a → a ≤ (N - 1) / 2 → h ∣ W.smulNumerator a ((N - 1) / 2) h

theorem IsCyclicKernel.monic {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

section Map

variable {T' : Type*} [CommRing T'] (f : T →+* T')

theorem smulNumerator_map (a d : ℕ) (h : T[X]) :
    (W.map f).smulNumerator a d (h.map f) = (W.smulNumerator a d h).map f := by
  simp only [smulNumerator, Polynomial.coeff_map, WeierstrassCurve.map_Φ,
    WeierstrassCurve.map_ΨSq, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]

theorem IsCyclicKernel.map {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) :
    (W.map f).IsCyclicKernel N (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_preΨ := by rw [WeierstrassCurve.map_preΨ]; exact Polynomial.map_dvd f hh.dvd_preΨ
  dvd_smulNumerator := fun a ha ha' => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha')

end Map

def kernelVariableChange (C : VariableChange T) (h : T[X]) : T[X] :=
  Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * h.natDegree)) * h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r)

def jOfUnit (hΔ : IsUnit W.Δ) : T :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  W.j

theorem jOfUnit_eq_j [W.IsElliptic] (hΔ : IsUnit W.Δ) : W.jOfUnit hΔ = W.j := rfl

theorem jOfUnit_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f).Δ) :
    (W.map f).jOfUnit hΔ' = f (W.jOfUnit hΔ) := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.map_j f

theorem jOfUnit_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (C • W).Δ) :
    (C • W).jOfUnit hΔ' = W.jOfUnit hΔ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.variableChange_j C

theorem isUnit_Δ_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) : IsUnit (W.map f).Δ := by
  rw [W.map_Δ]; exact hΔ.map f

theorem isUnit_Δ_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) : IsUnit (C • W).Δ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact (C • W).isUnit_Δ

end WeierstrassCurve

end
