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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_IsLocalRing_comap_map_adicCompletion_eq

set_option autoImplicit false

namespace C4sol
open IsLocalRing

theorem faithfullyFlat_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩

  have hm' : m = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hm)
  subst hm'
  intro htop

  have hle : (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := by
    have := AdicCompletion.pow_smul_top_le_ker_eval (I := maximalIdeal R) (M := R) 1
    simpa using this
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle

  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  rw [hle] at hsurj
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk 1)
  simp only [LinearMap.zero_apply] at hx
  have h1 : (1 : R) ∈ (maximalIdeal R) ^ 1 • (⊤ : Submodule R R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hx]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

end C4sol

open IsLocalRing in
theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  haveI := C4sol.faithfullyFlat_adicCompletion R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I
