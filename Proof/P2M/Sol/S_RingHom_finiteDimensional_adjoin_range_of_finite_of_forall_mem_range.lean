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
namespace P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range

namespace SolChiFinField

theorem isIntegral_apply
    {R S A K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [CommRing A] [CommRing K] [Algebra A K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap A K).range) (s : S) :
    IsIntegral A (χ' s) := by
  classical
  nontriviality K
  obtain ⟨p, hpm, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
  set χ : R →+* K := χ'.comp (algebraMap R S) with hχ
  have hlift : p.map χ ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := h (p.coeff n)
    exact ⟨a, ha⟩
  obtain ⟨q, hq, -, hqm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift (hpm.map χ)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂,
    hps, map_zero]

end SolChiFinField

theorem solution
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite R S)
  have hint : ∀ x ∈ (χ' '' (t : Set S)), IsIntegral E x := by
    rintro _ ⟨s, -, rfl⟩
    exact SolChiFinField.isIntegral_apply χ' h s
  have hsub : Set.range χ' ⊆ IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    rintro _ ⟨s, rfl⟩
    have hs : s ∈ Submodule.span R (t : Set S) := by rw [ht]; exact Submodule.mem_top
    induction hs using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      obtain ⟨a, ha⟩ := h r
      rw [← ha]
      exact mul_mem (IntermediateField.algebraMap_mem _ a) hx
  have heq : IntermediateField.adjoin E (Set.range χ')
      = IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    apply le_antisymm (IntermediateField.adjoin_le_iff.mpr hsub)
    exact IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  rw [heq]
  haveI : Finite (χ' '' (t : Set S)) := Set.toFinite _
  exact IntermediateField.finiteDimensional_adjoin hint
