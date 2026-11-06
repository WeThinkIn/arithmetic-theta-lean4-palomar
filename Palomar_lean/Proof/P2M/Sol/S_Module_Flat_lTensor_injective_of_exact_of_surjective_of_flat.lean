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
namespace P2MW.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat

set_option autoImplicit false

universe u

open TensorProduct

namespace UE1Aux

theorem sq {R : Type u} [CommRing R] {X Y X' Y' : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    (a : X →ₗ[R] X') (b : Y →ₗ[R] Y') (t : X ⊗[R] Y) :
    b.lTensor X' (a.rTensor Y t) = a.rTensor Y' (b.lTensor X t) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

theorem chase {R : Type u} [CommRing R] {N M P A K F : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup A] [Module R A] [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (ι : K →ₗ[R] F) (π : F →ₗ[R] A) (hι : Function.Injective ι) (hιπ : Function.Exact ι π)
    (hπ : Function.Surjective π) [Module.Flat R F] :
    Function.Injective (f.lTensor A) := by

  have colP : Function.Injective (ι.rTensor P) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have rowF : Function.Injective (f.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have rowK : Function.Exact (f.lTensor K) (g.lTensor K) := lTensor_exact K hfg hg
  have colM : Function.Exact (ι.rTensor M) (π.rTensor M) := rTensor_exact M hιπ hπ
  have colN : Function.Exact (ι.rTensor N) (π.rTensor N) := rTensor_exact N hιπ hπ
  have colN' : Function.Surjective (π.rTensor N) := LinearMap.rTensor_surjective N hπ
  have hgf : g ∘ₗ f = 0 := hfg.linearMap_comp_eq_zero

  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := colN' x
  rw [sq] at hx
  obtain ⟨z, hz⟩ := (colM _).mp hx
  have hz0 : g.lTensor K z = 0 := by
    apply colP
    rw [map_zero, ← sq, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgf,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w, hw⟩ := (rowK z).mp hz0
  have hwy : ι.rTensor N w = y := by
    apply rowF
    rw [sq, hw, hz]
  rw [← hwy]
  exact colN.apply_apply_eq_zero w

end UE1Aux

theorem solution
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) :=
  UE1Aux.chase (K := LinearMap.ker (Finsupp.linearCombination R (id : A → A))) f g hf hfg hg
    (LinearMap.ker (Finsupp.linearCombination R (id : A → A))).subtype
    (Finsupp.linearCombination R (id : A → A))
    (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_ker_map (Finsupp.linearCombination R (id : A → A)))
    (Finsupp.linearCombination_id_surjective R A)
