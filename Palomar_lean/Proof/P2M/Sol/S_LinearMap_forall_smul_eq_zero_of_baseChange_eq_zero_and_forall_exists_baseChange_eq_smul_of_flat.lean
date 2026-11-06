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
namespace P2MW.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat

set_option autoImplicit false

universe u v w w'

open TensorProduct

theorem solution
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] {N : Type w'} [AddCommGroup N] [Module R₀ N]
    (u : M →ₗ[R₀] N) (J : Ideal R₀)
    (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
    (∀ x : R ⊗[R₀] M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ (y : R ⊗[R₀] N), ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : R ⊗[R₀] M, u.baseChange R x = a • y) := by
  set φ := algebraMap R₀ R with hφ
  constructor
  ·
    intro x hx
    have hex : Function.Exact ((LinearMap.ker u).subtype.lTensor R) (u.lTensor R) :=
      Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map u)
    have hx' : u.lTensor R x = 0 := by rw [← LinearMap.baseChange_eq_ltensor]; exact hx
    obtain ⟨z, rfl⟩ := (hex x).1 hx'

    have hkill : ∀ j ∈ J, ∀ z : R ⊗[R₀] (LinearMap.ker u), j • z = 0 := by
      intro j hj z
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero]
      | tmul r k =>
        have : j • k = 0 := Subtype.ext (by simpa using hk k.1 k.2 j hj)
        rw [← TensorProduct.tmul_smul, this, TensorProduct.tmul_zero]
      | add a b ha hb => rw [smul_add, ha, hb, add_zero]

    suffices h : J.map φ ≤ Ideal.torsionOf R _ ((LinearMap.ker u).subtype.lTensor R z) by
      intro a ha; exact (Ideal.mem_torsionOf_iff _ _).1 (h ha)
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, algebraMap_smul, ← LinearMap.map_smul, hkill j hj z, map_zero]
  ·
    intro y a ha
    suffices h : (J.map φ) • (⊤ : Submodule R (R ⊗[R₀] N)) ≤ LinearMap.range (u.baseChange R) by
      exact h (Submodule.smul_mem_smul ha (Submodule.mem_top : y ∈ ⊤))
    have h1 : ((J.map φ) • (⊤ : Submodule R (R ⊗[R₀] N))).restrictScalars R₀ ≤
        (LinearMap.range (u.baseChange R)).restrictScalars R₀ := by
      rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top, Submodule.smul_le]
      rintro j hj y -
      show j • y ∈ LinearMap.range (u.baseChange R)
      induction y using TensorProduct.induction_on with
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | tmul r n =>
        obtain ⟨x, hx⟩ := hc n j hj
        refine ⟨r ⊗ₜ x, ?_⟩
        rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_smul]
      | add a b ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    exact fun v hv => h1 hv
