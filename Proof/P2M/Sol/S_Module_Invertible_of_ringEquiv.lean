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
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_Module_Invertible_of_ringEquiv

set_option autoImplicit false

universe u v

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    (M : Type v) [AddCommGroup M] [Module R' M] [Module.Invertible R' M]
    [Module R M] (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
    Module.Invertible R M := by
  letI : Algebra R' R := σ.symm.toRingHom.toAlgebra
  haveI : IsScalarTower R' R M := ⟨fun r' r m => by
    rw [Algebra.smul_def, hσ, hσ r m, ← mul_smul]
    congr 1
    simp [RingHom.algebraMap_toAlgebra]⟩
  haveI : IsLocalization (⊥ : Submonoid R') R :=
    IsLocalization.of_le_isUnit_of_bijective
      (by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp)
      σ.symm.bijective
  haveI : IsLocalizedModule (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M) :=
    isLocalizedModule_id (S := (⊥ : Submonoid R')) (M := M) (R' := R)
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M)
