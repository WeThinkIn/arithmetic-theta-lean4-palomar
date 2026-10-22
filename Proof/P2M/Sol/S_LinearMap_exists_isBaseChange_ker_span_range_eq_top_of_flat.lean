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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat

set_option autoImplicit false

universe u v

namespace PresBCSol

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

noncomputable abbrev φ (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → S) :=
  (Algebra.linearMap R S).compLeft (Fin n)

theorem φ_apply (n : ℕ) (v : Fin n → R) (i : Fin n) : φ R S n v i = algebraMap R S (v i) := rfl

theorem isBaseChange_φ (n : ℕ) : IsBaseChange S (φ R S n) :=
  IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R S)

theorem mem_span_of_isBaseChange {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (y : N) :
    y ∈ Submodule.span S (Set.range f) := by
  induction y using hf.inductionOn with
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ s hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

end PresBCSol

open PresBCSol in
theorem solution
    {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    ∃ g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' g ∧
      Submodule.span B' (Set.range g) = ⊤ := by
  classical
  have hφ : IsBaseChange B' (φ B B' r) := isBaseChange_φ r
  have hp'' : ∀ v, p' (φ B B' r v) = μ (p v) := hp'
  let g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p') :=
    LinearMap.codRestrict ((LinearMap.ker p').restrictScalars B) ((φ B B' r) ∘ₗ (LinearMap.ker p).subtype)
      (fun s => by
        show p' (φ B B' r s) = 0
        rw [hp'', (LinearMap.mem_ker).mp s.2, map_zero])
  have hg : IsBaseChange B' g := by
    refine IsBaseChange.of_left_exact B' g (φ B B' r) μ (f := (LinearMap.ker p).subtype) (g := p)
      (f' := (LinearMap.ker p').subtype) (g' := p') ?_ ?_ hφ hμ ?_ ?_ ?_ ?_
    · exact LinearMap.ext fun s => rfl
    · exact LinearMap.ext fun v => (hp'' v).symm
    · exact LinearMap.exact_subtype_ker_map p
    · exact Subtype.val_injective
    · exact LinearMap.exact_subtype_ker_map p'
    · exact Subtype.val_injective
  refine ⟨g, fun s i => rfl, hg, ?_⟩
  rw [eq_top_iff]
  rintro y -
  exact mem_span_of_isBaseChange hg y
