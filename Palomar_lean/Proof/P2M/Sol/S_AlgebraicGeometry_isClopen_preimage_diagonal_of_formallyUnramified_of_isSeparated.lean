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
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {Z S : Scheme.{u}} (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    (σ τ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) :
    IsClopen ((pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : S.Opens) : Set S) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ S),
      Set.range g ⊆ (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : Set S) ↔ g ≫ σ = g ≫ τ := by
  haveI : IsOpenImmersion (pullback.diagonal p) := inferInstance
  haveI : IsClosedImmersion (pullback.diagonal p) := inferInstance
  refine ⟨⟨?_, (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange).2⟩, ?_⟩
  ·
    show IsClosed ((pullback.lift σ τ (hσ.trans hτ.symm)) ⁻¹' Set.range (pullback.diagonal p))
    exact ((pullback.diagonal p).isClosedEmbedding.isClosed_range).preimage (pullback.lift σ τ _).continuous
  · intro T g
    constructor
    · intro hg
      have hrange : Set.range (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) ⊆ Set.range (pullback.diagonal p) := by
        rintro _ ⟨t, rfl⟩
        exact hg ⟨t, rfl⟩
      let h : T ⟶ Z := IsOpenImmersion.lift (pullback.diagonal p) (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) hrange
      have hh : h ≫ pullback.diagonal p = g ≫ pullback.lift σ τ (hσ.trans hτ.symm) :=
        IsOpenImmersion.lift_fac _ _ hrange
      have h1 : h = g ≫ σ := by
        have := congrArg (· ≫ pullback.fst p p) hh
        simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
        exact this
      have h2 : h = g ≫ τ := by
        have := congrArg (· ≫ pullback.snd p p) hh
        simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at this
        exact this
      rw [← h1, h2]
    · intro hστ
      rintro _ ⟨t, rfl⟩
      show (pullback.lift σ τ (hσ.trans hτ.symm)) (g t) ∈ Set.range (pullback.diagonal p)
      have hfac : g ≫ pullback.lift σ τ (hσ.trans hτ.symm) = (g ≫ σ) ≫ pullback.diagonal p := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hστ]
      refine ⟨(g ≫ σ) t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]
