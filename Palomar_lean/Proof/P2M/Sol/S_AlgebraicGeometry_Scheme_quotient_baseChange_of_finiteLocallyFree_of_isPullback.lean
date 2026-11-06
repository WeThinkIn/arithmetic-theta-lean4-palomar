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
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by

  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hX inferInstance
  haveI : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  haveI : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  haveI : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance

  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_)
      (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    ·
      refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc, c.condition]
      · rw [IsPullback.lift_fst]
    · exact hsq.lift_snd _ _ _
    ·
      apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    · apply hsq.hom_ext
      · rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      · rw [hsq.lift_snd]
        exact hm₁

  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  exact hk.toCoequalizer (regularEpiOfEffectiveEpi p')
