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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (u₁ u₂ : Spec (CommRingCat.of A) ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ u₁ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ u₂) :
    u₁ = u₂ := by
  let X' : Over Y := Over.mk (u₁ ≫ g)
  let Y' : Over Y := Over.mk g
  let f' : X' ⟶ Y' := Over.homMk u₁
  let g' : X' ⟶ Y' := Over.homMk u₂ hg.symm
  have hY'u : FormallyUnramified Y'.hom := ‹_›
  have hY'l : LocallyOfFiniteType Y'.hom := ‹_›
  let e := (equalizer.ι f' g').left

  have hopen : IsOpenImmersion e := by
    refine MorphismProperty.of_isPullback
      ((Limits.isPullback_equalizer_prod f' g').map (Over.forget _)).flip ?_
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
      (Over.prodLeftIsoPullback Y' Y').hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y'.hom))
    ext1 <;> simp [← Over.comp_left]

  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hpt : IsLocalRing.closedPoint A ∈ Set.range e := by
    let U' : Over Y := Over.mk (ρ ≫ u₁ ≫ g)
    let ι' : U' ⟶ X' := Over.homMk ρ
    have hl : (equalizer.lift ι' (by ext1; exact hres)).left ≫ e = ρ := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    let s : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) := (⊥ : PrimeSpectrum _)
    have hρs : ρ s = IsLocalRing.closedPoint A := by
      rw [Spec.map_apply]; exact IsLocalRing.PrimeSpectrum.comap_residue A s
    exact ⟨(equalizer.lift ι' (by ext1; exact hres)).left s, by rw [← hρs, ← hl]; rfl⟩

  have hsurj : Surjective e := ⟨fun y ↦
    (IsLocalRing.specializes_closedPoint y).mem_open e.isOpenEmbedding.isOpen_range hpt⟩
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr ⟨hopen, hsurj⟩
  have h12 : e ≫ u₁ = e ≫ u₂ := congr($(equalizer.condition f' g').left)
  exact (cancel_epi e).mp h12
