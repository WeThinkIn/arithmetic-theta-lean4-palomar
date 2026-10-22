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
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CLOPENSECT

theorem hasOfPostcompProperty_isOpenImmersion_unramified :
    MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ f hf ↦ by
      obtain ⟨h₁, h₂⟩ := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))

theorem main {S T : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by
  haveI : IsOpenImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact ⟨hasOfPostcompProperty_isOpenImmersion_unramified.of_postcomp s g ⟨‹_›, ‹_›⟩ ‹_›,
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) s g ‹_› ‹_›⟩

end CLOPENSECT

theorem solution
    {S T : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  CLOPENSECT.main g s hs
