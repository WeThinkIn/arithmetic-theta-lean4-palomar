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
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsClosedImmersion.of_isPreimmersion UniversallyClosed QuasiCompact Scheme Flat IsClosedImmersion IsSeparated"
namespace IsSeparatedDescentAux
p2m_open "AlgebraicGeometry"

theorem isSeparated_iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [MorphismProperty.diagonal_iff]
  exact isSeparated_iff_universallyClosed_diagonal f

end AlgebraicGeometry.IsSeparatedDescentAux

theorem solution :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [AlgebraicGeometry.IsSeparatedDescentAux.isSeparated_eq_diagonal_universallyClosed]
  infer_instance
