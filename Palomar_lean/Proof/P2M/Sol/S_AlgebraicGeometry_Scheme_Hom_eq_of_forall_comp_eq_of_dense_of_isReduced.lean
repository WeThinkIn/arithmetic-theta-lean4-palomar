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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Henselian
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
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DenseSetAgree

theorem epi_specMap_of_field {κ k : Type u} [Field κ] [Field k] (φ : CommRingCat.of κ ⟶ CommRingCat.of k) :
    Epi (Spec.map φ) := by
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI : Algebra κ k := φ.hom.toAlgebra
    show Module.Flat κ k
    infer_instance
  haveI : Surjective (Spec.map φ) := ⟨fun p => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end DenseSetAgree

theorem solution
    {X Y S : Scheme.{u}} [IsReduced X]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (D : Set ↥X) (hD : Dense D)
    (h : ∀ x ∈ D, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ X),
      x ∈ Set.range y.base ∧ y ≫ F = y ≫ G) :
    F = G := by
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq F G i D hD (fun x hx => ?_) hFG
  obtain ⟨k, _, y, ⟨p, rfl⟩, hy⟩ := h x hx
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  haveI := DenseSetAgree.epi_specMap_of_field (X.descResidueField (Scheme.stalkClosedPointTo y))
  rw [← cancel_epi (Spec.map (X.descResidueField (Scheme.stalkClosedPointTo y))), ← Category.assoc, ← Category.assoc,
    X.descResidueField_stalkClosedPointTo_fromSpecResidueField k y]
  exact hy
