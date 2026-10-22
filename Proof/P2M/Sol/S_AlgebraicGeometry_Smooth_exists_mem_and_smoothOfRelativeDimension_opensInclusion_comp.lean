module

public import Mathlib.Tactic.ReduceModChar
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RingHom p2m_export "RingHom" "Smooth IsStandardSmoothOfRelativeDimension locally_of toMorphismProperty_respectsIso_iff isStandardSmoothOfRelativeDimension_respectsIso locally_respectsIso Locally toMorphismProperty IsStandardSmooth toAlgebra" namespace IsStandardSmooth p2m_export "RingHom.IsStandardSmooth" "toAlgebra smooth" end RingHom.IsStandardSmooth
p2m_open_scoped "RingHom RingHom.IsStandardSmooth" in

theorem RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3
    {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  letI := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3 hstd
  refine ⟨V, d, hx, ?_⟩

  have hres : SmoothOfRelativeDimension d (f.resLE U V e) := by
    haveI : IsAffine V := hV
    haveI : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have := (RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))))
    refine ((MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))) (arrowResLEAppIso f U V e)).mpr ?_)
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _ hd
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  simpa using this
