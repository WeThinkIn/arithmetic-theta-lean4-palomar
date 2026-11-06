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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom Hom.image_preimage_eq_opensRange_inf restrictFunctor Modules Opens Opens.opensRange_ι"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback Hom restrictFunctor restrictFunctorIsoPullback Hom.isIso_iff_isIso_app Hom.isIso_of_isIso_app_of_iSup_eq_top"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma restrictFunctor_map_app' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) :
    ((restrictFunctor U.ι).map φ).app W = φ.app (U.ι ''ᵁ W) := rfl

lemma isIso_app_of_isIso_pullback_ι_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) (W : X.Opens) (hWU : W ≤ U) :
    IsIso (φ.app W) := by
  have h1 : IsIso ((restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).2 hU
  have h2 := Hom.isIso_iff_isIso_app.1 h1 (U.ι ⁻¹ᵁ W)
  rw [restrictFunctor_map_app'] at h2
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  rw [← e]
  exact h2

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.solution {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by
  choose U hxU hU using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top φ U ?_ (fun x V hV => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact isIso_app_of_isIso_pullback_ι_map φ (U x) (hU x) V hV

#print axioms solution

end AlgebraicGeometry.Scheme.Modules
