module

public import Mathlib.Topology.Sheaves.Abelian
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
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Γ Modules Opens evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

scoped instance : (toPresheaf X).Additive where
  map_add := by intros; rfl

noncomputable abbrev evalAt (U : X.Opens) : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} :=
  (CategoryTheory.evaluation _ Ab.{u}).obj (op U)

scoped instance (U : X.Opens) : (evalAt (X := X) U).Additive where
  map_add := by intros; rfl

theorem exists_app_eq_of_exact_of_app_eq_zero (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by

  have hK : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
  have hK₁ := KernelFork.mapIsLimit _ hK (toPresheaf X)
  have hPL : PreservesLimitsOfShape WalkingParallelPair (evalAt (X := X) U) :=
    evaluation_preservesLimitsOfShape _
  have hK' := @KernelFork.mapIsLimit _ _ _ _ _ _ _ _ _ _ hK₁ (evalAt (X := X) U) inferInstance
    (hPL.preservesLimit)

  let k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ (evalAt (X := X) U).obj ((toPresheaf X).obj S.X₂) :=
    AddCommGrpCat.ofHom ((zmultiplesHom Γ(S.X₂, U) m).comp AddEquiv.ulift.toAddMonoidHom)
  have hk1 : k (ULift.up (1 : ℤ)) = m := by
    change (zmultiplesHom Γ(S.X₂, U) m) (1 : ℤ) = m
    simp
  have hk : k ≫ (evalAt (X := X) U).map ((toPresheaf X).map S.g) = 0 := by
    ext ⟨z⟩
    change (S.g.app U) ((zmultiplesHom Γ(S.X₂, U) m) z) = 0
    rw [zmultiplesHom_apply, map_zsmul, hm, smul_zero]
  refine ⟨(KernelFork.IsLimit.lift' hK' k hk).1 (ULift.up (1 : ℤ)), ?_⟩
  have h := (KernelFork.IsLimit.lift' hK' k hk).2
  have h' := congr($h (ULift.up (1 : ℤ)))
  rw [hk1] at h'
  exact h'

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry"

theorem solution {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m :=
  AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS U m hm
