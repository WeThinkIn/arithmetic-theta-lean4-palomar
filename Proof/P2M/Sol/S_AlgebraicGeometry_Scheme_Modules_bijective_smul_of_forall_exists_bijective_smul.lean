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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.ENatToNat
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameLocalSol

variable {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤))

noncomputable abbrev res (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

theorem res_map {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

noncomputable def abSheaf : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem main (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • res M σ W) :
    Function.Bijective fun g : Γ(X, V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  · intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    show X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) =
      X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  · intro s
    have hloc : ∀ x, ∃! g : Γ(X, W x), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx hgx_uniq using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      show X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) =
        X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight (W x) (W y)),
        hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    show M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV x)).op s
    rw [smul_res, ← hgx x]
    exact congrArg (· • res M σ (W x)) (hg x)

end FrameLocalSol

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) :=
  FrameLocalSol.main M σ V h
