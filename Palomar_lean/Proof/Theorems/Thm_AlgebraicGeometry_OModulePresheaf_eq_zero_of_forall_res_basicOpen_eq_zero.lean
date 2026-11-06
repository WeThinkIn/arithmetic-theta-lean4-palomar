module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1)) (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1) (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.solution
