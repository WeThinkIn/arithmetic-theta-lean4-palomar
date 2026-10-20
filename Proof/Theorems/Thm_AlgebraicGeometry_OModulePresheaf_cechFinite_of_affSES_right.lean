module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Noetherian.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right.solution
