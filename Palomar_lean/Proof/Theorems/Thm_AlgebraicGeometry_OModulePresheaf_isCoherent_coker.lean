module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.isCoherent_coker {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.solution
