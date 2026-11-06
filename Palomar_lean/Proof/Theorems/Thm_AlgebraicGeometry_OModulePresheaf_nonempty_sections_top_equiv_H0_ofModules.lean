module

public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (M : V.Modules) (K : V.OrderedAffineCover) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Nonempty (Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.solution
