module

public import Mathlib
public import Definitions.Def_PresheafOfModules_ExteriorPower
public import Definitions.Def_AlgebraicGeometry_ModulesDet
public import Definitions.Def_AlgebraicGeometry_KaehlerModule
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (f.kaehlerToSections U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.solution
