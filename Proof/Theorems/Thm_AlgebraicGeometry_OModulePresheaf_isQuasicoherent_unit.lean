module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_unit
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) :
    (OModulePresheaf.unit π).IsQuasicoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit.solution
