module

public import Definitions.Def_AlgebraicGeometry_IdealSheafModule
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_AlgebraicCurve_RelCartier
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    Scheme.Modules.IsInvertible I.module := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.solution
