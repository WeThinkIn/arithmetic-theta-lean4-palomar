module

public import Definitions.Def_AlgebraicCurve_RelCartier
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_isIntegral
    {X Y : Scheme.{u}} [IsIntegral X] {I : Y.IdealSheafData} (hI : I.IsInvertible) (g : X ⟶ Y)
    (h : ((I.comap g).support : Set X) ≠ Set.univ) : (I.comap g).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral.solution
