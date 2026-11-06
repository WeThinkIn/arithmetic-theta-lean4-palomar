module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.solution
