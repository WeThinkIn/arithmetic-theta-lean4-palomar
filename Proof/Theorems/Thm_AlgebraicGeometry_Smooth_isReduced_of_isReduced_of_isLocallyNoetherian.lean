module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.solution
