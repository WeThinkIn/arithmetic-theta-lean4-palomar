module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace.solution
