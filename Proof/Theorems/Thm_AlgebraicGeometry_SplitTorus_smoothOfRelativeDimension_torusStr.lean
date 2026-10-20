module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_SplitTorusMu
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.smoothOfRelativeDimension_torusStr
    (S : Type u) [CommRing S] (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d S (torusCoord S d) ∧
      SmoothOfRelativeDimension d (torusStr S d) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr.solution
