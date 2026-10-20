module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
public import P2M.Util
public import P2M.Sol.S_ProjSpaceCech_Twist_d_sq

@[expose] public section

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.d_sq (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    ProjSpaceCech.Twist.d R n d (i + 1) ∘ₗ ProjSpaceCech.Twist.d R n d i = 0 := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_d_sq.solution
