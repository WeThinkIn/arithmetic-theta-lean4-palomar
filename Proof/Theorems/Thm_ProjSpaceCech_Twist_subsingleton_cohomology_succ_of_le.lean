module

public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
public import P2M.Util
public import P2M.Sol.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le

@[expose] public section

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : i + 2 ≤ n) : Subsingleton (ProjSpaceCech.Twist.H R n d (i + 1)) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.solution
