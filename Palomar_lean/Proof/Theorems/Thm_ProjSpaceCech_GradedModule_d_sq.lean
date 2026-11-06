module

public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
public import P2M.Util
public import P2M.Sol.S_ProjSpaceCech_GradedModule_d_sq

@[expose] public section

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.d_sq {R : Type u} [CommRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_d_sq.solution
