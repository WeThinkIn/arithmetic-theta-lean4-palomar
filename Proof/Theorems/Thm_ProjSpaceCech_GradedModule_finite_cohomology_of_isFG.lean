module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
public import P2M.Util
public import P2M.Sol.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG

@[expose] public section

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.finite_cohomology_of_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n)
    (hD : ProjSpaceCech.GradedModule.IsFG D) (i : ℕ) : Module.Finite R (ProjSpaceCech.GradedModule.H D i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG.solution
