module

public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
public import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
public import P2M.Util
public import P2M.Sol.S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective

@[expose] public section

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n}
    (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂) (h : ∀ i, Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective.solution
