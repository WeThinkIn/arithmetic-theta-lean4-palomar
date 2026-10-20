module

public import Mathlib
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.projectionMorphism_naturality
    {Z X : Scheme.{u}} (i : Z ⟶ X) {F F' : X.Modules} (φ : F ⟶ F') :
    Scheme.Modules.projectionMorphism i F ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫ Scheme.Modules.projectionMorphism i F' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality.solution
