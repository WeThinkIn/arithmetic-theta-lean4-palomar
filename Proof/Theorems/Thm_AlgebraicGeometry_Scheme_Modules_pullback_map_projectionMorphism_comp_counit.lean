module

public import Mathlib
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_projectionMorphism_comp_counit
    {Z X : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback i).map (Scheme.Modules.projectionMorphism i F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app ((Scheme.Modules.pullback i).obj F) =
      Scheme.Modules.projectionMorphismMate i F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit.solution
