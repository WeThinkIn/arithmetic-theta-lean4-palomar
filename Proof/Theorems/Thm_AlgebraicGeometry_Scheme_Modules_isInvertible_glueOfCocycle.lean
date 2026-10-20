module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle.solution
