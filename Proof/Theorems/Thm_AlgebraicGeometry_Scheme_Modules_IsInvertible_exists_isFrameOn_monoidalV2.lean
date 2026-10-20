module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_MonoidalV2
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2.solution
