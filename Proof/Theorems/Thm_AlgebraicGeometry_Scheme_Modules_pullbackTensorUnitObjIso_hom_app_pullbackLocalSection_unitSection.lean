module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_PresheafOfModules_PullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.solution
