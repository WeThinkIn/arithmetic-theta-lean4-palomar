module

public import Definitions.Def_PresheafOfModules_InternalHom
public import Definitions.Def_SheafOfModules_MonoidalV2
public import Definitions.Def_PresheafOfModules_PullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) {L M : Y.Modules} {U : Y.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso φ L M).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.tensorSections s t)) =
    AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ s)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2.solution
