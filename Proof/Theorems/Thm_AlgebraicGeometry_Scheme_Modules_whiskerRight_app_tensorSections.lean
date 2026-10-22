module

public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.whiskerRight_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (φ : L ⟶ L') (M : X.Modules) {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ▷ M).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections.solution
