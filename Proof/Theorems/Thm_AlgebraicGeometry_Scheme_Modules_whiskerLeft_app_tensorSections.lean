module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) {M M' : X.Modules} (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ◁ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections s (ψ.app U t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections.solution
