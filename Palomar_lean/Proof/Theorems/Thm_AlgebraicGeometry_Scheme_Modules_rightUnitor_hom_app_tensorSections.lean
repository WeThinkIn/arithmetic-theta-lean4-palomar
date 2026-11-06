module

public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections.solution
