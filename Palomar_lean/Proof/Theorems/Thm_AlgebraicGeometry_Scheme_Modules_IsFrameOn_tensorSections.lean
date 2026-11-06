module

public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorSections s t) V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.solution
