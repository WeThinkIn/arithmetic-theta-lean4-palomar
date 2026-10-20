module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection.solution
