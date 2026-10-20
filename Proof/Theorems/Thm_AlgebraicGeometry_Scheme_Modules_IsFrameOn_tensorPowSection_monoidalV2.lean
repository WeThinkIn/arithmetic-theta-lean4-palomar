module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_MonoidalV2
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2.solution
