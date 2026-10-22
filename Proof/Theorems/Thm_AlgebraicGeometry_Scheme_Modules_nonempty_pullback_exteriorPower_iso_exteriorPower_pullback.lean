module

public import Definitions.Def_AlgebraicGeometry_ModulesDet
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

@[expose] public section
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback {X : Scheme.{u}} (n : ℕ) (U : X.Opens) (M : X.Modules) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.exteriorPower X n).obj M) ≅
      (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).obj ((Scheme.Modules.pullback U.ι).obj M)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.solution
