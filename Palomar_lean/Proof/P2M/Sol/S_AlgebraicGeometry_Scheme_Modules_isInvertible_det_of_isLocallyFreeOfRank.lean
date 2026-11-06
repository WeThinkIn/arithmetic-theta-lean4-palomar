module

public import Definitions.Def_AlgebraicGeometry_ModulesDet
public import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsInvertible (Scheme.Modules.det n M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback n U M
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (U : Scheme.{u}) n
  exact ⟨U, hxU, ⟨e₁ ≪≫ (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).mapIso e ≪≫ e₂⟩⟩
