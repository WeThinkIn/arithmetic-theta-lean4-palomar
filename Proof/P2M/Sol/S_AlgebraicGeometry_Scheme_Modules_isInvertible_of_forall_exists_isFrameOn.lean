module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_PresheafOfModules_InternalHom
public import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, s, hx, hs⟩ := h x
  exact ⟨U, hx, AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hs U le_rfl le_rfl⟩
