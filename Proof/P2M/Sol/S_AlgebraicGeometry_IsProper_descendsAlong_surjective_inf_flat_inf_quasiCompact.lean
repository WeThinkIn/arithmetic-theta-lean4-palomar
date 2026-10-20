module

public import Mathlib
public import Theorems.Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
public import Theorems.Thm_AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact
public import P2M.Util

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace P2MW.S_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry"

theorem solution :
    DescendsAlong (@IsProper : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have := AlgebraicGeometry.LocallyOfFiniteType.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  rw [isProper_eq]
  infer_instance
