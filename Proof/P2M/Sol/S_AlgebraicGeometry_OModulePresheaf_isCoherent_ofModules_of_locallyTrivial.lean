module

public import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Defs
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    (OModulePresheaf.ofModules π M).IsCoherent :=
  fun U => Scheme.Modules.finite_sections_of_locallyTrivial M htriv U
