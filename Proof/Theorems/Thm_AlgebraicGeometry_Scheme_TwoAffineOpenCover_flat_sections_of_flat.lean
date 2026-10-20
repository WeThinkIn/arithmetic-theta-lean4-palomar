module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat.solution
