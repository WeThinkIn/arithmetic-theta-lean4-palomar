module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finiteType_algebraOfHom
    {R : Type u} [CommRing R] {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [LocallyOfFiniteType t]
    (W : T.Opens) (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
    Algebra.FiniteType R Γ(T, W) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom.solution
