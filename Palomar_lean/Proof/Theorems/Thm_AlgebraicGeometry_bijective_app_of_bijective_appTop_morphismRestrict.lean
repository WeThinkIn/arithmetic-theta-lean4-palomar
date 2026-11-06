module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict {X B : Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.solution
