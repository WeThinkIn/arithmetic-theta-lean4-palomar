module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.solution
