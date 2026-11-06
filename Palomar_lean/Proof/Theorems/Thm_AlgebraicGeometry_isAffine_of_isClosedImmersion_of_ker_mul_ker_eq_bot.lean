module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [IsAffine X₀]
    (h : i.ker * i.ker = ⊥) : IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot.solution
