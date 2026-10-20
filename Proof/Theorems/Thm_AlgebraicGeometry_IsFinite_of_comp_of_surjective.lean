module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_IsFinite_of_comp_of_surjective

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsFinite.of_comp_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g] [IsSeparated g] : IsFinite g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_of_comp_of_surjective.solution
