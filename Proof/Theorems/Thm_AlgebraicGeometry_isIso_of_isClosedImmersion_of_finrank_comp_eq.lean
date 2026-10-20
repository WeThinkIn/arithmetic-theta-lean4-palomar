module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.solution
