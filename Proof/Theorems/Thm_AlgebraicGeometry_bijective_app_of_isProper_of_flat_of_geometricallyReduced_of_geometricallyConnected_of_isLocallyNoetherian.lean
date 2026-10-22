module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian

@[expose] public section
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
    {X B : Scheme.{u}} [IsLocallyNoetherian B] (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] [GeometricallyConnected p] (U : B.Opens) :
    Function.Bijective (p.app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian.solution
