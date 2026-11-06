module

public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_addMorphism_gluing

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_gluing.{u} {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLRSixUCoverage W ∧ KwLRPerChartCompat W ∧ KwLROuterCompat W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_gluing.solution
