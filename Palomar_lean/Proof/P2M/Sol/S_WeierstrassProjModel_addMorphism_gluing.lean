module

public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Theorems.Thm_WeierstrassProjModel_kw_a2_sixu_cov
public import Theorems.Thm_WeierstrassProjModel_perChartCompat_of_smooth
public import Theorems.Thm_WeierstrassProjModel_outerCompat_of_smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import P2M.Util

@[expose] public section
namespace P2MW.S_WeierstrassProjModel_addMorphism_gluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel in
theorem solution.{u} {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLRSixUCoverage W ∧ KwLRPerChartCompat W ∧ KwLROuterCompat W :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  ⟨WeierstrassProjModel.kw_a2_sixu_cov W,
    WeierstrassProjModel.perChartCompat_of_smooth W hsm hgi hΔ,
    WeierstrassProjModel.outerCompat_of_smooth W hsm hgi hΔ⟩
