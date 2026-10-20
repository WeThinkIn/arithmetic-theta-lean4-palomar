module

public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_addMorphism_mul_zeroSect

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_mul_zeroSect.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (𝟙 (projModelCR W.toProjective)) (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1)
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_mul_zeroSect.solution
