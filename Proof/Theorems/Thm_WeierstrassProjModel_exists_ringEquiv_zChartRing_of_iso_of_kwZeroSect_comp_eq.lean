module

public import Definitions.Def_FormalGroup_NSeries
public import Definitions.Def_WeierstrassCurve_FormalGroupLaw
public import Definitions.Def_WeierstrassCurve_ProjModel
public import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
public import Definitions.Def_WeierstrassCurve_PointChart
public import Definitions.Def_WeierstrassCurve_SectionAtOrigin
public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq

@[expose] public section
attribute [-simp] WeierstrassCurve.wIter_zero MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
    (T : Type) [CommRing T] (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (fromZeroRingHom (projModelGradingCR W'.toProjective) _ (algebraMap T ((projModelGradingCR W'.toProjective) 0) t)) =
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq.solution
