module

public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) :
    IsOriginChartSection (kwZeroSect T W.toAffine) (kwYChartEval T W.toAffine) ∧
      kwYChartEval T W.toAffine (xOverY W) = 0 ∧ kwYChartEval T W.toAffine (zOverY W) = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval.solution
