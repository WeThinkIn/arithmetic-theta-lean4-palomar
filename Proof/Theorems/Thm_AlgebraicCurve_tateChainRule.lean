module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_ModularCurve_CanonicalDivisor
public import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_CanonicalDivisor
public import Definitions.Def_AlgebraicCurve_LocalResidue
public import Definitions.Def_AlgebraicCurve_DivisorPushPull
public import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
public import Definitions.Def_AlgebraicCurve_PlaceCompletion
public import Definitions.Def_AlgebraicCurve_TateResidueCurrency
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_tateChainRule

@[expose] public section

theorem AlgebraicCurve.tateChainRule
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_tateChainRule.solution
