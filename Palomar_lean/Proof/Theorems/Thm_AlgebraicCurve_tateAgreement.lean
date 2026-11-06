module

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
public import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_tateAgreement

@[expose] public section

theorem AlgebraicCurve.tateAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_tateAgreement.solution
