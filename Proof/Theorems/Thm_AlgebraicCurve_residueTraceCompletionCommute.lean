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
public import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_residueTraceCompletionCommute

@[expose] public section
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

theorem AlgebraicCurve.residueTraceCompletionCommute
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.solution
