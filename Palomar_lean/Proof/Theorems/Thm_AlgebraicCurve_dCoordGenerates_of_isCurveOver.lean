module

public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_ModularCurve_CanonicalDivisor
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver

@[expose] public section

namespace AlgebraicCurve

theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.solution
