module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_ell_eq_zero_of_degree_neg

@[expose] public section

namespace AlgebraicCurve
theorem ell_eq_zero_of_degree_neg {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_eq_zero_of_degree_neg.solution
end AlgebraicCurve
