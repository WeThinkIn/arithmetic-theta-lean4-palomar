module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_one_le_deg

@[expose] public section

namespace AlgebraicCurve
theorem one_le_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_one_le_deg.solution
end AlgebraicCurve
