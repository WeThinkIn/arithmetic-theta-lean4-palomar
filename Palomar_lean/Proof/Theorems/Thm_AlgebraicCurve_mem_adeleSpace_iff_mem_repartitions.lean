module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions

@[expose] public section

namespace AlgebraicCurve
theorem mem_adeleSpace_iff_mem_repartitions {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions.solution
end AlgebraicCurve
