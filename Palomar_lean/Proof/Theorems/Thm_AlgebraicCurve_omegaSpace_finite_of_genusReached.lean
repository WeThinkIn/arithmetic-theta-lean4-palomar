module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_omegaSpace_finite_of_genusReached

@[expose] public section

namespace AlgebraicCurve
theorem omegaSpace_finite_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K ↥(omegaSpace (K := K) (F := F) D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached.solution
end AlgebraicCurve
