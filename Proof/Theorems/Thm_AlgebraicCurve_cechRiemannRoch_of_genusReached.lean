module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicGeometry_TwoChartCech
public import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached

@[expose] public section

namespace AlgebraicCurve
theorem cechRiemannRoch_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached.solution
end AlgebraicCurve
