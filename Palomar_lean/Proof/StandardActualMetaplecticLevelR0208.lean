module

public import FiniteEtaleActualLevelR0208
public import ActualMetaplecticFPQCStackR0207

@[expose] public section

set_option autoImplicit false

namespace ArithmeticThetaActualLevelR0208

/-- One universal provider and one coherent actual family stack realize every
finite étale level with its specified Hodge square root. -/
theorem standard_actual_metaplectic_level :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L), ∃ (P : ArithmeticThetaActualLevelR0208.Provider k L) (C : ArithmeticThetaMetaplecticStackR0207.Coherence L (ArithmeticThetaLocalWeierstrassR0203.Base k)), Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L (ArithmeticThetaLocalWeierstrassR0203.Base k) C) ∧ CategoryTheory.Pseudofunctor.IsStack C.functor (ArithmeticThetaRootStackR0198.rootTopology (ArithmeticThetaLocalWeierstrassR0203.Base k)) ∧ ∀ (Y : CategoryTheory.Over (ArithmeticThetaLocalWeierstrassR0203.Base k)) (p : Quiver.Hom Y (ArithmeticThetaActualLevelR0208.base P)) (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left ((AlgebraicGeometry.Scheme.Modules.pullback p.left).obj (ArithmeticThetaActualLevelR0208.hodge P))), AlgebraicGeometry.IsFinite p.left → AlgebraicGeometry.Etale p.left → Nonempty (ArithmeticThetaActualLevelR0208.PullbackComparison (ArithmeticThetaActualLevelR0208.canonicalMap C Y (ArithmeticThetaActualLevelR0208.object P p H))) ∧ ArithmeticThetaActualLevelR0208.FiniteEtaleLevel P p H (ArithmeticThetaActualLevelR0208.canonicalMap C Y (ArithmeticThetaActualLevelR0208.object P p H)) := by
  intro k _ _ L hL heven
  obtain ⟨P⟩ := ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.provider_exists
    k L hL heven
  obtain ⟨C, hforget, hstack⟩ :=
    ArithmeticThetaMetaplecticStackR0207.actual_metaplectic_fpqc_stack k L hL heven
  refine ⟨P, C, hforget, hstack, ?_⟩
  intro Y p H hfin het
  exact ⟨actual_anchored_pullback k L C Y (object P p H)
      (canonicalMap C Y (object P p H)),
    finite_etale_actual_level k L hL heven P C Y p H
      (canonicalMap C Y (object P p H)) hfin het⟩

end ArithmeticThetaActualLevelR0208

#print axioms ArithmeticThetaActualLevelR0208.standard_actual_metaplectic_level
