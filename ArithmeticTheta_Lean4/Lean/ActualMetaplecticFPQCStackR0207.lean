import CoherentTautologicalLineR0207
import ActualFamilyFPQCDescentR0207
import ActualFamilyOpenDescentR0207

set_option autoImplicit false

namespace ArithmeticThetaMetaplecticStackR0207

/-- The actual family pseudofunctor is an fpqc stack with its coherently
normalized tautological root line. The coherence is constructed, and both
descent theorems apply to that same chosen pseudofunctor. -/
theorem actual_metaplectic_fpqc_stack :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L),
      ∃ C : ArithmeticThetaMetaplecticStackR0207.Coherence L
          (ArithmeticThetaLocalWeierstrassR0203.Base k),
        Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L
          (ArithmeticThetaLocalWeierstrassR0203.Base k) C) ∧
        CategoryTheory.Pseudofunctor.IsStack C.functor
          (ArithmeticThetaRootStackR0198.rootTopology
            (ArithmeticThetaLocalWeierstrassR0203.Base k)) := by
  intro k _ _ L hL heven
  obtain ⟨C⟩ := coherent_metaplectic_pullback L
    (ArithmeticThetaLocalWeierstrassR0203.Base k)
  refine ⟨C, coherent_tautological_line L
    (ArithmeticThetaLocalWeierstrassR0203.Base k) C, ?_⟩
  exact ArithmeticThetaRootStackR0198.fpqc_stack_criterion_over
    (ArithmeticThetaLocalWeierstrassR0203.Base k) C.functor
    (actual_family_open_descent k L hL heven C)
    (actual_family_fpqc_descent k L hL heven C)

end ArithmeticThetaMetaplecticStackR0207

#print axioms ArithmeticThetaMetaplecticStackR0207.actual_metaplectic_fpqc_stack
