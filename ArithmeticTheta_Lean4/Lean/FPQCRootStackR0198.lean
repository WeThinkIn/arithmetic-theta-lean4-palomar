import RootModuliPseudofunctorR0198
import CategoricalRootDescentR0198
import FPQCStackCriterionOverR0198

set_option autoImplicit false

namespace ArithmeticThetaRootStackR0198

/-- The groupoids of actual specified square roots of an invertible sheaf form
a stack for the standard big fpqc topology on schemes over the base. The
presentation includes the coherent tautological line and its square map. -/
theorem fpqc_root_stack
    (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (hW : AlgebraicGeometry.Scheme.Modules.IsInvertible W) :
    ∃ P : ArithmeticThetaRootStackR0198.Presentation B W,
      P.functor.IsStack (ArithmeticThetaRootStackR0198.rootTopology B) := by
  obtain ⟨P⟩ := root_moduli_pseudofunctor B W hW
  refine ⟨P, fpqc_stack_criterion_over B P.functor ?_ ?_⟩
  · exact categorical_open_root_descent B W hW P
  · exact categorical_fpqc_root_descent B W hW P

end ArithmeticThetaRootStackR0198

#print axioms ArithmeticThetaRootStackR0198.fpqc_root_stack
