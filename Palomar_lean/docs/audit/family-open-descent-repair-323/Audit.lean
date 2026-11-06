module
public import ActualFamilyOpenDescentR0207
@[expose] public section

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.effective_actual
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.descentArrowIso
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.underlyingArrowIso
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.underlyingArrowIso_hom
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.underlyingArrowIso_compatible
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.categorical_faithful
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.categorical_full
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.categorical_essSurj
#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyOpenDescentProof.categorical_equivalence
#print axioms ArithmeticThetaMetaplecticStackR0207.actual_family_open_descent

example : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (C : ArithmeticThetaMetaplecticStackR0207.Coherence L
        (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ArithmeticThetaRootStackR0198.OpenDescent C.functor :=
  ArithmeticThetaMetaplecticStackR0207.actual_family_open_descent
