module

public import SmoothDVR

@[expose] public section

/-!
# Smoothness of finite-type Dedekind domains in characteristic zero

The proof checks formal smoothness at every prime. Nonzero primes give DVRs;
the zero prime gives the fraction field. Finite presentation then permits the
smooth-locus criterion, including when the original domain is a field.
-/

set_option autoImplicit false
universe u v

namespace ArithmeticThetaNormalizedCurve

/-- Every finite-type Dedekind domain over a characteristic-zero field is smooth. -/
theorem dedekind_smooth :
    ∀ (k : Type u) [Field k] [CharZero k] (A : Type v) [CommRing A]
      [IsDomain A] [Algebra k A] [IsDedekindDomain A]
      [Algebra.FiniteType k A], Algebra.Smooth k A := by
  intro k _ _ A _ _ _ _ _
  have : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, inferInstance⟩
  apply Algebra.smoothLocus_eq_univ_iff.mp
  apply Set.eq_univ_of_forall
  intro p
  change Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal)
  have : Algebra.EssFiniteType A (Localization.AtPrime p.asIdeal) :=
    Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime p.asIdeal) :=
    Algebra.EssFiniteType.comp k A _
  by_cases hp : p.asIdeal = ⊥
  · have : IsFractionRing A (Localization.AtPrime p.asIdeal) := by
      change IsLocalization (nonZeroDivisors A) (Localization.AtPrime p.asIdeal)
      have hc : p.asIdeal.primeCompl = nonZeroDivisors A := by
        simp [hp, Ideal.primeCompl_bot]
      rw [← hc]
      infer_instance
    letI : Field (Localization.AtPrime p.asIdeal) := IsFractionRing.toField A
    infer_instance
  · have : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp _
    exact dvr_formallySmooth k (Localization.AtPrime p.asIdeal)

end ArithmeticThetaNormalizedCurve

#print axioms ArithmeticThetaNormalizedCurve.dedekind_smooth
