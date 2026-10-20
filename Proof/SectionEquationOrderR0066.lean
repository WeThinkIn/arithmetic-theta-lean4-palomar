module

public import SectionLocalDVRR0066

@[expose] public section

/-! The actual linear section equation is a uniformizer at its own prime. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalOrdersR0066

/-- The horizontal section equation has order exactly one in its DVR local ring. -/
theorem section_equation_order :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (α : k) (hα : α ≠ 0)
      (P : Ideal (GenericChart k)) [P.IsPrime],
      P = sectionIdeal k side α → ExactOrder k P (sectionEquation k side α) 1 := by
  intro k _ _ side α hα P _ hP
  let A := Localization.AtPrime P
  let f : A := algebraMap (GenericChart k) A (sectionEquation k side α)
  let : IsDiscreteValuationRing A := section_local_dvr k side α hα P hP
  have hspan : P.map (algebraMap (GenericChart k) A) = Ideal.span {f} := by
    calc
      _ = (sectionIdeal k side α).map (algebraMap (GenericChart k) A) :=
        congrArg (Ideal.map (algebraMap (GenericChart k) A)) hP
      _ = _ := by rw [sectionIdeal, Ideal.map_span, Set.image_singleton]
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A]
    exact hspan
  have hirr : Irreducible f :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer f).mpr hmax
  change f ∈ (P.map (algebraMap (GenericChart k) A)) ^ 1 ∧
    f ∉ (P.map (algebraMap (GenericChart k) A)) ^ (1 + 1)
  rw [hspan, pow_one]
  refine ⟨Ideal.subset_span (Set.mem_singleton f), ?_⟩
  intro h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hbad : (2 : ℕ) ≤ 1 :=
    (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).mp (by simpa using h)
  omega

end ArithmeticThetaLocalOrdersR0066
