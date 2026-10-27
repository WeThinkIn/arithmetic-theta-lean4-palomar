import SectionEquationOrderR0066

/-! Orders of the literal denominator on the completed generic chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066

private theorem radical_order_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R) (hf : f ≠ 0)
    (hr : (Ideal.span {f} : Ideal R).IsRadical)
    (hm : f ∈ IsLocalRing.maximalIdeal R)
    (q : R) (hq : Irreducible q)
    (hq2 : q ∉ (IsLocalRing.maximalIdeal R) ^ 2) :
    f ∉ (IsLocalRing.maximalIdeal R) ^ 2 := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hf hq
  have hqn : q ^ n ∈ (Ideal.span {f} : Ideal R) :=
    (Ideal.mem_iff_of_associated hn).mp (Ideal.mem_span_singleton_self f)
  have hqf : q ∈ (Ideal.span {f} : Ideal R) := hr ⟨n, hqn⟩
  have hnle : n ≤ 1 := by
    apply (pow_dvd_pow_iff hq.ne_zero hq.not_isUnit).mp
    simpa only [pow_one] using hn.symm.dvd.trans (Ideal.mem_span_singleton.mp hqf)
  have hn0 : n ≠ 0 := by
    intro h
    have hmem := (Ideal.mem_iff_of_associated hn).mp hm
    simp only [h, pow_zero] at hmem
    exact (Ideal.one_notMem (IsLocalRing.maximalIdeal R)) hmem
  have hn1 : n = 1 := by omega
  intro h
  apply hq2
  simpa only [hn1, pow_one] using (Ideal.mem_iff_of_associated hn).mp h

private theorem section_mem_iff (k : Type u) [Field k] [CharZero k]
    (side : Bool) (α : k) (hα : α ≠ 0)
    (P : Ideal (GenericChart k)) [P.IsPrime] (hP : P.height = 1) :
    sectionEquation k side α ∈ P ↔ P = sectionIdeal k side α := by
  constructor
  · intro h
    let := section_prime k side α hα
    have hh := section_height_one k side α hα (sectionIdeal k side α) rfl
    have hle : sectionIdeal k side α ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
    by_contra he
    have hlt := lt_of_le_of_ne hle (Ne.symm he)
    have hn := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hh, hP] at hn
    norm_num at hn
  · rintro rfl
    exact Ideal.mem_span_singleton_self _

private theorem horizontal_mem_iff (k : Type u) [Field k] [CharZero k]
    (side : Bool) (c : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (P : Ideal (GenericChart k)) [P.IsPrime]
    (hP : P.height = 1) :
    ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.horizontalEquation k side c) ∈ P ↔
      ∃ b : Fin c, P = sectionIdeal k side (ζ ^ b.val) := by
  have hfac := congrArg (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)
    (ArithmeticThetaAnnularTorsionPrereqR0053.horizontal_split_reduced
      k side c ζ hc hcop hζ).1
  have heq : ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.horizontalEquation k side c) =
      -(∏ b : Fin c, sectionEquation k side (ζ ^ b.val)) := by
    rw [map_prod] at hfac
    rw [← neg_sub] at hfac
    simpa only [ArithmeticThetaAnnularTorsionPrereqR0053.horizontalEquation,
      map_neg, neg_neg, sectionEquation] using (congrArg Neg.neg hfac).symm
  rw [heq, Ideal.neg_mem_iff, Ideal.IsPrime.prod_mem_iff]
  simp only [Finset.mem_univ, true_and]
  exact exists_congr (fun b => section_mem_iff k side (ζ ^ b.val)
    (pow_ne_zero _ (hζ.ne_zero (by omega))) P hP)

private theorem denominator_mem_iff (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c)
    (P : Ideal (GenericChart k)) [P.IsPrime] (hP : P.height = 1) :
    ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj ∈ P ↔
      IsTorsionPrime k c j ζ P := by
  have ha := (ArithmeticThetaLocalNormR0054.local_norm_factorization
    k c j ζ hc hcop hζ hj).2
  change ArithmeticThetaLocalNormR0054.localDenominator k c j ζ hc hcop hζ hj ∈ P ↔ _
  rw [Ideal.mem_iff_of_associated ha]
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.horizontal, map_mul,
    Ideal.IsPrime.mul_mem_iff_mem_or_mem]
  have hx := horizontal_mem_iff k true c ζ hc hcop hζ P hP
  have hy := horizontal_mem_iff k false c ζ hc hcop hζ P hP
  by_cases hX : 2*c ∣ c*j <;> by_cases hY : 2*c ∣ c*(j+1) <;>
    simp only [hX, hY, if_true, if_false, map_one,
      Ideal.one_notMem, or_false, false_or, hx, hy]
  all_goals
    simp only [IsTorsionPrime, Bool.exists_bool, Bool.false_eq_true, if_false,
      if_true, hX, hY, false_and, true_and, exists_false, or_false, false_or]
  · exact or_comm

/-- The frozen denominator-order statement, using the literal accepted denominator. -/
theorem denominator_orders :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c) (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 → ExactOrder k P
        (ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj)
        (denominatorOrder k c j ζ P) := by
  intro k _ _ c j ζ hc hcop hζ hj P _ hP
  classical
  let A := Localization.AtPrime P
  let D := ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj
  let f : A := algebraMap (GenericChart k) A D
  let : IsDiscreteValuationRing A := height_one_dvr k P hP
  have hmem : f ∈ IsLocalRing.maximalIdeal A ↔ IsTorsionPrime k c j ζ P :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A P D).trans
      (denominator_mem_iff k c j ζ hc hcop hζ hj P hP)
  change f ∈ (P.map (algebraMap (GenericChart k) A)) ^ denominatorOrder k c j ζ P ∧
    f ∉ (P.map (algebraMap (GenericChart k) A)) ^ (denominatorOrder k c j ζ P + 1)
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal P A]
  by_cases ht : IsTorsionPrime k c j ζ P
  · simp only [denominatorOrder, if_pos ht, pow_one]
    refine ⟨hmem.mpr ht, ?_⟩
    have hp := (Classical.choose_spec
      (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_local_divisor
        k (2*c) c j ζ (by omega) hc (by simp) hcop hζ hj)).1
    let γ := ArithmeticThetaLocalNormR0054.poweredLocal k (2*c) c j ζ
      (by omega) hc (by simp) hcop hζ hj
    have hradγ : (Ideal.span {γ} : Ideal (GenericChart k)).IsRadical := hp.2.2.1
    have hnzdγ : γ ∈ nonZeroDivisors (GenericChart k) := hp.2.2.2
    have hu : IsUnit ((-ArithmeticThetaLocalNormR0054.localZ k j) ^ (c*(c-1)/2)) :=
      (ArithmeticThetaLocalNormR0054.local_coordinate_unit k j).1.neg.pow _
    have heq : D = (-ArithmeticThetaLocalNormR0054.localZ k j) ^ (c*(c-1)/2) * γ := rfl
    have hspan : (Ideal.span {D} : Ideal (GenericChart k)) = Ideal.span {γ} := by
      rw [heq]
      exact Ideal.span_singleton_mul_left_unit hu γ
    have hrD : (Ideal.span {D} : Ideal (GenericChart k)).IsRadical := hspan ▸ hradγ
    have hnzdD : D ∈ nonZeroDivisors (GenericChart k) := by
      rw [heq]
      exact mul_mem_nonZeroDivisors.mpr ⟨hu.mem_nonZeroDivisors, hnzdγ⟩
    have hf : f ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
      (IsLocalization.nonZeroDivisors_le_comap P.primeCompl A hnzdD)
    have hmap : (Ideal.span {D} : Ideal (GenericChart k)).map
        (algebraMap (GenericChart k) A) = Ideal.span {f} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hr : (Ideal.span {f} : Ideal A).IsRadical := by
      apply Ideal.radical_eq_iff.mp
      rw [← hmap, ← IsLocalization.map_radical (M := P.primeCompl), hrD.radical]
    obtain ⟨side, b, hdiv, hsection⟩ := ht
    have hz : ζ ^ b.val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    let q : A := algebraMap (GenericChart k) A (sectionEquation k side (ζ ^ b.val))
    have hqspan : IsLocalRing.maximalIdeal A = Ideal.span {q} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A]
      calc
        _ = (sectionIdeal k side (ζ ^ b.val)).map
            (algebraMap (GenericChart k) A) :=
          congrArg (Ideal.map (algebraMap (GenericChart k) A)) hsection
        _ = _ := by rw [sectionIdeal, Ideal.map_span, Set.image_singleton]
    have hq : Irreducible q :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer q).mpr hqspan
    have hq2 : q ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
      have hs := (section_equation_order k side (ζ ^ b.val) hz P hsection).2
      change q ∉ (P.map (algebraMap (GenericChart k) A)) ^ 2 at hs
      rwa [IsLocalization.AtPrime.map_eq_maximalIdeal P A] at hs
    exact radical_order_one f hf hr (hmem.mpr ⟨side, b, hdiv, hsection⟩) q hq hq2
  · simp only [denominatorOrder, if_neg ht, pow_zero, zero_add, pow_one]
    exact ⟨by simp, fun h => ht (hmem.mp h)⟩

end ArithmeticThetaLocalOrdersR0066
