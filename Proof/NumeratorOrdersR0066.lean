module

public import SectionEquationOrderR0066

@[expose] public section

/-! Orders of the literal numerator, retaining the endpoint gamma factors. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066
variable (k : Type u) [Field k] [CharZero k]

lemma exactOrder_unit (P : Ideal (GenericChart k)) [P.IsPrime]
    (a : GenericChart k)
    (ha : IsUnit (algebraMap (GenericChart k) (Localization.AtPrime P) a)) :
    ExactOrder k P a 0 := by
  constructor
  · simp
  · intro h
    have hm : algebraMap (GenericChart k) (Localization.AtPrime P) a ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      simpa only [Nat.zero_add, pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal] using h
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha

lemma exactOrder_unit_mul (P : Ideal (GenericChart k)) [P.IsPrime]
    (a b : GenericChart k) (n : ℕ) (ha : IsUnit a) :
    ExactOrder k P (a * b) n ↔ ExactOrder k P b n := by
  unfold ExactOrder
  rw [map_mul]
  simp only [Ideal.unit_mul_mem_iff_mem _ (ha.map _)]

lemma section_power_order (side : Bool) (α : k) (hα : α ≠ 0)
    (P : Ideal (GenericChart k)) [P.IsPrime] (hP : P.height = 1) (n : ℕ) :
    ExactOrder k P (sectionEquation k side α ^ n)
      (if P = sectionIdeal k side α then n else 0) := by
  classical
  by_cases heq : P = sectionIdeal k side α
  · rw [if_pos heq]
    let A := Localization.AtPrime P
    let f : A := algebraMap (GenericChart k) A (sectionEquation k side α)
    have hspan : P.map (algebraMap (GenericChart k) A) = Ideal.span {f} := by
      calc
        _ = (sectionIdeal k side α).map (algebraMap (GenericChart k) A) :=
          congrArg (Ideal.map (algebraMap (GenericChart k) A)) heq
        _ = _ := by rw [sectionIdeal, Ideal.map_span, Set.image_singleton]
    have ho := section_equation_order k side α hα P heq
    change f ∈ (P.map (algebraMap (GenericChart k) A)) ^ 1 ∧
      f ∉ (P.map (algebraMap (GenericChart k) A)) ^ 2 at ho
    have hf0 : f ≠ 0 := fun h => ho.2 (h ▸ Ideal.zero_mem _)
    have hfunit : ¬ IsUnit f := by
      intro hu
      have hm : f ∈ IsLocalRing.maximalIdeal A := by
        simpa only [pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal] using ho.1
      exact ((IsLocalRing.mem_maximalIdeal _).mp hm) hu
    unfold ExactOrder
    rw [map_pow, hspan, Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    constructor
    · exact Ideal.mem_span_singleton.mpr (dvd_refl _)
    · intro h
      have hn := (pow_dvd_pow_iff hf0 hfunit).mp (Ideal.mem_span_singleton.mp h)
      omega
  · rw [if_neg heq]
    apply exactOrder_unit
    rw [map_pow]
    apply IsUnit.pow
    apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mpr
    change sectionEquation k side α ∉ P
    intro hmem
    let : (sectionIdeal k side α).IsPrime := section_prime k side α hα
    have hs := section_height_one k side α hα (sectionIdeal k side α) rfl
    have hle : sectionIdeal k side α ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
    have he : sectionIdeal k side α = P :=
      Ideal.eq_of_le_of_height_le (sectionIdeal k side α) hle (by rw [hs, hP])
    exact heq he.symm

lemma gamma_unit (c j : ℕ) (hc : 1 < c) (hj : j < 2*c) :
    IsUnit (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaLocalNormR0054.gammaUnit k (2*c) j (by omega) hj)) := by
  exact ((Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 (2*c) j
      (by omega) hj)).1.1).map _

lemma horizontal_endpoint (side : Bool) :
    ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (1 - ArithmeticThetaAnnularTorsionPrereqR0053.coord k side) =
        -sectionEquation k side 1 := by
  simp [sectionEquation, ArithmeticThetaAnnularTorsionPrereqR0053.sectionEquation]

/-- Every height-one order of the full source numerator. -/
theorem numerator_orders :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c) (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 →
        ExactOrder k P
          (ArithmeticThetaGenericOverlapR0065.numerator k c j ζ hc hcop hζ hj)
          (numeratorOrder k c j P) := by
  intro k _ _ c j ζ hc hcop hζ hj P _ hP
  classical
  unfold ArithmeticThetaGenericOverlapR0065.numerator
    ArithmeticThetaLocalNormR0054.localNumerator
  apply (exactOrder_unit_mul k P _ _ _ (Units.isUnit _)).mpr
  unfold ArithmeticThetaLocalNormR0054.gammaLocal
  rw [map_mul, mul_pow, mul_comm]
  apply (exactOrder_unit_mul k P _ _ _ ((gamma_unit k c j hc hj).pow _)).mpr
  by_cases hfirst : j = 0
  · have hlast0 : 1 ≠ 2*c := by omega
    have hh : ArithmeticThetaLocalNormR0054.gammaHorizontal k (2*c) j =
        1 - ArithmeticThetaAnnularTorsionPrereqR0053.coord k true := by
      simp [ArithmeticThetaLocalNormR0054.gammaHorizontal,
        ArithmeticThetaScaledAnnularR0050.gammaHorizontal, hfirst, hlast0,
        ArithmeticThetaAnnularTorsionPrereqR0053.coord,
        ArithmeticThetaAnnularTorsionPrereqR0053.cx]
    rw [hh, horizontal_endpoint, neg_eq_neg_one_mul, mul_pow]
    apply (exactOrder_unit_mul k P _ _ _ ((isUnit_one.neg).pow _)).mpr
    simpa [numeratorOrder, IsIdentityPrime, hfirst, hlast0] using
      section_power_order k true 1 one_ne_zero P hP (c^2)
  · by_cases hlast : j + 1 = 2*c
    · have hh : ArithmeticThetaLocalNormR0054.gammaHorizontal k (2*c) j =
          1 - ArithmeticThetaAnnularTorsionPrereqR0053.coord k false := by
        simp [ArithmeticThetaLocalNormR0054.gammaHorizontal,
          ArithmeticThetaScaledAnnularR0050.gammaHorizontal, hfirst, hlast,
          ArithmeticThetaAnnularTorsionPrereqR0053.coord,
          ArithmeticThetaAnnularTorsionPrereqR0053.cy]
      rw [hh, horizontal_endpoint, neg_eq_neg_one_mul, mul_pow]
      apply (exactOrder_unit_mul k P _ _ _ ((isUnit_one.neg).pow _)).mpr
      simpa [numeratorOrder, IsIdentityPrime, hfirst, hlast] using
        section_power_order k false 1 one_ne_zero P hP (c^2)
    · have hh : ArithmeticThetaLocalNormR0054.gammaHorizontal k (2*c) j = 1 := by
        simp [ArithmeticThetaLocalNormR0054.gammaHorizontal,
          ArithmeticThetaScaledAnnularR0050.gammaHorizontal, hfirst, hlast]
      simp only [hh, map_one, one_pow]
      have hn : numeratorOrder k c j P = 0 := by
        simp [numeratorOrder, IsIdentityPrime, hfirst, hlast]
      rw [hn]
      apply exactOrder_unit
      simp

end ArithmeticThetaLocalOrdersR0066
