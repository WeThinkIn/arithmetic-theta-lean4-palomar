import OrderRegularityR0067
import QuotientOrderR0067
import NormalDomainIntersection

/-! A conditional unit comparison for the actual completed generic chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067
open ArithmeticThetaLocalOrdersR0066

private lemma hasOrder_ne_zero (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    (f : FunctionField k) (m : ℤ) (hf : HasOrder k P f m) : f ≠ 0 := by
  intro hzero
  obtain ⟨a, b, na, nb, hb, hab, ha, hbo, hm⟩ := hf
  have hta : toFunctionField k a = 0 := by
    rw [← hab, hzero, zero_mul]
  have ha0 : a = 0 := by
    apply IsFractionRing.injective (GenericChart k) (FunctionField k)
    simpa [toFunctionField] using hta
  exact (exactOrder_ne_zero k P a na ha) ha0

theorem equal_divisor_unit :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c) (g : FunctionField k),
      (∀ (P : Ideal (GenericChart k)) [P.IsPrime], P.height = 1 →
        HasOrder k P g (divisorCoefficient k c j ζ P)) →
      ∃! v : (GenericChart k)ˣ,
        toFunctionField k (v : GenericChart k) =
          ratio k g (localFunction k c j ζ hc hcop hζ hj) := by
  intro k _ _ c j ζ hc hcop hζ hj g hg
  let f : FunctionField k := localFunction k c j ζ hc hcop hζ hj
  have hf : ∀ (P : Ideal (GenericChart k)) [P.IsPrime], P.height = 1 →
      HasOrder k P f (divisorCoefficient k c j ζ P) := by
    intro P hPinst hP
    simpa [f] using
      (local_f_divisor k c j ζ hc hcop hζ hj P hP).1
  let hratio : FunctionField k := ratio k g f
  have hratio_ne_zero : hratio ≠ 0 := by
    let P₀ : Ideal (GenericChart k) := sectionIdeal k true 1
    letI : P₀.IsPrime := section_prime k true 1 one_ne_zero
    have hP₀ : P₀.height = 1 := section_height_one k true 1 one_ne_zero P₀ rfl
    have hg0 : g ≠ 0 := by
      exact hasOrder_ne_zero k P₀ g _ (hg P₀ hP₀)
    have hf0 : f ≠ 0 := hasOrder_ne_zero k P₀ f _ (hf P₀ hP₀)
    change g / f ≠ 0
    exact div_ne_zero hg0 hf0
  have hregular : ∀ (P : Ideal (GenericChart k)) [P.IsPrime], P.height = 1 →
      RegularAt k P hratio := by
    intro P hPinst hP
    have hq := quotient_order k P g f
      (divisorCoefficient k c j ζ P) (divisorCoefficient k c j ζ P)
      hP (hg P hP) (hf P hP)
    have hq0 : HasOrder k P hratio 0 := by
      simpa [hratio] using hq
    have hz : (0 : ℤ) ≤ 0 := le_rfl
    exact (order_regularity k P hratio 0 hP hq0).mpr hz
  have hinvregular : ∀ (P : Ideal (GenericChart k)) [P.IsPrime], P.height = 1 →
      RegularAt k P hratio⁻¹ := by
    intro P hPinst hP
    have hq := quotient_order k P f g
      (divisorCoefficient k c j ζ P) (divisorCoefficient k c j ζ P)
      hP (hf P hP) (hg P hP)
    have hq0 : HasOrder k P (ratio k f g) 0 := by
      convert hq using 1 <;> omega
    have hz : (0 : ℤ) ≤ 0 := le_rfl
    have hs : ratio k f g = hratio⁻¹ := by
      simp [hratio, ratio, inv_div]
    rw [← hs]
    exact (order_regularity k P (ratio k f g) 0 hP hq0).mpr hz
  obtain ⟨a, ha⟩ :=
    ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
      (GenericChart k) (FunctionField k) hratio hregular
  obtain ⟨b, hb⟩ :=
    ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
      (GenericChart k) (FunctionField k) hratio⁻¹ hinvregular
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (GenericChart k) (FunctionField k)
    rw [map_mul, ha, hb, mul_inv_cancel₀ hratio_ne_zero, map_one]
  have hba : b * a = 1 := by
    apply IsFractionRing.injective (GenericChart k) (FunctionField k)
    rw [map_mul, hb, ha, inv_mul_cancel₀ hratio_ne_zero, map_one]
  let v : (GenericChart k)ˣ :=
    { val := a
      inv := b
      val_inv := hab
      inv_val := hba }
  refine ⟨v, ?_, ?_⟩
  · change (algebraMap (GenericChart k) (FunctionField k)) a =
      ratio k g (localFunction k c j ζ hc hcop hζ hj)
    simpa [f] using ha
  · intro w hw
    apply Units.ext
    apply IsFractionRing.injective (GenericChart k) (FunctionField k)
    calc
      toFunctionField k (↑w : GenericChart k) = ratio k g f := by simpa [f] using hw
      _ = toFunctionField k a := by
        change ratio k g f = (algebraMap (GenericChart k) (FunctionField k)) a
        exact ha.symm


end ArithmeticThetaRatioRegularityR0067
