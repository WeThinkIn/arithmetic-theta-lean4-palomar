module

public import LocalIdealOrderR0116
public import TranslationCompositionR0116
public import MillerInfinityNormalizationR0114
public import HalfMillerPrincipalIdealR0114

@[expose] public section

/-! The complete divisor and infinity normalization of the actual Miller function. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord pointIdeal pointFraction xFunction yFunction)

section
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
variable (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)

include he in
/-- Recover a coordinate-ring generator from the accepted fractional-ideal identity. -/
lemma miller_coordinate_generator (i : Fin 3) (x y : k)
    (hhalf : ArithmeticThetaMillerR0114.IsHalf k e i x y) :
    ∃ a : Coord k e, a ≠ 0 ∧
      algebraMap (Coord k e) (FF k e) a = ArithmeticThetaMillerR0114.millerFunction k e i x y ∧
      Ideal.span {a} = pointIdeal k e x y ^ 4 := by
  obtain ⟨hf, hI⟩ := ArithmeticThetaMillerR0114.half_miller_principal_ideal k e he i x y hhalf
  have hmem := FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (Coord k e))
    (ArithmeticThetaMillerR0114.millerFunction k e i x y)
  rw [hI, pointFraction, ← FractionalIdeal.coeIdeal_pow] at hmem
  obtain ⟨a, _, ha⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
  refine ⟨a, fun hz => hf (by rw [← ha, hz, map_zero]), ha, ?_⟩
  apply (FractionalIdeal.coeIdeal_injective (K := FF k e))
  change (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) =
    (pointIdeal k e x y ^ 4 : Ideal (Coord k e))
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_pow, ha]
  exact hI

include he hT hh hE in
/-- At every nonsingular affine point there is a coordinate function of order one. -/
lemma affine_parameter (x y : k) (hp : (Curve k e).Nonsingular x y) :
    ∃ t : Coord k e, t ≠ 0 ∧ t ∈ pointIdeal k e x y ∧
      pointOrder k e T E (algebraMap (Coord k e) (FF k e) t) (.some x y hp) = 1 := by
  have H := local_affine_expansion k e he T hT h E hh hE x y hp
  by_cases hy : y = 0
  · refine ⟨CoordinateRing.YClass (Curve k e) 0, CoordinateRing.YClass_ne_zero _, ?_, ?_⟩
    · apply Ideal.subset_span
      simp [hy]
    · exact H.2.2 hy
  · refine ⟨CoordinateRing.XClass (Curve k e) x, CoordinateRing.XClass_ne_zero _, ?_, ?_⟩
    · apply Ideal.subset_span
      simp
    · rw [field_XClass]
      exact H.2.1.trans (if_neg hy)

include he hT hh hE in
/-- A generator of the fourth power of a point ideal has order exactly four there. -/
lemma generator_order_self (x y : k) (hp : (Curve k e).Nonsingular x y)
    (a : Coord k e) (ha : a ≠ 0) (hspan : Ideal.span {a} = pointIdeal k e x y ^ 4) :
    pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) = 4 := by
  have H := local_ideal_order k e he T hT h E hh hE x y hp
  have hlow : (4 : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) :=
    (H a ha 4).mpr (hspan ▸ Ideal.mem_span_singleton_self a)
  have hhigh : ¬ (5 : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) := by
    intro hbad
    have hle : pointIdeal k e x y ^ 4 ≤ pointIdeal k e x y ^ 5 := by
      rw [← hspan]
      exact (Ideal.span_singleton_le_iff_mem _).mpr ((H a ha 5).mp hbad)
    obtain ⟨t, ht, htm, htord⟩ := affine_parameter k e he T hT h E hh hE x y hp
    have h5 := (H (t^4) (pow_ne_zero _ ht) 5).mpr (hle (Ideal.pow_mem_pow htm 4))
    have hpow : pointOrder k e T E (algebraMap (Coord k e) (FF k e) (t^4)) (.some x y hp) = 4 := by
      simp only [pointOrder, expansion, map_pow, HahnSeries.order_pow]
      change (4 : ℕ) • pointOrder k e T E (algebraMap (Coord k e) (FF k e) t) (.some x y hp) = 4
      rw [htord]
      norm_num
    rw [hpow] at h5
    norm_num at h5
  omega

omit [CharZero k] [DecidableEq k] in
include hT hh hE in
/-- The kernel description separates the actual ideals of distinct affine points. -/
lemma pointIdeal_coordinates_of_le (x y a b : k) (hp : (Curve k e).Nonsingular a b)
    (hle : pointIdeal k e x y ≤ pointIdeal k e a b) : x = a ∧ y = b := by
  let φ := localSeriesHom k e T hT h E hh hE a b hp
  have hx : CoordinateRing.XClass (Curve k e) x ∈ pointIdeal k e a b :=
    hle (Ideal.subset_span (by simp))
  have hy : CoordinateRing.YClass (Curve k e) (C y) ∈ pointIdeal k e a b :=
    hle (Ideal.subset_span (by simp))
  rw [localSeriesHom_kernel k e T hT h E hh hE a b hp, RingHom.mem_ker] at hx hy
  change PowerSeries.constantCoeff (φ (CoordinateRing.mk (Curve k e) (C (X-C x)))) = 0 at hx
  change PowerSeries.constantCoeff (φ (CoordinateRing.mk (Curve k e) (X-C (C y)))) = 0 at hy
  rw [localSeriesHom_constant] at hx hy
  simp at hx hy
  exact ⟨(sub_eq_zero.mp hx).symm, (sub_eq_zero.mp hy).symm⟩

include he hT hh hE in
/-- At every other affine point the same generator is a local unit. -/
lemma generator_order_other (x y a b : k) (hp : (Curve k e).Nonsingular a b)
    (hne : ¬ (x = a ∧ y = b)) (f : Coord k e) (hf : f ≠ 0)
    (hspan : Ideal.span {f} = pointIdeal k e x y ^ 4) :
    pointOrder k e T E (algebraMap (Coord k e) (FF k e) f) (.some a b hp) = 0 := by
  have H := local_ideal_order k e he T hT h E hh hE a b hp f hf
  have hlow : (0 : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) f) (.some a b hp) :=
    (H 0).mpr (by simp)
  have hhigh : ¬ (1 : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) f) (.some a b hp) := by
    intro hbad
    have hfm : f ∈ pointIdeal k e a b := by simpa using (H 1).mp hbad
    have hle : pointIdeal k e x y ^ 4 ≤ pointIdeal k e a b := by
      rw [← hspan]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hfm
    have hm := (pointIdeal_maximal k e a b hp).isPrime
    apply hne
    apply pointIdeal_coordinates_of_le k e T hT h E hh hE x y a b hp
    intro t ht
    exact hm.mem_of_pow_mem 4 (hle (Ideal.pow_mem_pow ht 4))
  omega

include he hT hh hE in
/-- The accepted normalized infinity series has order minus four and leading coefficient one. -/
lemma miller_infinity_order_leading (i : Fin 3) (x y : k)
    (hhalf : ArithmeticThetaMillerR0114.IsHalf k e i x y) :
    pointOrder k e T E (ArithmeticThetaMillerR0114.millerFunction k e i x y) 0 = -4 ∧
    localLeading k e T E (ArithmeticThetaMillerR0114.millerFunction k e i x y) 0 = 1 := by
  obtain ⟨s, hs, hnorm⟩ := ArithmeticThetaMillerR0114.miller_infinity_normalization
    k e he h E hh hE i x y hhalf
  have hz := (translation_composition k e he T hT).1
  have hsn : algebraMap (PowerSeries k) (LaurentSeries k) s ≠ 0 := by
    intro hn
    have hs0 : s = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using hn)
    simp [hs0] at hs
  have hord := series_order_zero k s (by rw [hs]; exact one_ne_zero)
  have hlead : (algebraMap (PowerSeries k) (LaurentSeries k) s).leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hord]
    change (HahnSeries.ofPowerSeries ℤ k s).coeff (0 : ℕ) = 1
    simpa only [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff] using hs
  have ht : ArithmeticThetaMillerR0114.parameter k ^ (-4 : ℤ) =
      HahnSeries.single (-4 : ℤ) (1 : k) := by
    change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X) ^ (-4 : ℤ) = _
    rw [HahnSeries.ofPowerSeries_X, ← RatFunc.single_zpow]
  simp only [pointOrder, localLeading, expansion, hz, AlgEquiv.coe_refl, id_eq, hnorm, ht]
  constructor
  · rw [HahnSeries.order_mul (by simp) hsn, HahnSeries.order_single one_ne_zero, hord]
    norm_num
  · rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single, hlead, one_mul]

end

/-- The actual normalized Miller function has complete divisor `4[P] - 4[0]`. -/
theorem complete_miller_divisor :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ T : Translations k e, IsTranslationSystem k e T →
    ∀ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
    ArithmeticThetaMillerR0114.branchEquation k e h →
    ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E →
    ∀ (i : Fin 3) (P : (Curve k e).Point), ArithmeticThetaMillerR0114.IsHalfPoint k e i P →
    millerAt k e i P ≠ 0 ∧
    (∀ A : (Curve k e).Point, pointOrder k e T E (millerAt k e i P) A =
      (if A = P then 4 else 0) - (if A = 0 then 4 else 0)) ∧
    localLeading k e T E (millerAt k e i P) 0 = 1 := by
  intro k _ _ _ e he T hT h E hh hE i P hP
  cases P with
  | zero =>
    obtain ⟨_, hbad⟩ := hP
    change (2 : ℤ) • (0 : (Curve k e).Point) = _ at hbad
    rw [smul_zero] at hbad
    exact False.elim (Point.some_ne_zero _ hbad.symm)
  | @some x y hp =>
    have hhalf : ArithmeticThetaMillerR0114.IsHalf k e i x y := by
      obtain ⟨hi, hhi⟩ := hP
      exact ⟨hp, hi, hhi⟩
    obtain ⟨f, hf, hfeq, hspan⟩ := miller_coordinate_generator k e he i x y hhalf
    have hinf := miller_infinity_order_leading k e he T hT h E hh hE i x y hhalf
    refine ⟨?_, ?_, hinf.2⟩
    · exact (ArithmeticThetaMillerR0114.half_miller_principal_ideal k e he i x y hhalf).1
    · intro A
      cases A with
      | zero =>
        change pointOrder k e T E (ArithmeticThetaMillerR0114.millerFunction k e i x y) 0 =
          (if (0 : (Curve k e).Point) = Point.some x y hp then 4 else 0) - (if (0 : (Curve k e).Point) = 0 then 4 else 0)
        simpa only [Ne.symm (Point.some_ne_zero hp), ↓reduceIte, zero_sub] using hinf.1
      | @some a b hab =>
        change pointOrder k e T E (ArithmeticThetaMillerR0114.millerFunction k e i x y) (.some a b hab) = _
        rw [← hfeq]
        by_cases hxy : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := hxy
          simpa using generator_order_self k e he T hT h E hh hE x y hp f hf hspan
        · have hpoints : Point.some a b hab ≠ Point.some x y hp := by
            intro H
            obtain ⟨ha, hb⟩ := Point.some.inj H
            exact hxy ⟨ha.symm, hb.symm⟩
          simpa [hpoints] using generator_order_other k e he T hT h E hh hE x y a b hab hxy f hf hspan

end ArithmeticThetaReciprocityR0116
