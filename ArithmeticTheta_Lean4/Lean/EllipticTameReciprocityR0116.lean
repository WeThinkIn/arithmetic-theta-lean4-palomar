import PrincipalDivisorSupportR0116
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! General signed tame-symbol reciprocity on the actual split cubic,
proved by quadratic reduction and explicit geometric fiber comparison. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116

section Laurent
variable {k : Type u} [Field k]

lemma laurent_one_sub_of_order_pos {a : LaurentSeries k} (ha : 0 < a.order) :
    (1 - a).order = 0 ∧ (1 - a).leadingCoeff = 1 := by
  have ht : (1 : LaurentSeries k).orderTop < a.orderTop := by
    simpa using HahnSeries.zero_lt_orderTop_of_order ha
  have ho := HahnSeries.orderTop_sub ht
  have hn : 1 - a ≠ 0 := by
    intro hz
    simp [hz] at ho
  have hc := HahnSeries.leadingCoeff_sub ht
  constructor
  · apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hn, ho]
    simp
  · simpa using hc

lemma laurent_one_sub_of_order_neg {a : LaurentSeries k} (ha : a.order < 0) :
    (1 - a).order = a.order ∧ (1 - a).leadingCoeff = -a.leadingCoeff := by
  have han : a ≠ 0 := by intro hz; simp [hz] at ha
  have ht : (-a).orderTop < (1 : LaurentSeries k).orderTop := by
    rw [HahnSeries.orderTop_neg, ← HahnSeries.order_eq_orderTop_of_ne_zero han]
    simpa using ha
  have ho := HahnSeries.orderTop_add_eq_right ht
  have hn : 1 + -a ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.orderTop_zero] at ho
    exact (HahnSeries.orderTop_ne_top.mpr (neg_ne_zero.mpr han)) ho.symm
  constructor
  · apply WithTop.coe_injective
    rw [sub_eq_add_neg, HahnSeries.order_eq_orderTop_of_ne_zero hn, ho,
      HahnSeries.orderTop_neg, HahnSeries.order_eq_orderTop_of_ne_zero han]
  · simpa [sub_eq_add_neg, HahnSeries.leadingCoeff_neg] using
      HahnSeries.leadingCoeff_add_eq_right ht

lemma sign_square_zpow (n : ℤ) : (-1 : k) ^ (n*n) = (-1 : k) ^ n := by
  have he : Even (n*n-n) := by simpa [mul_sub] using Int.even_mul_pred_self n
  have hh := he.neg_one_zpow (α := k)
  rw [zpow_sub₀ (neg_ne_zero.mpr one_ne_zero)] at hh
  exact (div_eq_one_iff_eq (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))).mp hh

lemma laurent_tame_steinberg {a : LaurentSeries k} (ha : a ≠ 0) (hb : 1-a ≠ 0) :
    (-1 : k) ^ (a.order * (1-a).order) * a.leadingCoeff ^ (1-a).order /
      (1-a).leadingCoeff ^ a.order = 1 := by
  rcases lt_trichotomy a.order 0 with hn | hn | hn
  · obtain ⟨ho,hc⟩ := laurent_one_sub_of_order_neg hn
    rw [ho, hc, show -a.leadingCoeff = (-1 : k) * a.leadingCoeff by ring,
      mul_zpow, sign_square_zpow]
    exact div_self (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (zpow_ne_zero _ (HahnSeries.leadingCoeff_ne_zero.mpr ha)))
  · by_cases hm : (1-a).order = 0
    · simp [hn,hm]
    · have hnonneg : 0 ≤ (1-a).order := by
        have h := HahnSeries.min_order_le_order_add (x := (1 : LaurentSeries k))
          (y := -a) (by simpa [sub_eq_add_neg] using hb)
        simpa [HahnSeries.order_neg, hn, sub_eq_add_neg] using h
      have hp : 0 < (1-a).order := lt_of_le_of_ne hnonneg (Ne.symm hm)
      have hc := (laurent_one_sub_of_order_pos hp).2
      have hc' : a.leadingCoeff = 1 := by simpa using hc
      simp [hn,hc']
  · obtain ⟨ho,hc⟩ := laurent_one_sub_of_order_pos hn
    simp [ho,hc]

lemma laurent_valuation_eq_order {a : LaurentSeries k} (ha : a ≠ 0) :
    Valued.v a = WithZero.exp (-a.order) := by
  have hc : PowerSeries.constantCoeff a.powerSeriesPart ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff,
      Nat.cast_zero, add_zero]
    exact HahnSeries.coeff_order_eq_zero.not.mpr ha
  have hunit := ArithmeticThetaMillerR0114.branch_valuation k hc
  have heq := congrArg (fun b : LaurentSeries k => Valued.v b)
    a.single_order_mul_powerSeriesPart
  rw [map_mul, LaurentSeries.valuation_single_zpow] at heq
  change WithZero.exp (-a.order) *
    Valued.v (algebraMap (PowerSeries k) (LaurentSeries k) a.powerSeriesPart) = Valued.v a at heq
  rw [hunit, mul_one] at heq
  exact heq.symm

end Laurent

section Local
variable (k : Type u) [Field k] (e : Fin 3 → k)
variable (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
variable (P : (Curve k e).Point)

lemma expansion_ne_zero {f : FF k e} (hf : f ≠ 0) :
    expansion k e T E P f ≠ 0 := by
  simpa [expansion] using E.injective.ne ((T P).injective.ne hf)

lemma localLeading_ne_zero {f : FF k e} (hf : f ≠ 0) :
    localLeading k e T E f P ≠ 0 :=
  HahnSeries.leadingCoeff_ne_zero.mpr (expansion_ne_zero k e T E P hf)

lemma pointOrder_mul {f g : FF k e} (hf : f ≠ 0) (hg : g ≠ 0) :
    pointOrder k e T E (f * g) P =
      pointOrder k e T E f P + pointOrder k e T E g P := by
  unfold pointOrder expansion
  rw [map_mul, map_mul]
  exact HahnSeries.order_mul (expansion_ne_zero k e T E P hf)
    (expansion_ne_zero k e T E P hg)

lemma localLeading_mul (f g : FF k e) :
    localLeading k e T E (f * g) P =
      localLeading k e T E f P * localLeading k e T E g P := by
  simp only [localLeading, expansion, map_mul, HahnSeries.leadingCoeff_mul]

lemma tameSymbol_eq_one_of_orders_eq_zero (f g : FF k e)
    (hf : pointOrder k e T E f P = 0) (hg : pointOrder k e T E g P = 0) :
    tameSymbol k e T E f g P = 1 := by
  simp [tameSymbol, hf, hg]

lemma tameSymbol_ne_zero {f g : FF k e} (hf : f ≠ 0) (hg : g ≠ 0) :
    tameSymbol k e T E f g P ≠ 0 := by
  unfold tameSymbol
  exact div_ne_zero (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (zpow_ne_zero _ (localLeading_ne_zero k e T E P hf)))
    (zpow_ne_zero _ (localLeading_ne_zero k e T E P hg))

lemma tameSymbol_mul_left {f₁ f₂ g : FF k e} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0) :
    tameSymbol k e T E (f₁ * f₂) g P =
      tameSymbol k e T E f₁ g P * tameSymbol k e T E f₂ g P := by
  unfold tameSymbol
  rw [pointOrder_mul k e T E P hf₁ hf₂, localLeading_mul, add_mul,
    zpow_add₀ (neg_ne_zero.mpr one_ne_zero), mul_zpow]
  rw [zpow_add₀ (localLeading_ne_zero k e T E P hg)]
  ring

lemma tameSymbol_swap (f g : FF k e) :
    tameSymbol k e T E g f P = (tameSymbol k e T E f g P)⁻¹ := by
  unfold tameSymbol
  rw [mul_comm (pointOrder k e T E g P), inv_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    ]
  simp only [← inv_zpow, inv_neg, inv_one]
  ring

lemma tameSymbol_mul_right {f g₁ g₂ : FF k e} (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    tameSymbol k e T E f (g₁ * g₂) P =
      tameSymbol k e T E f g₁ P * tameSymbol k e T E f g₂ P := by
  rw [tameSymbol_swap k e T E P (g₁ * g₂) f, tameSymbol_mul_left k e T E P hg₁ hg₂ hf,
    mul_inv, ← tameSymbol_swap k e T E P g₁ f, ← tameSymbol_swap k e T E P g₂ f]

@[simp] lemma tameSymbol_one_left (g : FF k e) : tameSymbol k e T E 1 g P = 1 := by
  simp [tameSymbol, pointOrder, localLeading, expansion]

@[simp] lemma tameSymbol_one_right (f : FF k e) : tameSymbol k e T E f 1 P = 1 := by
  rw [tameSymbol_swap, tameSymbol_one_left, inv_one]

lemma tameSymbol_inv_left {f g : FF k e} (hf : f ≠ 0) (hg : g ≠ 0) :
    tameSymbol k e T E f⁻¹ g P = (tameSymbol k e T E f g P)⁻¹ := by
  apply (mul_left_cancel₀ (tameSymbol_ne_zero k e T E P hf hg))
  rw [← tameSymbol_mul_left k e T E P hf (inv_ne_zero hf) hg, mul_inv_cancel₀ hf,
    tameSymbol_one_left, mul_inv_cancel₀ (tameSymbol_ne_zero k e T E P hf hg)]

lemma tameSymbol_inv_right {f g : FF k e} (hf : f ≠ 0) (hg : g ≠ 0) :
    tameSymbol k e T E f g⁻¹ P = (tameSymbol k e T E f g P)⁻¹ := by
  rw [tameSymbol_swap k e T E P g⁻¹ f, tameSymbol_inv_left k e T E P hg hf,
    ← tameSymbol_swap k e T E P g f]

lemma tameSymbol_steinberg {f : FF k e} (hf : f ≠ 0) (h1f : 1-f ≠ 0) :
    tameSymbol k e T E f (1-f) P = 1 := by
  have hf' := expansion_ne_zero k e T E P hf
  have h1f' := expansion_ne_zero k e T E P h1f
  unfold expansion at hf' h1f'
  simp only [map_sub, map_one] at h1f'
  simpa only [tameSymbol, pointOrder, localLeading, expansion, map_sub, map_one] using
    laurent_tame_steinberg hf' h1f'

lemma tameSymbol_div_left {f₁ f₂ g : FF k e} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0) :
    tameSymbol k e T E (f₁/f₂) g P =
      tameSymbol k e T E f₁ g P / tameSymbol k e T E f₂ g P := by
  rw [div_eq_mul_inv, tameSymbol_mul_left k e T E P hf₁ (inv_ne_zero hf₂) hg,
    tameSymbol_inv_left k e T E P hf₂ hg, div_eq_mul_inv]

lemma tameSymbol_div_right {f g₁ g₂ : FF k e} (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    tameSymbol k e T E f (g₁/g₂) P =
      tameSymbol k e T E f g₁ P / tameSymbol k e T E f g₂ P := by
  rw [div_eq_mul_inv, tameSymbol_mul_right k e T E P hf hg₁ (inv_ne_zero hg₂),
    tameSymbol_inv_right k e T E P hf hg₂, div_eq_mul_inv]

lemma tameSymbol_self {f : FF k e} (hf : f ≠ 0) :
    tameSymbol k e T E f f P = tameSymbol k e T E f (-1) P := by
  have hn := zpow_ne_zero (pointOrder k e T E f P) (localLeading_ne_zero k e T E P hf)
  have ho : pointOrder k e T E (-1) P = 0 := by
    simp [pointOrder, expansion, HahnSeries.order_neg]
  have hc : localLeading k e T E (-1) P = -1 := by
    simp [localLeading, expansion, HahnSeries.leadingCoeff_neg]
  unfold tameSymbol
  rw [ho, hc, mul_div_cancel_right₀ _ hn, sign_square_zpow]
  simp only [mul_zero, zpow_zero, mul_one, one_div, ← inv_zpow, inv_neg, inv_one]

/-- The Steinberg relation moves an arbitrary pair to their difference. -/
lemma tameSymbol_difference {f g : FF k e} (hf : f ≠ 0) (hg : g ≠ 0) (hd : g-f ≠ 0) :
    tameSymbol k e T E f g P * tameSymbol k e T E g (g-f) P =
      tameSymbol k e T E f (g-f) P * tameSymbol k e T E g (-1) P := by
  have heq : 1-f/g = (g-f)/g := by field_simp
  have hs := tameSymbol_steinberg k e T E P (div_ne_zero hf hg)
    (heq ▸ div_ne_zero hd hg)
  rw [heq, tameSymbol_div_left k e T E P hf hg (div_ne_zero hd hg),
    div_eq_one_iff_eq (tameSymbol_ne_zero k e T E P hg (div_ne_zero hd hg)),
    tameSymbol_div_right k e T E P hf hd hg,
    tameSymbol_div_right k e T E P hg hd hg,
    div_eq_div_iff (tameSymbol_ne_zero k e T E P hf hg)
      (tameSymbol_ne_zero k e T E P hg hg), tameSymbol_self k e T E P hg] at hs
  rw [mul_comm]
  exact hs.symm

/-- A nondegenerate affine pencil reduces a symbol to three scalar arguments. -/
lemma tameSymbol_pencil {f g r s : FF k e} (hf : f ≠ 0) (hg : g ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hfg : g = r*f+s) :
    tameSymbol k e T E f g P =
      tameSymbol k e T E (r*f) s P * tameSymbol k e T E g (-1) P *
        tameSymbol k e T E g r P / tameSymbol k e T E g s P := by
  have hd : g-r*f = s := by rw [hfg]; ring
  have H := tameSymbol_difference k e T E P (mul_ne_zero hr hf) hg (hd ▸ hs)
  rw [hd, tameSymbol_mul_left k e T E P hr hf hg] at H
  have hrg := tameSymbol_ne_zero k e T E P hr hg
  have hgs := tameSymbol_ne_zero k e T E P hg hs
  rw [tameSymbol_swap k e T E P r g]
  apply (eq_div_iff hgs).mpr
  apply (mul_left_cancel₀ hrg)
  calc
    _ = tameSymbol k e T E (r*f) s P * tameSymbol k e T E g (-1) P := by
      simpa only [mul_assoc] using H
    _ = _ := by field_simp

end Local

/-- The tame symbols have finite multiplicative support. This is proved from
finite principal-divisor support, independently of a product-one identity. -/
theorem finite_tameSymbol_support
    (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
    (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    Set.Finite {P : (Curve k e).Point | tameSymbol k e T E f g P ≠ 1} := by
  apply ((principal_divisor_support k e he T hT h E hh hE f hf).1.union
    (principal_divisor_support k e he T hT h E hh hE g hg).1).subset
  intro P hP
  by_contra hn
  have hz := not_or.mp hn
  exact hP (tameSymbol_eq_one_of_orders_eq_zero k e T E P f g
    (not_ne_iff.mp hz.1) (not_ne_iff.mp hz.2))

section Uniformizers
open ArithmeticThetaMillerR0114 (xFunction yFunction parameter infinityX infinityY)
variable (k : Type u) [Field k] (e : Fin 3 → k)
variable (T : Translations k e) (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)

/-- Pull the actual parameter at infinity back by the inverse translation. -/
def pointParameter (P : (Curve k e).Point) : FF k e :=
  (T P).symm (-xFunction k e / yFunction k e)

lemma infinity_parameter_expansion
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E) :
    E (-xFunction k e / yFunction k e) = parameter k := by
  have hn : h ≠ 0 := by intro hz; simpa [hz] using hh.1
  have hj : algebraMap (PowerSeries k) (LaurentSeries k) h ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne hn
  have hz := ArithmeticThetaMillerR0114.parameter_ne_zero k
  rw [map_div₀, map_neg, hE.1, hE.2]
  simp only [infinityX, infinityY, neg_div_neg_eq, zpow_neg]
  field_simp

lemma pointParameter_expansion
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) :
    expansion k e T E P (pointParameter k e T P) = parameter k := by
  unfold expansion pointParameter
  rw [AlgEquiv.apply_symm_apply]
  exact infinity_parameter_expansion k e h E hh hE

lemma pointParameter_ne_zero
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) : pointParameter k e T P ≠ 0 := by
  intro hz
  have hp := pointParameter_expansion k e T h E hh hE P
  rw [hz] at hp
  have hp0 : parameter k = 0 := by simpa [expansion] using hp.symm
  exact ArithmeticThetaMillerR0114.parameter_ne_zero k hp0

lemma pointParameter_order
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) : pointOrder k e T E (pointParameter k e T P) P = 1 := by
  unfold pointOrder
  rw [pointParameter_expansion k e T h E hh hE P]
  change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X).order = 1
  rw [HahnSeries.ofPowerSeries_X, HahnSeries.order_single one_ne_zero]

lemma pointParameter_leading
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) : localLeading k e T E (pointParameter k e T P) P = 1 := by
  unfold localLeading
  rw [pointParameter_expansion k e T h E hh hE P]
  change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X).leadingCoeff = 1
  rw [HahnSeries.ofPowerSeries_X, HahnSeries.leadingCoeff_of_single]

/-- Every integer occurs as the order of a nonzero actual rational function at P. -/
lemma pointOrder_surjective_nonzero
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) (n : ℤ) :
    ∃ f : FF k e, f ≠ 0 ∧ pointOrder k e T E f P = n := by
  refine ⟨pointParameter k e T P ^ n,
    zpow_ne_zero n (pointParameter_ne_zero k e T h E hh hE P), ?_⟩
  have hp := pointParameter_expansion k e T h E hh hE P
  unfold expansion at hp
  unfold pointOrder expansion
  rw [map_zpow₀, map_zpow₀, hp]
  change ((HahnSeries.ofPowerSeries ℤ k PowerSeries.X) ^ n).order = n
  rw [HahnSeries.ofPowerSeries_X]
  cases n with
  | ofNat m => simp [HahnSeries.single_pow, HahnSeries.order_single one_ne_zero]
  | negSucc m =>
    simp [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single,
      HahnSeries.order_single one_ne_zero]
    omega

/-- The valuation is pulled back along the actual translated Laurent embedding. -/
def pointValuation (P : (Curve k e).Point) :
    Valuation (FF k e) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (E.comp (T P).toAlgHom).toRingHom Valued.v

lemma pointValuation_eq_order (P : (Curve k e).Point) {f : FF k e} (hf : f ≠ 0) :
    pointValuation k e T E P f = WithZero.exp (-pointOrder k e T E f P) := by
  exact laurent_valuation_eq_order (expansion_ne_zero k e T E P hf)

lemma pointValuation_surjective
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) : Function.Surjective (pointValuation k e T E P) := by
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  · obtain ⟨f,hf,ho⟩ := pointOrder_surjective_nonzero k e T h E hh hE P (-WithZero.log z)
    refine ⟨f, ?_⟩
    rw [pointValuation_eq_order k e T E P hf, ho, neg_neg, WithZero.exp_log hz]

lemma pointValuation_algebraMap (P : (Curve k e).Point) {c : k} (hc : c ≠ 0) :
    pointValuation k e T E P (algebraMap k (FF k e) c) = 1 := by
  change Valued.v (E ((T P) (algebraMap k (FF k e) c))) = 1
  rw [(T P).commutes, E.commutes]
  change Valued.v (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C c)) = 1
  exact ArithmeticThetaMillerR0114.branch_valuation k (by simpa using hc)

/-- The actual local valuation has a nontrivial discrete value group. -/
lemma pointValuation_valueGroup_nontrivial
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (pointValuation k e T E P))) := by
  let v := pointValuation k e T E P
  obtain ⟨f,hf⟩ := pointValuation_surjective k e T h E hh hE P (WithZero.exp (-1 : ℤ))
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (v f) (by change pointValuation k e T E P f ≠ 0; rw [hf]; simp), ?_, ?_⟩
  · apply MonoidWithZeroHom.mem_valueGroup
    exact ⟨f, rfl⟩
  · intro hz
    have hc := congrArg Units.val hz
    change pointValuation k e T E P f = 1 at hc
    rw [hf] at hc
    norm_num at hc

lemma pointValuation_discrete
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) : (pointValuation k e T E P).IsRankOneDiscrete := by
  have := pointValuation_valueGroup_nontrivial k e T h E hh hE P
  infer_instance

lemma pointValuation_localRing_dvr
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) :
    IsDiscreteValuationRing (pointValuation k e T E P).valuationSubring := by
  have := pointValuation_valueGroup_nontrivial k e T h E hh hE P
  infer_instance

lemma pointValuation_localRing_mem_iff (P : (Curve k e).Point) (f : FF k e) :
    f ∈ (pointValuation k e T E P).valuationSubring ↔ 0 ≤ pointOrder k e T E f P := by
  rw [Valuation.mem_valuationSubring_iff]
  by_cases hf : f = 0
  · simp [hf, pointOrder, expansion]
  · rw [pointValuation_eq_order k e T E P hf, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    exact neg_nonpos

lemma pointValuation_localRing_ne_top
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) :
    (pointValuation k e T E P).valuationSubring ≠ ⊤ := by
  obtain ⟨f,_,ho⟩ := pointOrder_surjective_nonzero k e T h E hh hE P (-1)
  intro ht
  have hm : f ∈ (pointValuation k e T E P).valuationSubring :=
    ht ▸ ValuationSubring.mem_top f
  rw [pointValuation_localRing_mem_iff, ho] at hm
  omega

end Uniformizers

section Residues
variable (k : Type u) [Field k] (e : Fin 3 → k)
variable (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
variable (P : (Curve k e).Point)

abbrev pointLocalRing := (pointValuation k e T E P).valuationSubring

/-- Restriction of the actual expansion to its valuation ring. -/
def pointLocalExpansion : pointLocalRing k e T E P →+* LaurentSeries k :=
  (E.comp (T P).toAlgHom).toRingHom.comp (pointLocalRing k e T E P).subtype

lemma pointLocalExpansion_regular (a : pointLocalRing k e T E P) :
    ∃ s : PowerSeries k,
      algebraMap (PowerSeries k) (LaurentSeries k) s = pointLocalExpansion k e T E P a := by
  exact (LaurentSeries.val_le_one_iff_eq_coe _ _).mp a.property

/-- The complete regular expansion of an element of the actual valuation ring. -/
def pointSeriesHom : pointLocalRing k e T E P →+* PowerSeries k :=
  regularLift (pointLocalExpansion k e T E P) (pointLocalExpansion_regular k e T E P)

lemma pointSeriesHom_spec (a : pointLocalRing k e T E P) :
    algebraMap (PowerSeries k) (LaurentSeries k) (pointSeriesHom k e T E P a) =
      expansion k e T E P a :=
  regularLift_spec _ _ a

/-- Residue evaluation is the constant coefficient of the full regular expansion. -/
def pointResidue : pointLocalRing k e T E P →+* k :=
  PowerSeries.constantCoeff.comp (pointSeriesHom k e T E P)

lemma pointResidue_eq_localValue (a : pointLocalRing k e T E P) :
    pointResidue k e T E P a = localValue k e T E a P := by
  have hs := congrArg (fun f : LaurentSeries k => f.coeff 0) (pointSeriesHom_spec k e T E P a)
  change (HahnSeries.ofPowerSeries ℤ k (pointSeriesHom k e T E P a)).coeff (0 : ℕ) = _ at hs
  simpa only [pointResidue, RingHom.comp_apply, localValue, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff] using hs

lemma pointConstant_mem (c : k) : algebraMap k (FF k e) c ∈ pointLocalRing k e T E P := by
  rw [Valuation.mem_valuationSubring_iff]
  by_cases hc : c = 0
  · simp [hc]
  · rw [pointValuation_algebraMap k e T E P hc]

/-- The constant-field map into the actual local ring. -/
def pointConstant : k →+* pointLocalRing k e T E P :=
  (algebraMap k (FF k e)).codRestrict (pointLocalRing k e T E P).toSubring
    (pointConstant_mem k e T E P)

lemma pointSeriesHom_constant (c : k) :
    pointSeriesHom k e T E P (pointConstant k e T E P c) = PowerSeries.C c := by
  apply (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
  rw [pointSeriesHom_spec]
  change E ((T P) (algebraMap k (FF k e) c)) = _
  rw [(T P).commutes, E.commutes]
  rfl

lemma pointResidue_constant (c : k) :
    pointResidue k e T E P (pointConstant k e T E P c) = c := by
  change PowerSeries.constantCoeff (pointSeriesHom k e T E P _) = c
  rw [pointSeriesHom_constant, PowerSeries.constantCoeff_C]

lemma pointResidue_surjective : Function.Surjective (pointResidue k e T E P) :=
  fun c => ⟨pointConstant k e T E P c, pointResidue_constant k e T E P c⟩

lemma pointResidue_ker : RingHom.ker (pointResidue k e T E P) =
    IsLocalRing.maximalIdeal (pointLocalRing k e T E P) :=
  IsLocalRing.ker_eq_maximalIdeal _ (pointResidue_surjective k e T E P)

lemma pointResidue_isLocalHom : IsLocalHom (pointResidue k e T E P) :=
  IsLocalHom.of_surjective _ (pointResidue_surjective k e T E P)

/-- The residue field of the actual point valuation is canonically the base field. -/
def pointResidueFieldEquiv : IsLocalRing.ResidueField (pointLocalRing k e T E P) ≃+* k := by
  let ρ := pointResidue k e T E P
  have : IsLocalHom ρ := pointResidue_isLocalHom k e T E P
  let r := IsLocalRing.ResidueField.lift ρ
  exact RingEquiv.ofBijective r ⟨r.injective, fun c =>
    ⟨IsLocalRing.residue _ (pointConstant k e T E P c), pointResidue_constant k e T E P c⟩⟩

lemma pointResidueFieldEquiv_residue (a : pointLocalRing k e T E P) :
    pointResidueFieldEquiv k e T E P (IsLocalRing.residue _ a) = pointResidue k e T E P a := rfl

lemma pointResidue_eq_leading (a : pointLocalRing k e T E P)
    (ha : pointOrder k e T E a P = 0) :
    pointResidue k e T E P a = localLeading k e T E a P := by
  rw [pointResidue_eq_localValue]
  unfold localLeading localValue
  rw [HahnSeries.leadingCoeff_eq]
  change _ = (expansion k e T E P a).coeff (pointOrder k e T E a P)
  rw [ha]

lemma pointResidue_eq_zero_iff (a : pointLocalRing k e T E P) :
    pointResidue k e T E P a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (pointLocalRing k e T E P) := by
  rw [← pointResidue_ker, RingHom.mem_ker]

end Residues

section Product
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
variable (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)

include he hT in
lemma tameSymbol_translate (Q P : (Curve k e).Point) (f g : FF k e) :
    tameSymbol k e T E (T Q f) (T Q g) P = tameSymbol k e T E f g (P + Q) := by
  unfold tameSymbol pointOrder localLeading expansion
  rw [(translation_composition k e he T hT).2.1 P Q f,
    (translation_composition k e he T hT).2.1 P Q g]

include he hT hh hE in
lemma tameProduct_translate (Q : (Curve k e).Point) (f g : FF k e) :
    (∏ᶠ P, tameSymbol k e T E (T Q f) (T Q g) P) =
      (∏ᶠ P, tameSymbol k e T E f g P) := by
  simp_rw [tameSymbol_translate k e he T hT E Q]
  exact finprod_comp_equiv (Equiv.addRight Q)

include he hT hh hE in
lemma tameProduct_mul_left {f₁ f₂ g : FF k e}
    (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E (f₁*f₂) g P) =
      (∏ᶠ P, tameSymbol k e T E f₁ g P) * (∏ᶠ P, tameSymbol k e T E f₂ g P) := by
  simp_rw [tameSymbol_mul_left k e T E _ hf₁ hf₂ hg]
  exact finprod_mul_distrib
    (finite_tameSymbol_support k e he T hT h E hh hE f₁ g hf₁ hg)
    (finite_tameSymbol_support k e he T hT h E hh hE f₂ g hf₂ hg)

include he hT hh hE in
lemma tameProduct_mul_right {f g₁ g₂ : FF k e}
    (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E f (g₁*g₂) P) =
      (∏ᶠ P, tameSymbol k e T E f g₁ P) * (∏ᶠ P, tameSymbol k e T E f g₂ P) := by
  simp_rw [tameSymbol_mul_right k e T E _ hf hg₁ hg₂]
  exact finprod_mul_distrib
    (finite_tameSymbol_support k e he T hT h E hh hE f g₁ hf hg₁)
    (finite_tameSymbol_support k e he T hT h E hh hE f g₂ hf hg₂)

omit [CharZero k] [DecidableEq k] in
lemma tameProduct_steinberg {f : FF k e} (hf : f ≠ 0) (h1f : 1-f ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E f (1-f) P) = 1 := by
  simp_rw [tameSymbol_steinberg k e T E _ hf h1f]
  exact finprod_one

end Product

section GeometricSubfield
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord xFunction yFunction)
variable (k : Type u) [Field k] (e : Fin 3 → k)

/-- The concrete subfield generated by the actual x coordinate. -/
def xSubfield : IntermediateField k (FF k e) :=
  IntermediateField.adjoin k {xFunction k e}

lemma x_mem_xSubfield : xFunction k e ∈ xSubfield k e :=
  IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

/-- The coordinate-ring polynomial map is evaluation at the actual X. -/
lemma polynomial_to_ff (p : Polynomial k) :
    algebraMap (Coord k e) (FF k e) (algebraMap (Polynomial k) (Coord k e) p) =
      aeval (xFunction k e) p := by
  have hh : (IsScalarTower.toAlgHom k (Coord k e) (FF k e)).comp
      (IsScalarTower.toAlgHom k (Polynomial k) (Coord k e)) = aeval (xFunction k e) := by
    apply Polynomial.algHom_ext
    simp [xFunction, CoordinateRing.XClass, CoordinateRing.mk, AdjoinRoot.mk_C]
  exact DFunLike.congr_fun hh p

lemma ff_mem_of_coordinates (L : IntermediateField k (FF k e))
    (hx : xFunction k e ∈ L) (hy : yFunction k e ∈ L) (f : FF k e) : f ∈ L := by
  have hpoly (p : Polynomial k) : aeval (xFunction k e) p ∈ L := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using L.add_mem hp hq
    | monomial n c =>
      simpa only [aeval_monomial] using L.mul_mem (L.algebraMap_mem c) (L.toSubalgebra.pow_mem hx n)
  have hcoord (a : Coord k e) : algebraMap (Coord k e) (FF k e) a ∈ L := by
    obtain ⟨p,q,rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    simp only [CoordinateRing.smul, map_add, map_mul, mul_one]
    apply L.add_mem
    · change algebraMap (Coord k e) (FF k e) (algebraMap (Polynomial k) (Coord k e) p) ∈ L
      rw [polynomial_to_ff]
      exact hpoly p
    · apply L.mul_mem
      · change algebraMap (Coord k e) (FF k e) (algebraMap (Polynomial k) (Coord k e) q) ∈ L
        rw [polynomial_to_ff]
        exact hpoly q
      · simpa [yFunction, CoordinateRing.YClass] using hy
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective (Coord k e) f
  rw [← hab]
  exact L.div_mem (hcoord a) (hcoord b)

variable [CharZero k] [DecidableEq k]

lemma y_integral_over_xSubfield (he : Function.Injective e) :
    IsIntegral (xSubfield k e) (yFunction k e) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [generic_equation k e he]
  let L := xSubfield k e
  have hx : xFunction k e ∈ L := x_mem_xSubfield k e
  have hc (c : k) : algebraMap k (FF k e) c ∈ L := L.algebraMap_mem c
  have hmem : (xFunction k e)^3 -
      algebraMap k (FF k e) (e 0 + e 1 + e 2) * (xFunction k e)^2 +
      algebraMap k (FF k e) (e 0 * e 1 + e 0 * e 2 + e 1 * e 2) * xFunction k e -
      algebraMap k (FF k e) (e 0 * e 1 * e 2) ∈ L :=
    L.sub_mem (L.add_mem (L.sub_mem (L.toSubalgebra.pow_mem hx 3)
      (L.mul_mem (hc _) (L.toSubalgebra.pow_mem hx 2))) (L.mul_mem (hc _) hx)) (hc _)
  exact isIntegral_algebraMap (x := (⟨_,hmem⟩ : L))

omit [CharZero k] [DecidableEq k] in
lemma adjoin_y_over_x_eq_top :
    IntermediateField.adjoin (xSubfield k e) {yFunction k e} = ⊤ := by
  let A := IntermediateField.adjoin (xSubfield k e) {yFunction k e}
  have hy : yFunction k e ∈ A := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hx : xFunction k e ∈ A := A.algebraMap_mem ⟨_, x_mem_xSubfield k e⟩
  apply top_unique
  intro f _
  exact ff_mem_of_coordinates k e (A.restrictScalars k) hx hy f

lemma y_sq_mem_xSubfield (he : Function.Injective e) :
    (yFunction k e)^2 ∈ xSubfield k e := by
  rw [generic_equation k e he]
  let L := xSubfield k e
  have hx : xFunction k e ∈ L := x_mem_xSubfield k e
  have hc (c : k) : algebraMap k (FF k e) c ∈ L := L.algebraMap_mem c
  exact L.sub_mem (L.add_mem (L.sub_mem (L.toSubalgebra.pow_mem hx 3)
    (L.mul_mem (hc _) (L.toSubalgebra.pow_mem hx 2))) (L.mul_mem (hc _) hx)) (hc _)

/-- Every actual rational function has quadratic normal form over the geometric X-subfield. -/
lemma ff_quadratic_normal_form (he : Function.Injective e) (f : FF k e) :
    ∃ a b : xSubfield k e, f = (a : FF k e) + (b : FF k e) * yFunction k e := by
  let L := xSubfield k e
  have hf : f ∈ Algebra.adjoin L {yFunction k e} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (y_integral_over_xSubfield k e he).isAlgebraic]
    change f ∈ IntermediateField.adjoin L {yFunction k e}
    rw [adjoin_y_over_x_eq_top]
    trivial
  induction hf using Algebra.adjoin_induction with
  | mem z hz =>
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨0, 1, by simp⟩
  | algebraMap a => exact ⟨a, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,b,rfl⟩ := hx
    obtain ⟨c,d,rfl⟩ := hy
    refine ⟨a+c,b+d,?_⟩
    change _ = ((a : FF k e)+c)+((b : FF k e)+d)*yFunction k e
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨a,b,rfl⟩ := hx
    obtain ⟨c,d,rfl⟩ := hy
    let q : L := ⟨(yFunction k e)^2, y_sq_mem_xSubfield k e he⟩
    refine ⟨a*c+b*d*q,a*d+b*c,?_⟩
    change _ = (a : FF k e)*c+b*d*(yFunction k e)^2 +
      ((a : FF k e)*d+b*c)*yFunction k e
    ring

/-- The actual function field is finite-dimensional over its concrete x-subfield.
No unrelated scalar action is supplied as a hypothesis. -/
theorem finite_over_xSubfield (he : Function.Injective e) :
    FiniteDimensional (xSubfield k e) (FF k e) := by
  let L := xSubfield k e
  let A := IntermediateField.adjoin L {yFunction k e}
  have ht : A = ⊤ := adjoin_y_over_x_eq_top k e
  have : FiniteDimensional L A :=
    IntermediateField.adjoin.finiteDimensional (y_integral_over_xSubfield k e he)
  have hs : Function.Surjective A.val := by
    intro f
    exact ⟨⟨f, ht ▸ IntermediateField.mem_top⟩, rfl⟩
  exact Module.Finite.of_surjective A.val.toLinearMap hs

/-- The geometric rational-function embedding sends the indeterminate to X. -/
def xRatFuncMap (he : Function.Injective e) : RatFunc k →ₐ[k] FF k e :=
  (xSubfield k e).val.comp
    (RatFunc.algEquivOfTranscendental (xFunction k e) (x_transcendental k e he)).toAlgHom

lemma xRatFuncMap_X (he : Function.Injective e) :
    xRatFuncMap k e he RatFunc.X = xFunction k e := by
  change ((RatFunc.algEquivOfTranscendental (xFunction k e)
    (x_transcendental k e he)) RatFunc.X : FF k e) = xFunction k e
  exact RatFunc.algEquivOfTranscendental_X _ _

/-- Finite-dimensionality for precisely the scalar action induced by X ↦ X. -/
theorem finite_over_xRatFuncMap (he : Function.Injective e) :
    let : Algebra (RatFunc k) (FF k e) := (xRatFuncMap k e he).toRingHom.toAlgebra
    FiniteDimensional (RatFunc k) (FF k e) := by
  let : Algebra (RatFunc k) (FF k e) := (xRatFuncMap k e he).toRingHom.toAlgebra
  let L := xSubfield k e
  let φ := RatFunc.algEquivOfTranscendental (xFunction k e) (x_transcendental k e he)
  let : Algebra (RatFunc k) L := φ.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) L (FF k e) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (RatFunc k) L :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) L) φ.surjective
  have : FiniteDimensional L (FF k e) := finite_over_xSubfield k e he
  exact Module.Finite.trans L (FF k e)

lemma xRatFuncMap_scalarTower (he : Function.Injective e) :
    let : Algebra (RatFunc k) (FF k e) := (xRatFuncMap k e he).toRingHom.toAlgebra
    IsScalarTower k (RatFunc k) (FF k e) := by
  let : Algebra (RatFunc k) (FF k e) := (xRatFuncMap k e he).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c => ((xRatFuncMap k e he).commutes c).symm

/-- A general symbol is a finite product of symbols with second argument in
 the actual X-subfield. The list and nonvanishing proofs are constructed. -/
theorem tameSymbol_quadratic_reduction (he : Function.Injective e)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ pairs : List (FF k e × xSubfield k e),
      (∀ z ∈ pairs, z.1 ≠ 0 ∧ z.2 ≠ 0) ∧
      ∀ P : (Curve k e).Point, tameSymbol k e T E f g P =
        (pairs.map fun z => tameSymbol k e T E z.1 (z.2 : FF k e) P).prod := by
  obtain ⟨a,b,hab⟩ := ff_quadratic_normal_form k e he f
  obtain ⟨c,d,hcd⟩ := ff_quadratic_normal_form k e he g
  by_cases hb : b = 0
  · have hfa : f = (a : FF k e) := by simpa [hb] using hab
    have ha : a ≠ 0 := by intro hz; apply hf; simp [hfa,hz]
    refine ⟨[(g⁻¹,a)], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      subst z
      exact ⟨inv_ne_zero hg,ha⟩
    · intro P
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [tameSymbol_inv_left k e T E P hg (by simpa [← hfa] using hf)]
      rw [← hfa, tameSymbol_swap k e T E P g f]
  · let r : xSubfield k e := d/b
    let s : xSubfield k e := c-r*a
    have hb' : (b : FF k e) ≠ 0 := by exact_mod_cast hb
    have hpencil : g = (r : FF k e)*f+(s : FF k e) := by
      rw [hab,hcd]
      change _ = ((d : FF k e)/b)*((a : FF k e)+b*yFunction k e)+
        ((c : FF k e)-((d : FF k e)/b)*a)
      field_simp
      ring
    by_cases hr : r = 0
    · have hgs : g = (s : FF k e) := by simpa [hr] using hpencil
      have hs : s ≠ 0 := by intro hz; apply hg; simp [hgs,hz]
      refine ⟨[(f,s)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        subst z
        exact ⟨hf,hs⟩
      · intro P
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [hgs]
    · have hr' : (r : FF k e) ≠ 0 := by exact_mod_cast hr
      by_cases hs : s = 0
      · have hgrf : g = (r : FF k e)*f := by simpa [hs] using hpencil
        refine ⟨[(f,r),(f,-1)], ?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact ⟨hf,hr⟩
          · exact ⟨hf,neg_ne_zero.mpr one_ne_zero⟩
        · intro P
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [hgrf, tameSymbol_mul_right k e T E P hf hr' hf, tameSymbol_self k e T E P hf]
          rfl
      · have hs' : (s : FF k e) ≠ 0 := by exact_mod_cast hs
        refine ⟨[((r : FF k e)*f,s),(g,-1),(g,r),(g⁻¹,s)], ?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact ⟨mul_ne_zero hr' hf,hs⟩
          · exact ⟨hg,neg_ne_zero.mpr one_ne_zero⟩
          · exact ⟨hg,hr⟩
          · exact ⟨inv_ne_zero hg,hs⟩
        · intro P
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [tameSymbol_pencil k e T E P hf hg hr' hs' hpencil,
            tameSymbol_inv_left k e T E P hg hs']
          simp only [show ((-1 : xSubfield k e) : FF k e) = -1 from rfl,
            div_eq_mul_inv, mul_assoc]

lemma finite_tameSymbol_list_support (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (pairs : List (FF k e × xSubfield k e))
    (hn : ∀ z ∈ pairs, z.1 ≠ 0 ∧ z.2 ≠ 0) :
    Function.HasFiniteMulSupport (fun P : (Curve k e).Point =>
      (pairs.map fun z => tameSymbol k e T E z.1 (z.2 : FF k e) P).prod) := by
  induction pairs with
  | nil => simpa using (Function.hasFiniteMulSupport_one :
      Function.HasFiniteMulSupport (fun _ : (Curve k e).Point => (1 : k)))
  | cons z zs ih =>
    have hz := hn z (List.mem_cons_self ..)
    have htail : ∀ z ∈ zs, z.1 ≠ 0 ∧ z.2 ≠ 0 :=
      fun z hz => hn z (List.mem_cons_of_mem _ hz)
    have hhead := finite_tameSymbol_support k e he T hT h E hh hE z.1 z.2 hz.1
      (by exact_mod_cast hz.2)
    have ht : Set.Finite {P : (Curve k e).Point |
        (zs.map fun z => tameSymbol k e T E z.1 (z.2 : FF k e) P).prod ≠ 1} := ih htail
    apply (hhead.union ht).subset
    intro P hP
    by_contra hnot
    have H := not_or.mp hnot
    apply hP
    simp only [List.map_cons, List.prod_cons]
    rw [not_ne_iff.mp H.1, not_ne_iff.mp H.2, one_mul]

lemma finprod_tameSymbol_list (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (pairs : List (FF k e × xSubfield k e))
    (hn : ∀ z ∈ pairs, z.1 ≠ 0 ∧ z.2 ≠ 0) :
    (∏ᶠ P : (Curve k e).Point,
      (pairs.map fun z => tameSymbol k e T E z.1 (z.2 : FF k e) P).prod) =
      (pairs.map fun z => ∏ᶠ P : (Curve k e).Point,
        tameSymbol k e T E z.1 (z.2 : FF k e) P).prod := by
  induction pairs with
  | nil => simp
  | cons z zs ih =>
    have hz := hn z (List.mem_cons_self ..)
    have htail : ∀ z ∈ zs, z.1 ≠ 0 ∧ z.2 ≠ 0 :=
      fun z hz => hn z (List.mem_cons_of_mem _ hz)
    simp only [List.map_cons, List.prod_cons]
    rw [finprod_mul_distrib
      (finite_tameSymbol_support k e he T hT h E hh hE z.1 z.2 hz.1
        (by exact_mod_cast hz.2))
      (finite_tameSymbol_list_support k e he T hT h E hh hE zs htail), ih htail]

/-- An exact finite reduction of the global product; all resulting second
arguments belong to the specific geometric X-subfield. -/
theorem tameProduct_quadratic_reduction (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ pairs : List (FF k e × xSubfield k e),
      (∀ z ∈ pairs, z.1 ≠ 0 ∧ z.2 ≠ 0) ∧
      (∏ᶠ P : (Curve k e).Point, tameSymbol k e T E f g P) =
        (pairs.map fun z => ∏ᶠ P : (Curve k e).Point,
          tameSymbol k e T E z.1 (z.2 : FF k e) P).prod := by
  obtain ⟨pairs,hn,hpairs⟩ := tameSymbol_quadratic_reduction k e he T E f g hf hg
  refine ⟨pairs,hn,?_⟩
  rw [finprod_congr hpairs]
  exact finprod_tameSymbol_list k e he T hT h E hh hE pairs hn

omit [CharZero k] [DecidableEq k] in
/-- Algebraic closedness factors every nonzero element of the geometric X-subfield
into constants and actual vertical functions X-a, with multiplicities retained. -/
theorem xSubfield_factorization [IsAlgClosed k] (a : xSubfield k e) (ha : a ≠ 0) :
    ∃ (c : k) (zeros poles : Multiset k), c ≠ 0 ∧
      (a : FF k e) = algebraMap k (FF k e) c *
        (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
        (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod := by
  obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff k (a : FF k e)).mp a.property
  have ha' : (a : FF k e) ≠ 0 := by exact_mod_cast ha
  have hp : p ≠ 0 := by intro hz; apply ha'; simpa [hz] using hpq
  have hq : q ≠ 0 := by intro hz; apply ha'; simpa [hz] using hpq
  have hfactor (p : Polynomial k) : aeval (xFunction k e) p =
      algebraMap k (FF k e) p.leadingCoeff *
      (p.roots.map fun z => xFunction k e-algebraMap k (FF k e) z).prod := by
    have hf := congrArg (aeval (xFunction k e)) (IsAlgClosed.splits p).eq_prod_roots
    simpa only [map_mul, aeval_C, map_multiset_prod, Multiset.map_map, Function.comp_def,
      map_sub, aeval_X] using hf
  refine ⟨p.leadingCoeff/q.leadingCoeff,p.roots,q.roots,
    div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq),?_⟩
  rw [hpq,hfactor,hfactor,map_div₀]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Pullback of geometric negation, constructed from X ↦ X and Y ↦ -Y. -/
def curveNegationHom (he : Function.Injective e) : FF k e →ₐ[k] FF k e :=
  (lift_coordinates k e (xFunction k e) (-yFunction k e) (x_transcendental k e he)
    (by simpa using generic_equation k e he)).choose

lemma curveNegationHom_X (he : Function.Injective e) :
    curveNegationHom k e he (xFunction k e) = xFunction k e :=
  (lift_coordinates k e (xFunction k e) (-yFunction k e) (x_transcendental k e he)
    (by simpa using generic_equation k e he)).choose_spec.1

lemma curveNegationHom_Y (he : Function.Injective e) :
    curveNegationHom k e he (yFunction k e) = -yFunction k e :=
  (lift_coordinates k e (xFunction k e) (-yFunction k e) (x_transcendental k e he)
    (by simpa using generic_equation k e he)).choose_spec.2

lemma curveNegationHom_involutive (he : Function.Injective e) :
    Function.Involutive (curveNegationHom k e he) := by
  have hh : (curveNegationHom k e he).comp (curveNegationHom k e he) = AlgHom.id k (FF k e) := by
    apply ff_ext k e
    · simp only [AlgHom.comp_apply, curveNegationHom_X, AlgHom.id_apply]
    · simp only [AlgHom.comp_apply, curveNegationHom_Y, map_neg, neg_neg, AlgHom.id_apply]
  intro f
  exact DFunLike.congr_fun hh f

def curveNegation (he : Function.Injective e) : FF k e ≃ₐ[k] FF k e :=
  AlgEquiv.ofBijective (curveNegationHom k e he) (curveNegationHom_involutive k e he).bijective

lemma curveNegation_X (he : Function.Injective e) :
    curveNegation k e he (xFunction k e) = xFunction k e := curveNegationHom_X k e he

lemma curveNegation_Y (he : Function.Injective e) :
    curveNegation k e he (yFunction k e) = -yFunction k e := curveNegationHom_Y k e he

lemma curveNegation_involutive (he : Function.Injective e) :
    Function.Involutive (curveNegation k e he) := curveNegationHom_involutive k e he

lemma curveNegation_fixed_xSubfield (he : Function.Injective e) (a : xSubfield k e) :
    curveNegation k e he (a : FF k e) = a := by
  obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff k (a : FF k e)).mp a.property
  have hp (p : Polynomial k) : curveNegation k e he (aeval (xFunction k e) p) =
      aeval (xFunction k e) p := by
    rw [← aeval_algHom_apply, curveNegation_X]
  rw [hpq,map_div₀,hp,hp]

/-- Product with the actual geometric conjugate. -/
def conjugateProduct (he : Function.Injective e) (f : FF k e) : FF k e :=
  f * curveNegation k e he f

lemma conjugateProduct_mem (he : Function.Injective e) (f : FF k e) :
    conjugateProduct k e he f ∈ xSubfield k e := by
  obtain ⟨a,b,hf⟩ := ff_quadratic_normal_form k e he f
  have hn : conjugateProduct k e he f = (a : FF k e)^2 - (b : FF k e)^2*(yFunction k e)^2 := by
    unfold conjugateProduct
    rw [hf,map_add,map_mul,curveNegation_fixed_xSubfield,curveNegation_fixed_xSubfield,curveNegation_Y]
    ring
  rw [hn]
  exact (xSubfield k e).sub_mem ((xSubfield k e).toSubalgebra.pow_mem a.property 2)
    ((xSubfield k e).mul_mem ((xSubfield k e).toSubalgebra.pow_mem b.property 2)
      (y_sq_mem_xSubfield k e he))

lemma conjugateProduct_ne_zero (he : Function.Injective e) {f : FF k e} (hf : f ≠ 0) :
    conjugateProduct k e he f ≠ 0 := by
  exact mul_ne_zero hf (by simpa using (curveNegation k e he).injective.ne hf)

end GeometricSubfield

section LaurentNegation
open ArithmeticThetaMillerR0114
variable (k : Type u) [Field k]
lemma powerSign_involutive : Function.Involutive (PowerSeries.rescale (-1 : k)) := by
  intro f
  simp [PowerSeries.rescale_rescale]
def laurentSignHom : LaurentSeries k →+* LaurentSeries k :=
  IsFractionRing.lift
    (g := (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (PowerSeries.rescale (-1)))
    ((IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
      (powerSign_involutive k).injective)
def laurentSign : LaurentSeries k →ₐ[k] LaurentSeries k :=
  { laurentSignHom k with
    commutes' := fun c => by
      change laurentSignHom k (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C c)) = _
      rw [laurentSignHom, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
      have hc : PowerSeries.rescale (-1 : k) (PowerSeries.C c) = PowerSeries.C c := by
        ext n
        simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
        split_ifs with hn <;> simp [hn]
      rw [hc]
      rfl }
lemma laurentSign_coe (a : PowerSeries k) :
    laurentSign k (algebraMap (PowerSeries k) (LaurentSeries k) a) =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.rescale (-1) a) := by
  change laurentSignHom k _ = _
  rw [laurentSignHom, IsFractionRing.lift_algebraMap]
  rfl
lemma laurentSign_parameter : laurentSign k (parameter k) = -parameter k := by
  unfold parameter
  rw [laurentSign_coe, PowerSeries.rescale_neg_one_X, map_neg]
lemma laurentSign_involutive : Function.Involutive (laurentSign k) := by
  have he : (laurentSign k).comp (laurentSign k) = AlgHom.id k (LaurentSeries k) := by
    apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.ringHom_ext (A := PowerSeries k)
    intro a
    change laurentSign k (laurentSign k (algebraMap (PowerSeries k) (LaurentSeries k) a)) = _
    rw [laurentSign_coe, laurentSign_coe]
    simp [PowerSeries.rescale_rescale]
  exact fun f => DFunLike.congr_fun he f
lemma laurentSign_single (n : ℤ) :
    laurentSign k (HahnSeries.single n (1 : k)) = HahnSeries.single n ((-1 : k)^n) := by
  have ht : HahnSeries.single (1 : ℤ) (1 : k) = parameter k := by
    exact (HahnSeries.ofPowerSeries_X).symm
  rw [RatFunc.single_zpow, ht, map_zpow₀, laurentSign_parameter,
    neg_eq_neg_one_mul, mul_zpow]
  have hc : (-1 : LaurentSeries k)^n = algebraMap k (LaurentSeries k) ((-1 : k)^n) := by
    simp
  rw [hc, ← ht, ← RatFunc.single_zpow]
  change (HahnSeries.ofPowerSeries ℤ k (PowerSeries.C ((-1 : k)^n))) * _ = _
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  rw [HahnSeries.single_mul_single, zero_add, mul_one]
lemma series_leading_zero (s : PowerSeries k) (hs : PowerSeries.constantCoeff s ≠ 0) :
    (algebraMap (PowerSeries k) (LaurentSeries k) s).leadingCoeff =
      PowerSeries.constantCoeff s := by
  rw [HahnSeries.leadingCoeff_eq, series_order_zero k s hs]
  change (HahnSeries.ofPowerSeries ℤ k s).coeff (0 : ℕ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff]
lemma laurentSign_order_leading (a : LaurentSeries k) :
    (laurentSign k a).order = a.order ∧
    (laurentSign k a).leadingCoeff = (-1 : k)^a.order * a.leadingCoeff := by
  by_cases ha : a = 0
  · simp [ha]
  have hc : PowerSeries.constantCoeff a.powerSeriesPart ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff,
      Nat.cast_zero, add_zero]
    exact HahnSeries.coeff_order_eq_zero.not.mpr ha
  have hs : PowerSeries.constantCoeff (PowerSeries.rescale (-1) a.powerSeriesPart) ≠ 0 := by
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hc
  have hn : algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.rescale (-1) a.powerSeriesPart) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne
      (show PowerSeries.rescale (-1) a.powerSeriesPart ≠ 0 from fun hz => hs (by rw [hz, map_zero]))
  have he : laurentSign k a = HahnSeries.single a.order ((-1 : k)^a.order) *
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.rescale (-1) a.powerSeriesPart) := by
    conv_lhs => rw [← a.single_order_mul_powerSeriesPart]
    rw [map_mul, laurentSign_single]
    exact congrArg _ (laurentSign_coe k _)
  rw [he]
  constructor
  · rw [HahnSeries.order_mul (HahnSeries.single_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) hn,
      HahnSeries.order_single (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
      series_order_zero k _ hs, add_zero]
  · rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single,
      series_leading_zero k _ hs]
    have hh : PowerSeries.constantCoeff (PowerSeries.rescale (-1) a.powerSeriesPart) = a.leadingCoeff := by
      simp only [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
        pow_zero, one_mul, LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero,
        HahnSeries.leadingCoeff_eq]
    rw [hh]
lemma branch_rescale [CharZero k] (e : Fin 3 → k) (h : PowerSeries k)
    (hh : branchEquation k e h) : PowerSeries.rescale (-1) h = h := by
  apply (infinity_branch k e).unique
  · constructor
    · simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hh.1
    · have hx : PowerSeries.rescale (-1 : k) (PowerSeries.X ^ 2) = PowerSeries.X ^ 2 := by
        rw [map_pow, PowerSeries.rescale_neg_one_X, neg_sq]
      have hc (a : k) : PowerSeries.rescale (-1 : k) (PowerSeries.C a) = PowerSeries.C a := by
        ext n
        simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
        split_ifs with hn <;> simp [hn]
      simpa only [map_pow, map_prod, map_sub, map_mul, hx, hc] using
        congrArg (PowerSeries.rescale (-1 : k)) hh.2
  · exact hh
lemma laurentSign_infinityX [CharZero k] (e : Fin 3 → k) (h : PowerSeries k)
    (hh : branchEquation k e h) : laurentSign k (infinityX k h) = infinityX k h := by
  unfold infinityX
  rw [map_mul, map_zpow₀, laurentSign_parameter, laurentSign_coe, branch_rescale k e h hh]
  simp
lemma laurentSign_infinityY [CharZero k] (e : Fin 3 → k) (h : PowerSeries k)
    (hh : branchEquation k e h) : laurentSign k (infinityY k h) = -infinityY k h := by
  unfold infinityY
  rw [map_neg, map_mul, map_zpow₀, laurentSign_parameter, laurentSign_coe, branch_rescale k e h hh]
  simp only [zpow_neg, zpow_ofNat]
  rw [show (-parameter k)^3 = -(parameter k)^3 by ring]
  simp
lemma infinity_curveNegation [CharZero k] [DecidableEq k] (e : Fin 3 → k)
    (he : Function.Injective e) (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E) (f : FF k e) :
    E (curveNegation k e he f) = laurentSign k (E f) := by
  have hp : E.comp (curveNegation k e he).toAlgHom = (laurentSign k).comp E := by
    apply ff_ext k e
    · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, curveNegation_X, hE.1,
        laurentSign_infinityX k e h hh]
    · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, curveNegation_Y, map_neg, hE.2,
        laurentSign_infinityY k e h hh]
  exact DFunLike.congr_fun hp f
lemma curveNegation_generic [CharZero k] [DecidableEq k] (e : Fin 3 → k)
    (he : Function.Injective e) :
    WeierstrassCurve.Affine.Point.map (W' := Curve k e) (curveNegation k e he).toAlgHom
      (genericPoint k e he) = -genericPoint k e he := by
  simp only [genericPoint, WeierstrassCurve.Affine.Point.map_some,
    WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq,
    AlgEquiv.coe_toAlgHom, curveNegation_X, curveNegation_Y]
  simp [WeierstrassCurve.Affine.negY, Curve, ArithmeticThetaMillerR0114.Curve,
    ArithmeticThetaFourTorsion.splitCurve, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]
lemma curveNegation_translation [CharZero k] [DecidableEq k] (e : Fin 3 → k)
    (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
    (P : (Curve k e).Point) (f : FF k e) :
    T P (curveNegation k e he f) = curveNegation k e he (T (-P) f) := by
  have hp : WeierstrassCurve.Affine.Point.map (W' := Curve k e) (T P).toAlgHom
      (WeierstrassCurve.Affine.Point.map (W' := Curve k e) (curveNegation k e he).toAlgHom
        (genericPoint k e he)) =
      WeierstrassCurve.Affine.Point.map (W' := Curve k e) (curveNegation k e he).toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := Curve k e) (T (-P)).toAlgHom
          (genericPoint k e he)) := by
    rw [curveNegation_generic, map_neg, map_generic_translation k e he T hT P,
      map_generic_translation k e he T hT (-P), map_add, curveNegation_generic,
      map_constant, map_neg, neg_add]
  change WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some _ _ _ at hp
  obtain ⟨hx,hy⟩ := WeierstrassCurve.Affine.Point.some.inj hp
  have hh : (T P).toAlgHom.comp (curveNegation k e he).toAlgHom =
      (curveNegation k e he).toAlgHom.comp (T (-P)).toAlgHom := ff_ext k e hx hy
  exact DFunLike.congr_fun hh f
section ConjugateLocal
variable [CharZero k] [DecidableEq k] (e : Fin 3 → k) (he : Function.Injective e)
variable (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)
include hh hE hT in
lemma expansion_curveNegation (P : (Curve k e).Point) (f : FF k e) :
    expansion k e T E P (curveNegation k e he f) =
      laurentSign k (expansion k e T E (-P) f) := by
  unfold expansion
  rw [curveNegation_translation k e he T hT,
    infinity_curveNegation k e he h E hh hE]
include hh hE hT in
lemma pointOrder_curveNegation (P : (Curve k e).Point) (f : FF k e) :
    pointOrder k e T E (curveNegation k e he f) P = pointOrder k e T E f (-P) := by
  unfold pointOrder
  rw [expansion_curveNegation k e he T hT h E hh hE]
  exact (laurentSign_order_leading k _).1
include hh hE hT in
lemma localLeading_curveNegation (P : (Curve k e).Point) (f : FF k e) :
    localLeading k e T E (curveNegation k e he f) P =
      (-1 : k) ^ pointOrder k e T E f (-P) * localLeading k e T E f (-P) := by
  unfold localLeading
  rw [expansion_curveNegation k e he T hT h E hh hE]
  exact (laurentSign_order_leading k _).2
include hh hE hT in
lemma conjugateProduct_order (P : (Curve k e).Point) (f : FF k e) (hf : f ≠ 0) :
    pointOrder k e T E (conjugateProduct k e he f) P =
      pointOrder k e T E f P + pointOrder k e T E f (-P) := by
  rw [conjugateProduct, pointOrder_mul k e T E P hf
    (by simpa using (curveNegation k e he).injective.ne hf),
    pointOrder_curveNegation k e he T hT h E hh hE]
include hh hE hT in
lemma conjugateProduct_leading (P : (Curve k e).Point) (f : FF k e) :
    localLeading k e T E (conjugateProduct k e he f) P =
      (-1 : k) ^ pointOrder k e T E f (-P) *
        localLeading k e T E f P * localLeading k e T E f (-P) := by
  rw [conjugateProduct, localLeading_mul,
    localLeading_curveNegation k e he T hT h E hh hE]
  ring
end ConjugateLocal

end LaurentNegation

section VerticalDivisors
set_option backward.isDefEq.respectTransparency false
open ArithmeticThetaMillerR0114
open WeierstrassCurve.Affine
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)
lemma expansion_constant (P : (Curve k e).Point) (c : k) :
    expansion k e T E P (algebraMap k (FF k e) c) =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C c) := by
  simp only [expansion, AlgEquiv.commutes, AlgHom.commutes]
  rfl
lemma pointOrder_constant (P : (Curve k e).Point) (c : k) :
    pointOrder k e T E (algebraMap k (FF k e) c) P = 0 := by
  unfold pointOrder
  rw [expansion_constant]
  by_cases hc : c = 0
  · simp [hc]
  · exact series_order_zero k _ (by simpa using hc)
lemma localLeading_constant (P : (Curve k e).Point) (c : k) :
    localLeading k e T E (algebraMap k (FF k e) c) P = c := by
  unfold localLeading
  rw [expansion_constant]
  by_cases hc : c = 0
  · simp [hc]
  · exact (series_leading_zero k _ (by simpa using hc)).trans (PowerSeries.constantCoeff_C _)
include hT hh hE in
lemma vertical_expansion_affine (a b z : k) (hp : (Curve k e).Nonsingular a b) :
    expansion k e T E (.some a b hp) (xFunction k e-algebraMap k (FF k e) z) =
      algebraMap (PowerSeries k) (LaurentSeries k) (localX k e h a b-PowerSeries.C z) := by
  change E (T _ (_-_)) = _
  rw [map_sub, map_sub]
  change expansion k e T E _ (xFunction k e) - expansion k e T E _ (algebraMap k (FF k e) z) = _
  rw [(translated_coordinate_series k e T hT h E hh hE a b hp).1, expansion_constant, map_sub]
include hT hh hE in
lemma vertical_at_other (a b z : k) (hp : (Curve k e).Nonsingular a b) (hz : a ≠ z) :
    pointOrder k e T E (xFunction k e-algebraMap k (FF k e) z) (.some a b hp) = 0 ∧
    localLeading k e T E (xFunction k e-algebraMap k (FF k e) z) (.some a b hp) = a-z := by
  have hc : PowerSeries.constantCoeff (localX k e h a b-PowerSeries.C z) = a-z := by
    rw [map_sub, PowerSeries.constantCoeff_C, (localXY_constant k e hh.1 a b).1]
  unfold pointOrder localLeading
  rw [vertical_expansion_affine k e T hT h E hh hE]
  exact ⟨series_order_zero k _ (by rw [hc]; exact sub_ne_zero.mpr hz),
    (series_leading_zero k _ (by rw [hc]; exact sub_ne_zero.mpr hz)).trans hc⟩
include hT hh hE in
lemma vertical_leading_unramified (a b : k) (hp : (Curve k e).Nonsingular a b) (hb : b ≠ 0) :
    localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) = 2*b := by
  unfold localLeading
  rw [vertical_expansion_affine k e T hT h E hh hE]
  simp only [localX, add_sub_cancel_left, map_mul, HahnSeries.leadingCoeff_mul]
  have hx : (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X).leadingCoeff = 1 := by
    change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X).leadingCoeff = 1
    rw [HahnSeries.ofPowerSeries_X, HahnSeries.leadingCoeff_of_single]
  rw [hx, one_mul, series_leading_zero k _ (by rw [localR_constant k e hh.1]; exact mul_ne_zero two_ne_zero hb),
    localR_constant k e hh.1]
include hT hh hE in
lemma vertical_at_infinity (z : k) :
    pointOrder k e T E (xFunction k e-algebraMap k (FF k e) z) 0 = -2 ∧
    localLeading k e T E (xFunction k e-algebraMap k (FF k e) z) 0 = 1 := by
  have ht : parameter k ^ (-2 : ℤ) = HahnSeries.single (-2 : ℤ) (1 : k) := by
    rw [RatFunc.single_zpow]
    congr 1
    exact HahnSeries.ofPowerSeries_X
  have hx : expansion k e T E 0 (xFunction k e-algebraMap k (FF k e) z) =
      HahnSeries.single (-2 : ℤ) (1 : k) *
        algebraMap (PowerSeries k) (LaurentSeries k) (h-PowerSeries.C z*PowerSeries.X^2) := by
    unfold expansion
    rw [translation_zero k e T hT]
    change E (xFunction k e - algebraMap k (FF k e) z) = _
    rw [map_sub, E.commutes, hE.1, infinityX]
    rw [map_sub, map_mul, map_pow, mul_sub, ← ht]
    change parameter k ^ (-2 : ℤ) * _ - algebraMap k (LaurentSeries k) z =
      parameter k ^ (-2 : ℤ) * _ - parameter k ^ (-2 : ℤ) * (algebraMap k (LaurentSeries k) z * parameter k ^ (2 : ℕ))
    congr 1
    rw [mul_left_comm, ← zpow_natCast (parameter k) 2, ← zpow_add₀ (parameter_ne_zero k)]
    norm_num
  have hc : PowerSeries.constantCoeff (h-PowerSeries.C z*PowerSeries.X^2) = 1 := by simp [hh.1]
  have hn : algebraMap (PowerSeries k) (LaurentSeries k) (h-PowerSeries.C z*PowerSeries.X^2) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne
      (show h-PowerSeries.C z*PowerSeries.X^2 ≠ 0 from fun hz => by simpa [hz] using hc)
  unfold pointOrder localLeading
  rw [hx]
  constructor
  · rw [HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero) hn,
      HahnSeries.order_single one_ne_zero, series_order_zero k _ (by rw [hc]; exact one_ne_zero)]
    norm_num
  · rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single, one_mul,
      series_leading_zero k _ (by rw [hc]; exact one_ne_zero), hc]
lemma affine_neg (a b : k) (hp : (Curve k e).Nonsingular a b) :
    -Point.some a b hp = Point.some a (-b)
      (by simpa [negY, Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve]
        using (nonsingular_neg (W' := Curve k e) a b).mpr hp) := by
  rw [Point.neg_some, Point.some.injEq]
  simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve]
lemma exists_point_over [IsAlgClosed k] (he : Function.Injective e) (a : k) :
    ∃ b : k, (Curve k e).Nonsingular a b := by
  obtain ⟨b,hb⟩ := IsAlgClosed.exists_pow_nat_eq ((a-e 0)*(a-e 1)*(a-e 2)) (by omega : 0 < 2)
  letI : (Curve k e).IsElliptic := ArithmeticThetaFourTorsion.split_elliptic (e 0) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  refine ⟨b, equation_iff_nonsingular.mp ?_⟩
  exact (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a b).mpr hb
include hT hh hE in
lemma vertical_order_formula (a b : k) (hp : (Curve k e).Nonsingular a b)
    (P : (Curve k e).Point) :
    pointOrder k e T E (xFunction k e-algebraMap k (FF k e) a) P =
      (if P = Point.some a b hp then 1 else 0) +
      (if P = -Point.some a b hp then 1 else 0) - (if P = 0 then 2 else 0) := by
  classical
  cases P with
  | zero =>
    simp only [show (Point.zero : (Curve k e).Point) = 0 from rfl]
    simpa using (vertical_at_infinity k e T hT h E hh hE a).1
  | some x y hxy =>
    rw [affine_neg]
    simp only [Point.some.injEq, Point.some_ne_zero, if_false, sub_zero]
    by_cases hx : x = a
    · subst x
      have hy : y^2 = b^2 := by
        have h1 := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a y).mp hxy.1
        have h2 := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a b).mp hp.1
        exact h1.trans h2.symm
      rw [(local_orders k e T hT h E hh hE a y hxy).1]
      rcases eq_or_eq_neg_of_sq_eq_sq y b hy with hyb | hyb
      · subst y
        by_cases hb : b = 0
        · simp [hb]
        · have hn : b ≠ -b := by intro heq; apply hb; linear_combination (1/2 : k) * heq
          simp [hb, hn]
      · subst y
        by_cases hb : b = 0
        · simp [hb]
        · have hn : -b ≠ b := by intro heq; apply hb; linear_combination (-1/2 : k) * heq
          simp [hb, hn]
    · rw [(vertical_at_other k e T hT h E hh hE x y a hxy hx).1]
      simp [hx]
include hT hh hE in
lemma vertical_degree_zero [IsAlgClosed k] (he : Function.Injective e) (a : k) :
    (∑ᶠ P, pointOrder k e T E (xFunction k e-algebraMap k (FF k e) a) P) = 0 := by
  classical
  obtain ⟨b,hp⟩ := exists_point_over k e he a
  simp_rw [vertical_order_formula k e T hT h E hh hE a b hp]
  have h1 : Function.HasFiniteSupport (fun P : (Curve k e).Point => if P = Point.some a b hp then (1 : ℤ) else 0) := by
    apply (Set.finite_singleton _).subset
    intro P hP
    simpa only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_singleton_iff] using hP
  have h2 : Function.HasFiniteSupport (fun P : (Curve k e).Point => if P = -Point.some a b hp then (1 : ℤ) else 0) := by
    apply (Set.finite_singleton _).subset
    intro P hP
    simpa only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_singleton_iff] using hP
  have h0 : Function.HasFiniteSupport (fun P : (Curve k e).Point => if P = 0 then (2 : ℤ) else 0) := by
    apply (Set.finite_singleton (0 : (Curve k e).Point)).subset
    intro P hP
    by_contra hn
    apply hP
    simp only [Set.mem_singleton_iff] at hn
    simp [hn]
  have hs := finsum_sub_distrib (h1.add h2) h0
  simp only [Pi.add_apply] at hs
  rw [hs, finsum_add_distrib h1 h2]
  have hd (q : (Curve k e).Point) (n : ℤ) : (∑ᶠ P, if P = q then n else 0) = n := by
    rw [finsum_eq_single _ q (by intro P hP; simp [hP])]
    simp
  rw [hd, hd, hd]
  norm_num
lemma pointOrder_div (P : (Curve k e).Point) (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    pointOrder k e T E (f/g) P = pointOrder k e T E f P-pointOrder k e T E g P := by
  have hv := pointOrder_mul k e T E P (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ _ hg] at hv
  omega
/-- Degree of the actual finite principal divisor. -/
def principalDegree (f : FF k e) : ℤ := ∑ᶠ P, pointOrder k e T E f P
lemma principalDegree_constant (c : k) : principalDegree k e T E (algebraMap k (FF k e) c) = 0 := by
  unfold principalDegree
  simp_rw [pointOrder_constant]
  simp
include hT hh hE in
lemma principalDegree_mul (he : Function.Injective e) (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDegree k e T E (f*g) = principalDegree k e T E f+principalDegree k e T E g := by
  unfold principalDegree
  simp_rw [pointOrder_mul k e T E _ hf hg]
  exact finsum_add_distrib
    (principal_divisor_support k e he T hT h E hh hE f hf).1
    (principal_divisor_support k e he T hT h E hh hE g hg).1
include hT hh hE in
lemma principalDegree_div (he : Function.Injective e) (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDegree k e T E (f/g) = principalDegree k e T E f-principalDegree k e T E g := by
  have hv := principalDegree_mul k e T hT h E hh hE he (f/g) g (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ _ hg] at hv
  omega
lemma vertical_product_ne_zero (s : Multiset k) :
    (s.map fun a => xFunction k e-algebraMap k (FF k e) a).prod ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simpa using mul_ne_zero (x_sub_ne_zero k e a) ih
include hT hh hE in
lemma vertical_product_degree_zero [IsAlgClosed k] (he : Function.Injective e) (s : Multiset k) :
    principalDegree k e T E (s.map fun a => xFunction k e-algebraMap k (FF k e) a).prod = 0 := by
  induction s using Multiset.induction_on with
  | empty => simpa using principalDegree_constant k e T E 1
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [principalDegree_mul k e T hT h E hh hE he _ _
      (x_sub_ne_zero k e a) (vertical_product_ne_zero k e s), ih]
    simpa only [principalDegree, add_zero] using vertical_degree_zero k e T hT h E hh hE he a
include hT hh hE in
lemma xSubfield_degree_zero [IsAlgClosed k] (he : Function.Injective e)
    (a : xSubfield k e) (ha : a ≠ 0) : principalDegree k e T E a = 0 := by
  obtain ⟨c,z,p,hc,heq⟩ := xSubfield_factorization k e a ha
  rw [heq, principalDegree_div k e T hT h E hh hE he _ _
    (mul_ne_zero (by simpa using (algebraMap k (FF k e)).injective.ne hc) (vertical_product_ne_zero k e z))
    (vertical_product_ne_zero k e p), principalDegree_mul k e T hT h E hh hE he _ _
    (by simpa using (algebraMap k (FF k e)).injective.ne hc) (vertical_product_ne_zero k e z),
    principalDegree_constant, vertical_product_degree_zero k e T hT h E hh hE he,
    vertical_product_degree_zero k e T hT h E hh hE he]
  norm_num
include hT hh hE in
lemma principalDegree_curveNegation (he : Function.Injective e) (f : FF k e) :
    principalDegree k e T E (curveNegation k e he f) = principalDegree k e T E f := by
  unfold principalDegree
  simp_rw [pointOrder_curveNegation k e he T hT h E hh hE]
  exact finsum_comp (fun P : (Curve k e).Point => -P) (Function.Involutive.bijective neg_neg)
include hT hh hE in
/-- Every nonzero function on the actual split cubic has divisor of degree zero. -/
theorem principal_degree_zero [IsAlgClosed k] (he : Function.Injective e)
    (f : FF k e) (hf : f ≠ 0) : principalDegree k e T E f = 0 := by
  have hn := xSubfield_degree_zero k e T hT h E hh hE he
    ⟨conjugateProduct k e he f, conjugateProduct_mem k e he f⟩
    (by intro hz; exact conjugateProduct_ne_zero k e he hf (congrArg Subtype.val hz))
  change principalDegree k e T E (f * curveNegation k e he f) = 0 at hn
  rw [principalDegree_mul k e T hT h E hh hE he _ _ hf
    (by simpa using (curveNegation k e he).injective.ne hf),
    principalDegree_curveNegation k e T hT h E hh hE he] at hn
  omega
include hT hh hE in
/-- Signed tame-symbol reciprocity against a nonzero constant. -/
theorem tameProduct_constant [IsAlgClosed k] (he : Function.Injective e)
    (f : FF k e) (hf : f ≠ 0) (c : k) (hc : c ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E f (algebraMap k (FF k e) c) P) = 1 := by
  classical
  have hs := (principal_divisor_support k e he T hT h E hh hE f hf).1
  let S := hs.toFinset
  have ho : (∑ P ∈ S, pointOrder k e T E f P) = 0 := by
    rw [← finsum_eq_sum_of_support_subset]
    · exact principal_degree_zero k e T hT h E hh hE he f hf
    · intro P hP
      exact hs.mem_toFinset.mpr hP
  have hprod (s : Finset (Curve k e).Point) :
      (∏ P ∈ s, c ^ pointOrder k e T E f P) = c ^ (∑ P ∈ s, pointOrder k e T E f P) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert P s hP ih => rw [Finset.prod_insert hP, Finset.sum_insert hP, ih, zpow_add₀ hc]
  have hsupp : Function.mulSupport (fun P => tameSymbol k e T E f (algebraMap k (FF k e) c) P) ⊆ S := by
    intro P hP
    apply hs.mem_toFinset.mpr
    intro hz
    exact hP (tameSymbol_eq_one_of_orders_eq_zero k e T E P _ _ hz
      (pointOrder_constant k e T E P c))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  simp only [tameSymbol, pointOrder_constant, localLeading_constant, mul_zero, zpow_zero,
    one_mul, one_div]
  rw [Finset.prod_inv_distrib, hprod, ho, zpow_zero, inv_one]

end VerticalDivisors

section FactoredExpansions
set_option backward.isDefEq.respectTransparency false
open ArithmeticThetaMillerR0114 WeierstrassCurve.Affine
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)
lemma localLeading_div (P : (Curve k e).Point) (f g : FF k e) (hg : g ≠ 0) :
    localLeading k e T E (f/g) P = localLeading k e T E f P / localLeading k e T E g P := by
  have hv := localLeading_mul k e T E P (f/g) g
  rw [div_mul_cancel₀ _ hg] at hv
  exact (eq_div_iff (localLeading_ne_zero k e T E P hg)).mpr hv.symm
/-- The unit part of a split polynomial at a finite base point. -/
def rootUnitProduct (s : Multiset k) (a : k) : k :=
  (s.map fun z => if z = a then 1 else a-z).prod
lemma rootUnitProduct_ne_zero (s : Multiset k) (a : k) : rootUnitProduct k s a ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [rootUnitProduct]
  | cons z s ih =>
    simp only [rootUnitProduct, Multiset.map_cons, Multiset.prod_cons] at *
    apply mul_ne_zero _ ih
    split_ifs with hz
    · exact one_ne_zero
    · exact sub_ne_zero.mpr (Ne.symm hz)
include hT hh hE in
lemma vertical_product_local (s : Multiset k) (a b : k) (hp : (Curve k e).Nonsingular a b) :
    let P := Point.some a b hp
    let ell := localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) P
    pointOrder k e T E (s.map fun z => xFunction k e-algebraMap k (FF k e) z).prod P =
      (if b = 0 then 2 else 1) * (s.count a : ℤ) ∧
    localLeading k e T E (s.map fun z => xFunction k e-algebraMap k (FF k e) z).prod P =
      ell ^ (s.count a : ℤ) * rootUnitProduct k s a := by
  dsimp only
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.count_zero, Nat.cast_zero, mul_zero,
      zpow_zero, rootUnitProduct, one_mul]
    constructor
    · simpa only [map_one] using pointOrder_constant k e T E (Point.some a b hp) 1
    · simpa only [map_one] using localLeading_constant k e T E (Point.some a b hp) 1
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [pointOrder_mul k e T E _ (x_sub_ne_zero k e z) (vertical_product_ne_zero k e s),
      localLeading_mul, ih.1, ih.2]
    have hell : localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) ≠ 0 :=
      localLeading_ne_zero k e T E _ (x_sub_ne_zero k e a)
    by_cases hz : z = a
    · subst z
      rw [(local_orders k e T hT h E hh hE a b hp).1]
      simp only [Multiset.count_cons_self, Nat.cast_add, Nat.cast_one, rootUnitProduct,
        Multiset.map_cons, Multiset.prod_cons, ite_true, one_mul, zpow_add₀ hell, zpow_one]
      constructor <;> ring
    · rw [(vertical_at_other k e T hT h E hh hE a b z hp (Ne.symm hz)).1,
        (vertical_at_other k e T hT h E hh hE a b z hp (Ne.symm hz)).2]
      simp only [Multiset.count_cons_of_ne (Ne.symm hz), zero_add, rootUnitProduct,
        Multiset.map_cons, Multiset.prod_cons, if_neg hz, true_and]
      ring
include hT hh hE in
lemma factored_local (c : k) (hc : c ≠ 0) (zeros poles : Multiset k)
    (a b : k) (hp : (Curve k e).Nonsingular a b) :
    let F := algebraMap k (FF k e) c *
      (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
      (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod
    let n : ℤ := (zeros.count a : ℤ)-(poles.count a : ℤ)
    let L := c * rootUnitProduct k zeros a / rootUnitProduct k poles a
    let P := Point.some a b hp
    let ell := localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) P
    pointOrder k e T E F P = (if b = 0 then 2 else 1)*n ∧
      localLeading k e T E F P = ell^n * L := by
  dsimp only
  have hc' : algebraMap k (FF k e) c ≠ 0 := by simpa using (algebraMap k (FF k e)).injective.ne hc
  have hz := vertical_product_ne_zero k e zeros
  have hp' := vertical_product_ne_zero k e poles
  have hell : localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) ≠ 0 :=
    localLeading_ne_zero k e T E _ (x_sub_ne_zero k e a)
  obtain ⟨hzo,hzl⟩ := vertical_product_local k e T hT h E hh hE zeros a b hp
  obtain ⟨hpo,hpl⟩ := vertical_product_local k e T hT h E hh hE poles a b hp
  rw [pointOrder_div k e T E _ _ _ (mul_ne_zero hc' hz) hp',
    pointOrder_mul k e T E _ hc' hz, pointOrder_constant,
    localLeading_div k e T E _ _ _ hp', localLeading_mul, localLeading_constant,
    hzo, hzl, hpo, hpl, zpow_sub₀ hell]
  constructor
  · ring
  · simp only [div_eq_mul_inv, mul_inv]
    ring
include hT hh hE in
lemma vertical_product_infinity (s : Multiset k) :
    pointOrder k e T E (s.map fun z => xFunction k e-algebraMap k (FF k e) z).prod 0 =
      -2 * (s.card : ℤ) ∧
    localLeading k e T E (s.map fun z => xFunction k e-algebraMap k (FF k e) z).prod 0 = 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, Nat.cast_zero, mul_zero]
    constructor
    · simpa only [map_one] using pointOrder_constant k e T E 0 1
    · simpa only [map_one] using localLeading_constant k e T E 0 1
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    rw [pointOrder_mul k e T E _ (x_sub_ne_zero k e z) (vertical_product_ne_zero k e s),
      localLeading_mul, ih.1, ih.2, (vertical_at_infinity k e T hT h E hh hE z).1,
      (vertical_at_infinity k e T hT h E hh hE z).2]
    constructor <;> ring
include hT hh hE in
lemma factored_infinity (c : k) (hc : c ≠ 0) (zeros poles : Multiset k) :
    let F := algebraMap k (FF k e) c *
      (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
      (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod
    pointOrder k e T E F 0 = -2 * ((zeros.card : ℤ)-(poles.card : ℤ)) ∧
      localLeading k e T E F 0 = c := by
  dsimp only
  have hc' : algebraMap k (FF k e) c ≠ 0 := by simpa using (algebraMap k (FF k e)).injective.ne hc
  have hz := vertical_product_ne_zero k e zeros
  have hp := vertical_product_ne_zero k e poles
  obtain ⟨hzo,hzl⟩ := vertical_product_infinity k e T hT h E hh hE zeros
  obtain ⟨hpo,hpl⟩ := vertical_product_infinity k e T hT h E hh hE poles
  rw [pointOrder_div k e T E _ _ _ (mul_ne_zero hc' hz) hp,
    pointOrder_mul k e T E _ hc' hz, pointOrder_constant,
    localLeading_div k e T E _ _ _ hp, localLeading_mul, localLeading_constant,
    hzo, hzl, hpo, hpl]
  constructor <;> ring

end FactoredExpansions

section RationalBaseSymbols
set_option backward.isDefEq.respectTransparency false
variable (k : Type u) [Field k] [DecidableEq k]
/-- Rational-line symbol of X-z against X-a, including the point at infinity. -/
def linearBaseSymbol (z a : k) : Option k → k
  | none => -1
  | some x => if x = a then (if z = a then -1 else a-z)
      else if z = x then (x-a)⁻¹ else 1
/-- Rational-line symbol of a constant against X-a. -/
def constantBaseSymbol (c a : k) : Option k → k
  | none => c⁻¹
  | some x => if x = a then c else 1
lemma finite_linearBaseSymbol (z a : k) : Function.HasFiniteMulSupport (linearBaseSymbol k z a) := by
  classical
  apply (Set.toFinite ({none, some a, some z} : Set (Option k))).subset
  intro x hx
  cases x with
  | none => simp
  | some x =>
    by_contra hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq, Option.some_ne_none,
      false_or, not_or] at hn
    apply hx
    simp [linearBaseSymbol, hn.1, Ne.symm hn.2]
lemma finite_constantBaseSymbol (c a : k) : Function.HasFiniteMulSupport (constantBaseSymbol k c a) := by
  classical
  apply (Set.toFinite ({none, some a} : Set (Option k))).subset
  intro x hx
  cases x with
  | none => simp
  | some x =>
    by_contra hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq, Option.some_ne_none,
      false_or] at hn
    exact hx (by simp [constantBaseSymbol, hn])
lemma linearBaseSymbol_product (z a : k) : (∏ᶠ x, linearBaseSymbol k z a x) = 1 := by
  classical
  have hs : Function.mulSupport (linearBaseSymbol k z a) ⊆ ({none, some a, some z} : Finset (Option k)) := by
    intro x hx
    cases x with
    | none => simp
    | some x =>
      by_contra hn
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, Option.some_ne_none,
        false_or, not_or] at hn
      exact hx (by simp [linearBaseSymbol, hn.1, Ne.symm hn.2])
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  by_cases hz : z = a
  · subst z
    simp [linearBaseSymbol]
  · have haz : a-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    simp [linearBaseSymbol, hz, Ne.symm hz]
    field_simp
    ring
lemma constantBaseSymbol_product (c a : k) (hc : c ≠ 0) :
    (∏ᶠ x, constantBaseSymbol k c a x) = 1 := by
  classical
  have hs : Function.mulSupport (constantBaseSymbol k c a) ⊆ ({none, some a} : Finset (Option k)) := by
    intro x hx
    cases x with
    | none => simp
    | some x =>
      by_contra hn
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, Option.some_ne_none,
        false_or] at hn
      exact hx (by simp [constantBaseSymbol, hn])
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  simp [constantBaseSymbol, hc]
/-- Product of the rational-line linear factors, retaining multiplicities. -/
def multisetBaseSymbol (s : Multiset k) (a : k) (x : Option k) : k :=
  (s.map fun z => linearBaseSymbol k z a x).prod
lemma finite_multisetBaseSymbol (s : Multiset k) (a : k) :
    Function.HasFiniteMulSupport (multisetBaseSymbol k s a) := by
  induction s using Multiset.induction_on with
  | empty =>
    change Function.HasFiniteMulSupport (fun _ : Option k => (1 : k))
    exact Function.hasFiniteMulSupport_one
  | cons z s ih =>
    apply ((finite_linearBaseSymbol k z a).union ih).subset
    intro x hx
    by_contra hn
    have hn' := not_or.mp hn
    have h1 : linearBaseSymbol k z a x = 1 := not_ne_iff.mp hn'.1
    have h2 : multisetBaseSymbol k s a x = 1 := not_ne_iff.mp hn'.2
    apply hx
    simpa only [multisetBaseSymbol, Multiset.map_cons, Multiset.prod_cons, h1, one_mul] using h2
lemma multisetBaseSymbol_product (s : Multiset k) (a : k) :
    (∏ᶠ x, multisetBaseSymbol k s a x) = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetBaseSymbol]
  | cons z s ih =>
    have hm := finprod_mul_distrib (finite_linearBaseSymbol k z a) (finite_multisetBaseSymbol k s a)
    rw [linearBaseSymbol_product, ih, mul_one] at hm
    simpa only [multisetBaseSymbol, Multiset.map_cons, Multiset.prod_cons] using hm
def factoredBaseSymbol (c : k) (zeros poles : Multiset k) (a : k) (x : Option k) : k :=
  constantBaseSymbol k c a x * multisetBaseSymbol k zeros a x / multisetBaseSymbol k poles a x
lemma finite_factoredBaseSymbol (c : k) (zeros poles : Multiset k) (a : k) :
    Function.HasFiniteMulSupport (factoredBaseSymbol k c zeros poles a) := by
  exact ((finite_constantBaseSymbol k c a).mul (finite_multisetBaseSymbol k zeros a)).div
    (finite_multisetBaseSymbol k poles a)
lemma factoredBaseSymbol_product (c : k) (hc : c ≠ 0) (zeros poles : Multiset k) (a : k) :
    (∏ᶠ x, factoredBaseSymbol k c zeros poles a x) = 1 := by
  unfold factoredBaseSymbol
  have hd := finprod_div_distrib ((finite_constantBaseSymbol k c a).mul (finite_multisetBaseSymbol k zeros a))
      (finite_multisetBaseSymbol k poles a)
  simp only [Pi.mul_apply] at hd
  rw [hd,
    finprod_mul_distrib (finite_constantBaseSymbol k c a) (finite_multisetBaseSymbol k zeros a),
    constantBaseSymbol_product k c a hc, multisetBaseSymbol_product, multisetBaseSymbol_product]
  simp

end RationalBaseSymbols

section RationalBaseFormulas
set_option backward.isDefEq.respectTransparency false
variable (k : Type u) [Field k] [DecidableEq k]
lemma multisetBaseSymbol_at_root (s : Multiset k) (a : k) :
    multisetBaseSymbol k s a (some a) = (-1 : k)^(s.count a : ℤ) * rootUnitProduct k s a := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetBaseSymbol, rootUnitProduct]
  | cons z s ih =>
    have hcons : multisetBaseSymbol k (z ::ₘ s) a (some a) =
        linearBaseSymbol k z a (some a) * multisetBaseSymbol k s a (some a) := by
      simp only [multisetBaseSymbol, Multiset.map_cons, Multiset.prod_cons]
    rw [hcons, ih]
    by_cases hz : z = a
    · subst z
      simp only [linearBaseSymbol, ite_true, Multiset.count_cons_self, Nat.cast_add,
        Nat.cast_one, zpow_add₀ (show (-1 : k) ≠ 0 from neg_ne_zero.mpr one_ne_zero), zpow_one, rootUnitProduct,
        Multiset.map_cons, Multiset.prod_cons, one_mul]
      ring
    · simp only [linearBaseSymbol, ite_true, if_neg hz, Multiset.count_cons_of_ne (Ne.symm hz),
        rootUnitProduct, Multiset.map_cons, Multiset.prod_cons]
      ring
lemma multisetBaseSymbol_at_other (s : Multiset k) (a x : k) (hx : x ≠ a) :
    multisetBaseSymbol k s a (some x) = (x-a)^(-(s.count x : ℤ)) := by
  have hxa : x-a ≠ 0 := sub_ne_zero.mpr hx
  induction s using Multiset.induction_on with
  | empty => simp [multisetBaseSymbol]
  | cons z s ih =>
    have hcons : multisetBaseSymbol k (z ::ₘ s) a (some x) =
        linearBaseSymbol k z a (some x) * multisetBaseSymbol k s a (some x) := by
      simp only [multisetBaseSymbol, Multiset.map_cons, Multiset.prod_cons]
    rw [hcons, ih]
    by_cases hz : z = x
    · subst z
      simp only [linearBaseSymbol, if_neg hx, ite_true, Multiset.count_cons_self, Nat.cast_add,
        Nat.cast_one, neg_add, zpow_add₀ hxa, neg_neg, zpow_neg_one]
      ring
    · simp [linearBaseSymbol, hx, hz, Multiset.count_cons_of_ne (Ne.symm hz)]
lemma multisetBaseSymbol_at_infinity (s : Multiset k) (a : k) :
    multisetBaseSymbol k s a none = (-1 : k)^(s.card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetBaseSymbol]
  | cons z s ih =>
    have hcons : multisetBaseSymbol k (z ::ₘ s) a none =
        linearBaseSymbol k z a none * multisetBaseSymbol k s a none := by
      simp only [multisetBaseSymbol, Multiset.map_cons, Multiset.prod_cons]
    rw [hcons, ih]
    simp only [linearBaseSymbol, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
      zpow_add₀ (show (-1 : k) ≠ 0 from neg_ne_zero.mpr one_ne_zero), zpow_one]
    ring
lemma factoredBaseSymbol_at_root (c : k) (zeros poles : Multiset k) (a : k) :
    factoredBaseSymbol k c zeros poles a (some a) =
      (-1 : k)^((zeros.count a : ℤ)-(poles.count a : ℤ)) *
      (c * rootUnitProduct k zeros a / rootUnitProduct k poles a) := by
  rw [factoredBaseSymbol, multisetBaseSymbol_at_root, multisetBaseSymbol_at_root,
    zpow_sub₀ (neg_ne_zero.mpr one_ne_zero)]
  simp only [constantBaseSymbol, ite_true, div_eq_mul_inv, mul_inv]
  ring
lemma factoredBaseSymbol_at_other (c : k) (zeros poles : Multiset k) (a x : k) (hx : x ≠ a) :
    factoredBaseSymbol k c zeros poles a (some x) =
      (x-a)^(-((zeros.count x : ℤ)-(poles.count x : ℤ))) := by
  rw [factoredBaseSymbol, multisetBaseSymbol_at_other k zeros a x hx,
    multisetBaseSymbol_at_other k poles a x hx, constantBaseSymbol, if_neg hx, one_mul,
    neg_sub, zpow_sub₀ (sub_ne_zero.mpr hx)]
  simp [zpow_neg, div_eq_mul_inv, mul_comm]
lemma factoredBaseSymbol_at_infinity (c : k) (zeros poles : Multiset k) (a : k) :
    factoredBaseSymbol k c zeros poles a none =
      (-1 : k)^((zeros.card : ℤ)-(poles.card : ℤ)) / c := by
  rw [factoredBaseSymbol, multisetBaseSymbol_at_infinity, multisetBaseSymbol_at_infinity,
    zpow_sub₀ (neg_ne_zero.mpr one_ne_zero)]
  simp only [constantBaseSymbol, div_eq_mul_inv]
  ring
end RationalBaseFormulas


section FiberAlgebra
variable {k : Type u} [Field k]
lemma sign_mul_self (n : ℤ) : (-1 : k)^n * (-1 : k)^n = 1 := by
  rw [← zpow_add₀ (show (-1 : k) ≠ 0 from neg_ne_zero.mpr one_ne_zero)]
  exact (show Even (n+n) from ⟨n, rfl⟩).neg_one_zpow
lemma sign_even_product (n : ℤ) : (-1 : k)^(n*2) = 1 := by
  exact (show Even (n*2) from ⟨n, by ring⟩).neg_one_zpow
lemma fiber_algebra_unramified (n m : ℤ) (L M ell A : k) (hell : ell ≠ 0)
    (hN : (-1 : k)^m * L * M = ell^(n+m)*A) :
    ((-1 : k)^n * L / ell^n) * ((-1 : k)^m * M / (-ell)^m) =
      (-1 : k)^(n+m)*A := by
  have hs : (-1 : k)^m ≠ 0 := zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hn : ell^(n+m) ≠ 0 := zpow_ne_zero _ hell
  have hA : A = (-1 : k)^m * L * M / ell^(n+m) := (eq_div_iff hn).mpr (by simpa [mul_comm] using hN.symm)
  rw [hA, show -ell = (-1 : k)*ell by ring, mul_zpow,
    zpow_add₀ (show (-1 : k) ≠ 0 from neg_ne_zero.mpr one_ne_zero), zpow_add₀ hell]
  field_simp
  have hsign : ((-1 : k)^m)^2 = 1 := by simpa [pow_two] using sign_mul_self (k := k) m
  ring_nf
  simp [hsign]

lemma fiber_algebra_ramified (n : ℤ) (L ell A : k) (hell : ell ≠ 0)
    (hN : (-1 : k)^n * L * L = ell^n*A) :
    (-1 : k)^(n*2) * L^(2 : ℤ) / ell^n = (-1 : k)^n*A := by
  have hA : A = (-1 : k)^n * L * L / ell^n :=
    (eq_div_iff (zpow_ne_zero _ hell)).mpr (by simpa [mul_comm] using hN.symm)
  rw [hA, sign_even_product, one_mul, zpow_ofNat]
  field_simp
  have hsign : ((-1 : k)^n)^2 = 1 := by simpa [pow_two] using sign_mul_self (k := k) n
  rw [hsign, mul_one]
end FiberAlgebra

section VerticalReciprocity
set_option backward.isDefEq.respectTransparency false
open ArithmeticThetaMillerR0114 WeierstrassCurve.Affine
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)

def pointX : (Curve k e).Point → Option k
  | .zero => none
  | .some x _ _ => some x

lemma pointX_fiber (a b : k) (hp : (Curve k e).Nonsingular a b) (P : (Curve k e).Point) :
    pointX k e P = some a ↔ P = Point.some a b hp ∨ P = -Point.some a b hp := by
  cases P with
  | zero => simp [pointX]
  | some x y hxy =>
    rw [affine_neg]
    simp only [pointX, Option.some.injEq, Point.some.injEq]
    constructor
    · intro hx
      subst x
      have hy : y^2 = b^2 := by
        have h1 := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a y).mp hxy.1
        have h2 := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a b).mp hp.1
        exact h1.trans h2.symm
      rcases eq_or_eq_neg_of_sq_eq_sq y b hy with hy | hy <;> simp [hy]
    · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx

lemma pointX_none (P : (Curve k e).Point) : pointX k e P = none ↔ P = 0 := by
  cases P <;> simp [pointX, show (Point.zero : (Curve k e).Point) = 0 from rfl]

lemma point_eq_neg_iff (a b : k) (hp : (Curve k e).Nonsingular a b) :
    Point.some a b hp = -Point.some a b hp ↔ b = 0 := by
  rw [affine_neg, Point.some.injEq]
  constructor
  · rintro ⟨_,hb⟩
    linear_combination (1/2 : k)*hb
  · intro hb; simp [hb]

lemma finprod_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (π : α → β) (F : α → k) (hf : Function.HasFiniteMulSupport F) :
    (∏ᶠ P, F P) = ∏ᶠ x, ∏ᶠ P, if π P = x then F P else 1 := by
  classical
  let S := hf.toFinset
  have hs : Function.mulSupport F ⊆ S := fun P hP => hf.mem_toFinset.mpr hP
  rw [finprod_eq_prod_of_mulSupport_subset F hs, ← finprod_prod_filter π S F]
  apply finprod_congr
  intro x
  have hx : Function.mulSupport (fun P => if π P = x then F P else 1) ⊆ S := by
    intro P hP
    by_cases hp : π P = x
    · exact hs (by simpa [hp] using hP)
    · simp [hp] at hP
  rw [finprod_eq_prod_of_mulSupport_subset _ hx, Finset.prod_filter]

include he hT hh hE in
lemma norm_factored_data (f : FF k e) (hf : f ≠ 0) [IsAlgClosed k] :
    ∃ (c : k) (zeros poles : Multiset k), c ≠ 0 ∧
      conjugateProduct k e he f = algebraMap k (FF k e) c *
        (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
        (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod := by
  exact xSubfield_factorization k e
    ⟨conjugateProduct k e he f, conjugateProduct_mem k e he f⟩
    (by intro hz; exact conjugateProduct_ne_zero k e he hf (congrArg Subtype.val hz))

lemma sign_double (n : ℤ) : (-1 : k)^(2*n) = 1 :=
  (even_two_mul n).neg_one_zpow

include he hT hh hE in
lemma vertical_norm_at_infinity (f : FF k e) (hf : f ≠ 0)
    (c : k) (hc : c ≠ 0) (zeros poles : Multiset k)
    (hN : conjugateProduct k e he f = algebraMap k (FF k e) c *
      (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
      (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod) (a : k) :
    tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) 0 =
      factoredBaseSymbol k c zeros poles a none := by
  have hnorm := factored_infinity k e T hT h E hh hE c hc zeros poles
  dsimp only at hnorm
  rw [← hN, conjugateProduct_order k e he T hT h E hh hE _ _ hf,
    conjugateProduct_leading k e he T hT h E hh hE, neg_zero] at hnorm
  have ho : pointOrder k e T E f 0 = -((zeros.card : ℤ)-(poles.card : ℤ)) := by
    omega
  have hL : (-1 : k)^pointOrder k e T E f 0 * (localLeading k e T E f 0)^2 = c := by
    simpa only [neg_zero, pow_two, mul_assoc] using hnorm.2
  rw [factoredBaseSymbol_at_infinity]
  unfold tameSymbol
  rw [(vertical_at_infinity k e T hT h E hh hE a).1,
    (vertical_at_infinity k e T hT h E hh hE a).2]
  have hs : (-1 : k) ^ (pointOrder k e T E f 0 * -2) = 1 := by
    rw [show pointOrder k e T E f 0 * -2 = 2 * (-pointOrder k e T E f 0) by ring, sign_double]
  rw [hs, one_mul, one_zpow, div_one]
  have hd : (zeros.card : ℤ)-(poles.card : ℤ) = -pointOrder k e T E f 0 := by omega
  rw [← hL, hd]
  simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_inv, ← inv_zpow, inv_neg, inv_one]
  rw [← mul_assoc, sign_mul_self, one_mul]

include he hT hh hE in
lemma vertical_norm_at_other (f : FF k e) (hf : f ≠ 0)
    (c : k) (hc : c ≠ 0) (zeros poles : Multiset k)
    (hN : conjugateProduct k e he f = algebraMap k (FF k e) c *
      (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
      (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod)
    (a x y : k) (hp : (Curve k e).Nonsingular x y) (hxa : x ≠ a) :
    (if y = 0 then tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (.some x y hp)
      else tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (.some x y hp) *
        tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (-Point.some x y hp)) =
      factoredBaseSymbol k c zeros poles a (some x) := by
  have hnorm := (factored_local k e T hT h E hh hE c hc zeros poles x y hp).1
  rw [← hN, conjugateProduct_order k e he T hT h E hh hE _ _ hf] at hnorm
  have ht (y : k) (hp : (Curve k e).Nonsingular x y) :
      tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (.some x y hp) =
        (x-a)^(-pointOrder k e T E f (.some x y hp)) := by
    unfold tameSymbol
    rw [(vertical_at_other k e T hT h E hh hE x y a hp hxa).1,
      (vertical_at_other k e T hT h E hh hE x y a hp hxa).2]
    simp [zpow_neg]
  rw [factoredBaseSymbol_at_other k c zeros poles a x hxa]
  by_cases hy : y = 0
  · have hpneg : -Point.some x y hp = Point.some x y hp :=
      ((point_eq_neg_iff k e x y hp).mpr hy).symm
    rw [if_pos hy, hpneg] at hnorm
    rw [if_pos hy]
    have ho : pointOrder k e T E f (.some x y hp) =
        (zeros.count x : ℤ)-(poles.count x : ℤ) := by omega
    rw [ht, ho]
  · simp only [hy, ite_false, one_mul] at hnorm ⊢
    rw [ht, affine_neg, ht, ← zpow_add₀ (sub_ne_zero.mpr hxa), ← (affine_neg k e x y hp),
      ← neg_add, hnorm]

include he hT hh hE in
lemma vertical_norm_at_root (f : FF k e) (hf : f ≠ 0)
    (c : k) (hc : c ≠ 0) (zeros poles : Multiset k)
    (hN : conjugateProduct k e he f = algebraMap k (FF k e) c *
      (zeros.map fun z => xFunction k e-algebraMap k (FF k e) z).prod /
      (poles.map fun z => xFunction k e-algebraMap k (FF k e) z).prod)
    (a b : k) (hp : (Curve k e).Nonsingular a b) :
    (if b = 0 then tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (.some a b hp)
      else tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) *
        tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) (-Point.some a b hp)) =
      factoredBaseSymbol k c zeros poles a (some a) := by
  have hnorm := factored_local k e T hT h E hh hE c hc zeros poles a b hp
  dsimp only at hnorm
  rw [← hN, conjugateProduct_order k e he T hT h E hh hE _ _ hf,
    conjugateProduct_leading k e he T hT h E hh hE] at hnorm
  have hell : localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) ≠ 0 :=
    localLeading_ne_zero k e T E _ (x_sub_ne_zero k e a)
  rw [factoredBaseSymbol_at_root]
  by_cases hb : b = 0
  · have hneg : -Point.some a b hp = Point.some a b hp :=
      ((point_eq_neg_iff k e a b hp).mpr hb).symm
    rw [if_pos hb, hneg] at hnorm
    rw [if_pos hb]
    have hn : (zeros.count a : ℤ)-(poles.count a : ℤ) =
        pointOrder k e T E f (.some a b hp) := by omega
    rw [hn] at hnorm ⊢
    unfold tameSymbol
    rw [(local_orders k e T hT h E hh hE a b hp).1, if_pos hb]
    exact fiber_algebra_ramified _ _ _ _ hell hnorm.2
  · rw [if_neg hb, one_mul] at hnorm
    rw [if_neg hb]
    have hn : (zeros.count a : ℤ)-(poles.count a : ℤ) =
        pointOrder k e T E f (.some a b hp) + pointOrder k e T E f (-Point.some a b hp) := hnorm.1.symm
    rw [hn] at hnorm ⊢
    have hoM : pointOrder k e T E (xFunction k e-algebraMap k (FF k e) a) (-Point.some a b hp) = 1 := by
      rw [affine_neg]
      simpa [neg_ne_zero.mpr hb] using (local_orders k e T hT h E hh hE a (-b) _).1
    have hLM : localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (-Point.some a b hp) =
        -localLeading k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) := by
      rw [affine_neg, vertical_leading_unramified k e T hT h E hh hE a (-b) _ (neg_ne_zero.mpr hb),
        vertical_leading_unramified k e T hT h E hh hE a b hp hb]
      ring
    unfold tameSymbol
    rw [(local_orders k e T hT h E hh hE a b hp).1, if_neg hb, hoM, hLM]
    simp only [mul_one, zpow_one]
    exact fiber_algebra_unramified _ _ _ _ _ _ hell hnorm.2

lemma fiber_product_some (F : (Curve k e).Point → k)
    (x y : k) (hp : (Curve k e).Nonsingular x y) :
    (∏ᶠ P, if pointX k e P = some x then F P else 1) =
      if y = 0 then F (.some x y hp) else F (.some x y hp)*F (-Point.some x y hp) := by
  classical
  simp_rw [pointX_fiber k e x y hp]
  have hs : Function.mulSupport (fun P =>
      if P = Point.some x y hp ∨ P = -Point.some x y hp then F P else 1) ⊆
      ({Point.some x y hp, -Point.some x y hp} : Finset (Curve k e).Point) := by
    intro P hP
    by_contra hn
    have hn' : ¬ (P = Point.some x y hp ∨ P = -Point.some x y hp) := by simpa using hn
    simpa only [Function.mem_mulSupport, if_neg hn', ne_self_iff_false] using hP
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  by_cases hy : y = 0
  · have hneg : -Point.some x y hp = Point.some x y hp :=
      ((point_eq_neg_iff k e x y hp).mpr hy).symm
    rw [if_pos hy, hneg]
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
      Finset.prod_singleton, eq_self_iff_true, or_self, if_true]
  · have hneg : Point.some x y hp ≠ -Point.some x y hp :=
      mt (point_eq_neg_iff k e x y hp).mp hy
    rw [if_neg hy, Finset.prod_insert (by simpa only [Finset.mem_singleton] using hneg),
      Finset.prod_singleton]
    simp only [eq_self_iff_true, true_or, or_true, if_true]

lemma fiber_product_none (F : (Curve k e).Point → k) :
    (∏ᶠ P, if pointX k e P = none then F P else 1) = F 0 := by
  simp_rw [pointX_none]
  rw [finprod_eq_single _ 0 (by intro P hP; simp [hP])]
  simp

include he hT hh hE in
theorem tameProduct_vertical [IsAlgClosed k] (f : FF k e) (hf : f ≠ 0) (a : k) :
    (∏ᶠ P, tameSymbol k e T E f (xFunction k e-algebraMap k (FF k e) a) P) = 1 := by
  classical
  obtain ⟨c,zeros,poles,hc,hN⟩ := norm_factored_data k e he T hT h E hh hE f hf
  rw [finprod_fibers k (pointX k e) _
    (finite_tameSymbol_support k e he T hT h E hh hE f _ hf (x_sub_ne_zero k e a))]
  calc
    _ = ∏ᶠ x, factoredBaseSymbol k c zeros poles a x := by
      apply finprod_congr
      intro x
      cases x with
      | none =>
        rw [fiber_product_none]
        exact vertical_norm_at_infinity k e he T hT h E hh hE f hf c hc zeros poles hN a
      | some x =>
        obtain ⟨y,hp⟩ := exists_point_over k e he x
        rw [fiber_product_some k e _ x y hp]
        by_cases hx : x = a
        · subst x
          exact vertical_norm_at_root k e he T hT h E hh hE f hf c hc zeros poles hN a y hp
        · exact vertical_norm_at_other k e he T hT h E hh hE f hf c hc zeros poles hN a x y hp hx
    _ = 1 := factoredBaseSymbol_product k c hc zeros poles a

end VerticalReciprocity

section GlobalReciprocity
set_option backward.isDefEq.respectTransparency false
open ArithmeticThetaMillerR0114
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)

include he hT hh hE in
lemma tameProduct_div_right {f g₁ g₂ : FF k e}
    (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E f (g₁/g₂) P) =
      (∏ᶠ P, tameSymbol k e T E f g₁ P) / (∏ᶠ P, tameSymbol k e T E f g₂ P) := by
  simp_rw [tameSymbol_div_right k e T E _ hf hg₁ hg₂]
  exact finprod_div_distrib
    (finite_tameSymbol_support k e he T hT h E hh hE f g₁ hf hg₁)
    (finite_tameSymbol_support k e he T hT h E hh hE f g₂ hf hg₂)

include he hT hh hE in
lemma tameProduct_vertical_multiset [IsAlgClosed k] (f : FF k e) (hf : f ≠ 0)
    (s : Multiset k) :
    (∏ᶠ P, tameSymbol k e T E f
      (s.map fun z => xFunction k e-algebraMap k (FF k e) z).prod P) = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, tameSymbol_one_right, finprod_one]
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [tameProduct_mul_right k e he T hT h E hh hE hf (x_sub_ne_zero k e z)
      (vertical_product_ne_zero k e s), tameProduct_vertical k e he T hT h E hh hE f hf z,
      ih, mul_one]

include he hT hh hE in
theorem tameProduct_xSubfield [IsAlgClosed k] (f : FF k e) (hf : f ≠ 0)
    (a : xSubfield k e) (ha : a ≠ 0) :
    (∏ᶠ P, tameSymbol k e T E f (a : FF k e) P) = 1 := by
  obtain ⟨c,zeros,poles,hc,hfactor⟩ := xSubfield_factorization k e a ha
  have hc' : algebraMap k (FF k e) c ≠ 0 := by
    simpa only [map_zero] using (algebraMap k (FF k e)).injective.ne hc
  rw [hfactor, tameProduct_div_right k e he T hT h E hh hE hf
    (mul_ne_zero hc' (vertical_product_ne_zero k e zeros)) (vertical_product_ne_zero k e poles),
    tameProduct_mul_right k e he T hT h E hh hE hf hc' (vertical_product_ne_zero k e zeros),
    tameProduct_constant k e T hT h E hh hE he f hf c hc,
    tameProduct_vertical_multiset k e he T hT h E hh hE f hf zeros,
    tameProduct_vertical_multiset k e he T hT h E hh hE f hf poles]
  simp

/-- General signed tame-symbol reciprocity on the actual smooth split cubic. -/
theorem elliptic_tame_reciprocity
    (k : Type u) [Field k] [CharZero k] [DecidableEq k] [IsAlgClosed k]
    (e : Fin 3 → k) (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : branchEquation k e h) (hE : IsInfinityEmbedding k e h E)
    (f g : FF k e) (hf : f ≠ 0) (hg : g ≠ 0) :
    Set.Finite {P : (Curve k e).Point | tameSymbol k e T E f g P ≠ 1} ∧
      (∏ᶠ P : (Curve k e).Point, tameSymbol k e T E f g P) = 1 := by
  refine ⟨finite_tameSymbol_support k e he T hT h E hh hE f g hf hg, ?_⟩
  obtain ⟨pairs,hn,hprod⟩ := tameProduct_quadratic_reduction k e he T hT h E hh hE f g hf hg
  rw [hprod]
  have hones : pairs.map (fun z => ∏ᶠ P : (Curve k e).Point,
      tameSymbol k e T E z.1 (z.2 : FF k e) P) = pairs.map (fun _ => (1 : k)) := by
    apply List.map_congr_left
    intro z hz
    exact tameProduct_xSubfield k e he T hT h E hh hE z.1 (hn z hz).1 z.2 (hn z hz).2
  rw [hones]
  simp

end GlobalReciprocity

end ArithmeticThetaReciprocityR0116
