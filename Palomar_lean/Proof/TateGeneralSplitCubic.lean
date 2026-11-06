module

public import TateCoeffYTerm
public import TateCoeffXTerm
public import TateSeriesStabilization
public import Definitions.Def_LaurentSeries_XAdic
public import Theorems.Thm_TateCurve_equation_pointX_pointY
public import TateLegacySeriesStabilization

@[expose] public section

/-! The literal annular split cubic.
The proof identifies stabilized coefficientwise sums with analytic Tate
coordinates in the complete Laurent-series field, then splits the normalized
cubic at three directly verified and pairwise distinct derivative zeros. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaTateIdentities
open ArithmeticThetaTateSeries
open scoped BigOperators

variable {k : Type u} [Field k]

theorem tateY_boundary_neg_one (d : ℕ) : tateY d 0 (-1 : k) = 0 := by
  apply PowerSeries.ext
  intro n
  simp [tateY, partialY, monomial, yTerm]

private lemma midpoint_tail (m N : ℕ) (a : k) (ha : a⁻¹ = a) :
    yTerm (monomial a m) +
      ∑ j ∈ Finset.range N,
        (yTerm (monomial a (2*m*(j+1)+m)) -
          yTerm (monomial a⁻¹ (2*m*(j+1)-m))) =
      yTerm (monomial a (2*m*N+m)) := by
  rw [ha]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hsub : 2*m*(N+1)-m = 2*m*N+m := by
      have h : 2*m*(N+1) = (2*m*N+m)+m := by ring
      omega
    rw [hsub]
    have hadd : yTerm (monomial a m) +
        (∑ j ∈ Finset.range N,
          (yTerm (monomial a (2*m*(j+1)+m)) -
            yTerm (monomial a (2*m*(j+1)-m)))) =
        yTerm (monomial a (2*m*N+m)) := ih
    linear_combination hadd

theorem tateY_midpoint (m : ℕ) (hm : 0 < m) (a : k) (ha : a⁻¹ = a) :
    tateY (2*m) m a = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [tateY, PowerSeries.coeff_mk, partialY]
  rw [midpoint_tail m (n+1) a ha, PowerSeries.coeff_C_mul]
  have hdeg : n < 2*m*(n+1)+m := by nlinarith
  rw [ArithmeticThetaTateBridges.y_term_coeff a _ n (by omega)]
  by_cases hdiv : 2*m*(n+1)+m ∣ n
  · have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hdeg
    simp [hn]
  · simp [hdiv]

theorem tateY_midpoint_one (m : ℕ) (hm : 0 < m) :
    tateY (2*m) m (1 : k) = 0 :=
  tateY_midpoint m hm 1 (by simp)

theorem tateY_midpoint_neg_one (m : ℕ) (hm : 0 < m) :
    tateY (2*m) m (-1 : k) = 0 :=
  tateY_midpoint m hm (-1) (by simp)

private lemma coeff_xTerm_lt (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (xTerm (monomial a r)) = 0 := by
  rw [ArithmeticThetaTateBridges.x_term_coeff a r n (by omega)]
  by_cases hd : r ∣ n
  · have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt hd h
    simp [hn]
  · simp [hd]

private lemma coeff_yTerm_lt (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (yTerm (monomial a r)) = 0 := by
  rw [ArithmeticThetaTateBridges.y_term_coeff a r n (by omega)]
  by_cases hd : r ∣ n
  · have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt hd h
    simp [hn]
  · simp [hd]

private lemma coeff_corr_lt (c : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (PowerSeries.C c * monomial 1 r *
      (1 - monomial 1 r)⁻¹) = 0 := by
  simp only [monomial, map_one, one_mul]
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le_of_lt h]

theorem tateX_interior_constant (d i : ℕ) (a : k) (hi : 0 < i) (hid : i < d) :
    PowerSeries.coeff 0 (tateX d i a) = 0 := by
  simp only [tateX, PowerSeries.coeff_mk, partialX,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
    Nat.zero_add, Nat.mul_one, Nat.sub_zero]
  rw [map_sub, map_add, map_add, coeff_xTerm_lt a hi,
    coeff_xTerm_lt a (by omega), coeff_xTerm_lt a⁻¹ (by omega)]
  simp [monomial, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_inv, (show d ≠ 0 by omega)]

theorem tateX_boundary_constant (d : ℕ) (hd : 0 < d) (a : k) :
    PowerSeries.coeff 0 (tateX d 0 a) = a * ((1-a)⁻¹)^2 := by
  simp only [tateX, PowerSeries.coeff_mk, partialX,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
    Nat.zero_add, Nat.mul_one, Nat.sub_zero]
  rw [map_sub, map_add, map_add, coeff_xTerm_lt a hd, coeff_xTerm_lt a⁻¹ hd]
  simp [xTerm, monomial, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_inv, hd.ne']

theorem tateX_midpoint_leading (m : ℕ) (hm : 0 < m) (a : k) :
    PowerSeries.coeff m (tateX (2*m) m a) = a + a⁻¹ := by
  have hbase (b : k) : PowerSeries.coeff m (xTerm (monomial b m)) = b := by
    rw [ArithmeticThetaTateBridges.x_term_coeff b m m hm]
    simp [Nat.div_self hm]
  have htail : PowerSeries.coeff m
      (∑ j ∈ Finset.range (m+1),
        (xTerm (monomial a (2*m*(j+1)+m)) +
         xTerm (monomial a⁻¹ (2*m*(j+1)-m)))) = a⁻¹ := by
    rw [map_sum]
    have hsub : 2*m*(0+1)-m = m := by omega
    rw [Finset.sum_eq_single 0]
    · rw [map_add, coeff_xTerm_lt a (by nlinarith), hsub, hbase, zero_add]
    · intro j hj hj0
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [map_add, coeff_xTerm_lt a (by nlinarith),
        coeff_xTerm_lt a⁻¹ (by
          have : m+m < 2*m*(j+1) := by nlinarith
          omega), add_zero]
    · simp
  have hcorr : PowerSeries.coeff m
      (∑ j ∈ Finset.range (m+1),
        PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (2*m*(j+1)) *
          (1-monomial 1 (2*m*(j+1)))⁻¹) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact coeff_corr_lt _ (by nlinarith)
  simp only [tateX, PowerSeries.coeff_mk, partialX]
  rw [map_sub, map_add, hbase, htail]
  rw [two_mul, map_add, hcorr]
  simp

theorem general_two_torsion_distinct [CharZero k] (m : ℕ) (hm : 0 < m) :
    tateX (2*m) 0 (-1 : k) ≠ tateX (2*m) m (1 : k) ∧
    tateX (2*m) 0 (-1 : k) ≠ tateX (2*m) m (-1 : k) ∧
    tateX (2*m) m (1 : k) ≠ tateX (2*m) m (-1 : k) := by
  have h1 := tateX_boundary_constant (k := k) (2*m) (by omega) (-1)
  have h2 := tateX_interior_constant (k := k) (2*m) m 1 hm (by omega)
  have h3 := tateX_interior_constant (k := k) (2*m) m (-1) hm (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (PowerSeries.coeff 0) h
    rw [h1, h2] at hc
    norm_num at hc
  · intro h
    have hc := congrArg (PowerSeries.coeff 0) h
    rw [h1, h3] at hc
    norm_num at hc
  · intro h
    have hc := congrArg (PowerSeries.coeff m) h
    rw [tateX_midpoint_leading m hm, tateX_midpoint_leading m hm] at hc
    norm_num at hc


open Filter Topology
open scoped LaurentSeries.XAdic

local instance [CharZero k] : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k

/-- Stable coefficients give convergence in the actual Laurent-series field. -/
theorem toLaurent_tendsto_of_stable (F : ℕ → PowerSeries k) (f : PowerSeries k)
    (h : ∀ n N : ℕ, n+1 ≤ N → PowerSeries.coeff n (F N) = PowerSeries.coeff n f) :
    Tendsto (fun N => toLaurent k (F N)) atTop (𝓝 (toLaurent k f)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  rw [(Valued.hasBasis_nhds_zero (LaurentSeries k)
    (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  let e := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  let D : ℤ := -(WithZero.log e - 1)
  have he : e ≠ 0 := by simp [e]
  have hD : WithZero.exp (-D) < e := by
    rw [← WithZero.lt_log_iff_exp_lt he]
    dsimp [D]
    omega
  filter_upwards [eventually_ge_atTop (D.toNat + 1)] with N hN
  change Valued.v.restrict (toLaurent k (F N) - toLaurent k f) < γ.val
  rw [Valued.v.restrict_lt_iff_lt_embedding]
  apply lt_of_le_of_lt ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mpr ?_) hD
  intro n hn
  rw [← map_sub]
  change (↑(F N-f) : LaurentSeries k).coeff n = 0
  rw [PowerSeries.coeff_coe]
  split_ifs with hn0
  · rfl
  · rw [map_sub, h n.natAbs N (by omega), sub_self]

 theorem partialX_tendsto [CharZero k] (d i : ℕ) (a : k) (ha : Admissible d i a) :
    Tendsto (fun N => toLaurent k (partialX d i a N)) atTop
      (𝓝 (toLaurent k (tateX d i a))) := by
  apply toLaurent_tendsto_of_stable
  intro n N hN
  simpa only [tateX, PowerSeries.coeff_mk] using (annular_stabilization d i a ha n N hN).1

 theorem partialY_tendsto [CharZero k] (d i : ℕ) (a : k) (ha : Admissible d i a) :
    Tendsto (fun N => toLaurent k (partialY d i a N)) atTop
      (𝓝 (toLaurent k (tateY d i a))) := by
  apply toLaurent_tendsto_of_stable
  intro n N hN
  simpa only [tateY, PowerSeries.coeff_mk] using (annular_stabilization d i a ha n N hN).2

private theorem toLaurent_inv (f : PowerSeries k)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    toLaurent k f⁻¹ = (toLaurent k f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, PowerSeries.inv_mul_cancel f hf, map_one]

private theorem monomial_denominator (a : k) (r : ℕ) (ha : r = 0 → a ≠ 1) :
    PowerSeries.constantCoeff (1 - monomial a r) ≠ 0 := by
  by_cases hr : r = 0
  · subst r
    simpa [monomial, sub_ne_zero] using (ha rfl).symm
  · simp [monomial, hr]

private theorem toLaurent_monomial (a : k) (r : ℕ) :
    toLaurent k (monomial a r) = HahnSeries.single (r : ℤ) a := by
  simp only [toLaurent, monomial, map_mul, map_pow, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X, HahnSeries.C_apply, HahnSeries.single_pow,
    HahnSeries.single_mul_single, one_pow, zero_add, nsmul_eq_mul, mul_one]

private theorem laurent_monomial_ne_zero (a : k) (r : ℕ) (ha : a ≠ 0) :
    toLaurent k (monomial a r) ≠ 0 := by
  rw [toLaurent_monomial]
  simpa using ha

private theorem laurent_monomial_ne_one (a : k) (r : ℕ)
    (ha : r = 0 → a ≠ 1) : toLaurent k (monomial a r) ≠ 1 := by
  intro h
  have h' := congrArg (fun f : LaurentSeries k => f.coeff 0) h
  rw [toLaurent_monomial] at h'
  by_cases hr : r = 0
  · subst r
    simp at h'
    exact ha rfl h'
  · simp [HahnSeries.coeff_single, eq_comm, hr] at h'

private theorem toLaurent_xTerm (a : k) (r : ℕ) (ha : r = 0 → a ≠ 1) :
    toLaurent k (xTerm (monomial a r)) =
      TateCurve.xfun (toLaurent k (monomial a r)) := by
  simp only [xTerm, map_mul, map_pow, toLaurent_inv _ (monomial_denominator a r ha),
    map_sub, map_one, TateCurve.xfun, div_eq_mul_inv, inv_pow]

private theorem toLaurent_yTerm (a : k) (r : ℕ) (ha : r = 0 → a ≠ 1) :
    toLaurent k (yTerm (monomial a r)) =
      2 * TateCurve.yfun (toLaurent k (monomial a r)) +
        TateCurve.xfun (toLaurent k (monomial a r)) := by
  have hd := sub_ne_zero.mpr (laurent_monomial_ne_one a r ha).symm
  simp only [yTerm, map_mul, map_pow, map_add, map_one,
    toLaurent_inv _ (monomial_denominator a r ha), map_sub,
    TateCurve.xfun, TateCurve.yfun]
  field_simp
  <;> ring

private theorem annular_positive (d i j : ℕ) (a : k) :
    (toLaurent k (monomial 1 d)) ^ (j+1) * toLaurent k (monomial a i) =
      toLaurent k (monomial a (d*(j+1)+i)) := by
  simp only [toLaurent_monomial, HahnSeries.single_pow, one_pow,
    HahnSeries.single_mul_single, one_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one]
  congr 1
  ring

private theorem annular_negative (d i j : ℕ) (a : k) (hi : i < d) :
    (toLaurent k (monomial 1 d)) ^ (-((j : ℤ)+1)) * toLaurent k (monomial a i) =
      (toLaurent k (monomial a⁻¹ (d*(j+1)-i)))⁻¹ := by
  have hib : i ≤ d*(j+1) := by nlinarith
  rw [show (j : ℤ)+1 = ((j+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  simp only [toLaurent_monomial,
    HahnSeries.single_pow, one_pow, HahnSeries.inv_single, inv_one, inv_inv,
    HahnSeries.single_mul_single, one_mul, nsmul_eq_mul, Nat.cast_sub hib,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private theorem annular_parameter (d i : ℕ) (a : k) (ha : Admissible d i a) :
    ∀ n : ℤ, (toLaurent k (monomial 1 d)) ^ n * toLaurent k (monomial a i) ≠ 1 := by
  intro n
  cases n with
  | ofNat n =>
    cases n with
    | zero => simpa using laurent_monomial_ne_one a i ha.2.2.2
    | succ j =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, annular_positive]
      apply laurent_monomial_ne_one
      intro h
      have := ha.1
      have : 0 < d*(j+1)+i := by positivity
      omega
  | negSucc j =>
    rw [Int.negSucc_eq, annular_negative d i j a ha.2.1]
    apply inv_ne_one.mpr
    apply laurent_monomial_ne_one
    intro h
    have := ha.2.1
    have : i < d*(j+1) := by nlinarith
    omega

private theorem symmetric_sum_tendsto (f : ℤ → LaurentSeries k) (hf : Summable f) :
    Tendsto (fun N => f 0 + ∑ j ∈ Finset.range N, (f ((j : ℤ)+1) + f (-((j : ℤ)+1))))
      atTop (𝓝 (∑' n, f n)) := by
  have hp : Summable (fun j : ℕ => f ((j : ℤ)+1)) :=
    hf.comp_injective (i := fun j : ℕ => ((j : ℤ)+1)) (by intro i j hij; dsimp at hij; omega)
  have hn : Summable (fun j : ℕ => f (-((j : ℤ)+1))) :=
    hf.comp_injective (i := fun j : ℕ => -((j : ℤ)+1)) (by intro i j hij; dsimp at hij; omega)
  have ht := (hp.add hn).hasSum.tendsto_sum_nat.const_add (f 0)
  rw [hp.tsum_add hn] at ht
  rw [tsum_of_add_one_of_neg_add_one hp hn]
  convert ht using 1 <;> ring

private theorem correction_tendsto (q : LaurentSeries k) (hq : ‖q‖₊ < 1) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, TateCurve.term (fun n => n) q (j+1))
      atTop (𝓝 (TateCurve.s₁ q)) := by
  have hs := TateCurve.summable_term (fun n => n) hq
  have ht := ((summable_nat_add_iff 1).mpr hs).hasSum.tendsto_sum_nat
  simpa only [TateCurve.s₁, TateCurve.coeffSum, hs.tsum_eq_zero_add,
    TateCurve.term_zero, zero_add] using ht

private theorem toLaurent_correction (d j : ℕ) (hd : 0 < d) :
    toLaurent k (PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1-monomial 1 (d*(j+1)))⁻¹) =
      TateCurve.term (fun n => n) (toLaurent k (monomial 1 d)) (j+1) := by
  have hp : 0 < d*(j+1) := Nat.mul_pos hd (by omega)
  have hmono : toLaurent k (monomial 1 (d*(j+1))) =
      (toLaurent k (monomial 1 d))^(j+1) := by
    simpa [monomial, toLaurent] using (annular_positive (k := k) d 0 j 1).symm
  rw [map_mul, map_mul, toLaurent_inv _ (monomial_denominator 1 _ (by omega)),
    map_sub, map_one, hmono]
  simp [toLaurent, TateCurve.term, div_eq_mul_inv, mul_assoc]

private theorem partialX_analytic (d i : ℕ) (a : k) (ha : Admissible d i a) (N : ℕ) :
    let q := toLaurent k (monomial 1 d)
    let u := toLaurent k (monomial a i)
    toLaurent k (partialX d i a N) =
      TateCurve.xTerm q u 0 +
      ∑ j ∈ Finset.range N, (TateCurve.xTerm q u ((j : ℤ)+1) +
        TateCurve.xTerm q u (-((j : ℤ)+1))) -
      2 * ∑ j ∈ Finset.range N, TateCurve.term (fun n => n) q (j+1) := by
  dsimp only
  simp only [partialX, map_sub, map_add, map_mul, map_ofNat, map_sum]
  rw [toLaurent_xTerm a i ha.2.2.2, TateCurve.xTerm_zero]
  congr 2
  · apply Finset.sum_congr rfl
    intro j hj
    have hp : 0 < d*(j+1)+i := by have := ha.1; positivity
    have hn : 0 < d*(j+1)-i := by
      apply Nat.sub_pos_of_lt
      have := ha.2.1
      nlinarith
    rw [toLaurent_xTerm a _ (by omega), toLaurent_xTerm a⁻¹ _ (by omega)]
    simp only [TateCurve.xTerm]
    rw [show (j : ℤ)+1 = ((j+1 : ℕ) : ℤ) by omega, zpow_natCast,
      annular_positive]
    rw [show -((j+1 : ℕ) : ℤ) = -((j : ℤ)+1) by omega,
      annular_negative d i j a ha.2.1,
      TateCurve.xfun_inv (laurent_monomial_ne_zero _ _ (inv_ne_zero ha.2.2.1))
        (laurent_monomial_ne_one _ _ (by omega))]
  · apply Finset.sum_congr rfl
    intro j hj
    simpa only [map_mul] using (toLaurent_correction (k := k) d j ha.1)

 theorem tateX_eq_pointX [CharZero k] (d i : ℕ) (a : k) (ha : Admissible d i a) :
    toLaurent k (tateX d i a) = TateCurve.pointX
      (toLaurent k (monomial 1 d)) (toLaurent k (monomial a i)) := by
  let q := toLaurent k (monomial 1 d)
  let u := toLaurent k (monomial a i)
  have hq0 : q ≠ 0 := laurent_monomial_ne_zero 1 d one_ne_zero
  have hu0 : u ≠ 0 := laurent_monomial_ne_zero a i ha.2.2.1
  have hq : ‖q‖₊ < 1 := by
    simpa [q, toLaurent, monomial] using
      (LaurentSeries.XAdic.nnnorm_X_pow_lt_one (F := k) ha.1.ne')
  have ht := (symmetric_sum_tendsto _ (TateCurve.summable_xTerm hq0 hq hu0)).sub
    ((correction_tendsto q hq).const_mul 2)
  have he := partialX_tendsto d i a ha
  apply tendsto_nhds_unique he
  simpa only [partialX_analytic d i a ha, TateCurve.pointX] using ht

private def analyticYTerm (q u : LaurentSeries k) (n : ℤ) : LaurentSeries k :=
  2 * TateCurve.yTerm q u n + TateCurve.xTerm q u n

private theorem partialY_analytic (d i : ℕ) (a : k) (ha : Admissible d i a) (N : ℕ) :
    let q := toLaurent k (monomial 1 d)
    let u := toLaurent k (monomial a i)
    toLaurent k (partialY d i a N) =
      (2 : LaurentSeries k)⁻¹ * (analyticYTerm q u 0 +
      ∑ j ∈ Finset.range N, (analyticYTerm q u ((j : ℤ)+1) +
        analyticYTerm q u (-((j : ℤ)+1)))) := by
  dsimp only
  simp only [partialY, map_mul, map_add, map_sum, map_sub]
  have hc : toLaurent k (PowerSeries.C (2 : k)⁻¹) = (2 : LaurentSeries k)⁻¹ := by
    rw [toLaurent, HahnSeries.ofPowerSeries_C, map_inv₀, map_ofNat]
  rw [hc, toLaurent_yTerm a i ha.2.2.2]
  apply congrArg (fun v : LaurentSeries k => (2 : LaurentSeries k)⁻¹ * v)
  simp only [analyticYTerm, TateCurve.yTerm_zero, TateCurve.xTerm_zero]
  apply congrArg (fun v : LaurentSeries k =>
    (2 * TateCurve.yfun (toLaurent k (monomial a i)) +
      TateCurve.xfun (toLaurent k (monomial a i))) + v)
  apply Finset.sum_congr rfl
  intro j hj
  have hp : 0 < d*(j+1)+i := by have := ha.1; positivity
  have hn : 0 < d*(j+1)-i := by
    apply Nat.sub_pos_of_lt
    have := ha.2.1
    nlinarith
  rw [toLaurent_yTerm a _ (by omega), toLaurent_yTerm a⁻¹ _ (by omega)]
  simp only [analyticYTerm, TateCurve.yTerm, TateCurve.xTerm]
  rw [show (j : ℤ)+1 = ((j+1 : ℕ) : ℤ) by omega, zpow_natCast, annular_positive]
  rw [show -((j+1 : ℕ) : ℤ) = -((j : ℤ)+1) by omega,
    annular_negative d i j a ha.2.1,
    TateCurve.xfun_inv (laurent_monomial_ne_zero _ _ (inv_ne_zero ha.2.2.1))
      (laurent_monomial_ne_one _ _ (by omega)),
    TateCurve.yfun_inv (laurent_monomial_ne_zero _ _ (inv_ne_zero ha.2.2.1))
      (laurent_monomial_ne_one _ _ (by omega))]
  ring

 theorem tateY_eq_pointY [CharZero k] (d i : ℕ) (a : k) (ha : Admissible d i a) :
    toLaurent k (tateY d i a) = TateCurve.pointY
      (toLaurent k (monomial 1 d)) (toLaurent k (monomial a i)) +
      TateCurve.pointX (toLaurent k (monomial 1 d)) (toLaurent k (monomial a i)) / 2 := by
  let q := toLaurent k (monomial 1 d)
  let u := toLaurent k (monomial a i)
  have hq0 : q ≠ 0 := laurent_monomial_ne_zero 1 d one_ne_zero
  have hu0 : u ≠ 0 := laurent_monomial_ne_zero a i ha.2.2.1
  have hq : ‖q‖₊ < 1 := by
    simpa [q, toLaurent, monomial] using
      (LaurentSeries.XAdic.nnnorm_X_pow_lt_one (F := k) ha.1.ne')
  have hx := TateCurve.summable_xTerm hq0 hq hu0
  have hy := TateCurve.summable_yTerm hq0 hq hu0
  have hs : Summable (analyticYTerm q u) := (hy.mul_left 2).add hx
  have ht := (symmetric_sum_tendsto _ hs).const_mul (2 : LaurentSeries k)⁻¹
  have he := partialY_tendsto d i a ha
  have hlimit : toLaurent k (tateY d i a) = (2 : LaurentSeries k)⁻¹ *
      (∑' n, analyticYTerm q u n) := by
    apply tendsto_nhds_unique he
    simpa only [partialY_analytic d i a ha] using ht
  rw [hlimit]
  simp only [analyticYTerm, (hy.mul_left 2).tsum_add hx, tsum_mul_left,
    TateCurve.pointX, TateCurve.pointY]
  dsimp only [q, u]
  field_simp
  <;> ring

/-- The literal coordinates satisfy the normalized Tate equation. -/
theorem literal_tate_equation [CharZero k] (d i : ℕ) (a : k) (ha : Admissible d i a) :
    let q := toLaurent k (monomial 1 d)
    let x := toLaurent k (tateX d i a)
    (toLaurent k (tateY d i a))^2 =
      x^3 + (1/4 : LaurentSeries k)*x^2 + TateCurve.a₄ q*x + TateCurve.a₆ q := by
  dsimp only
  rw [tateX_eq_pointX d i a ha, tateY_eq_pointY d i a ha]
  have hq : ‖toLaurent k (monomial 1 d)‖₊ < 1 := by
    simpa [toLaurent, monomial] using
      (LaurentSeries.XAdic.nnnorm_X_pow_lt_one (F := k) ha.1.ne')
  have ht := TateCurve.equation_pointX_pointY
    (laurent_monomial_ne_zero (1 : k) d one_ne_zero) hq
    (laurent_monomial_ne_zero a i ha.2.2.1) (annular_parameter d i a ha)
  linear_combination ht

private theorem split_cubic_of_roots {F : Type*} [Field F]
    (B C D e₁ e₂ e₃ x : F) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (h1 : e₁^3+B*e₁^2+C*e₁+D=0) (h2 : e₂^3+B*e₂^2+C*e₂+D=0)
    (h3 : e₃^3+B*e₃^2+C*e₃+D=0) :
    x^3+B*x^2+C*x+D = (x-e₁)*(x-e₂)*(x-e₃) := by
  have h12' : e₁^2+e₁*e₂+e₂^2+B*(e₁+e₂)+C = 0 := by
    apply (mul_eq_zero.mp (show (e₁-e₂)*(e₁^2+e₁*e₂+e₂^2+B*(e₁+e₂)+C)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h12)
    linear_combination h1-h2
  have h13' : e₁^2+e₁*e₃+e₃^2+B*(e₁+e₃)+C = 0 := by
    apply (mul_eq_zero.mp (show (e₁-e₃)*(e₁^2+e₁*e₃+e₃^2+B*(e₁+e₃)+C)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h13)
    linear_combination h1-h3
  have hsum : e₁+e₂+e₃+B = 0 := by
    apply (mul_eq_zero.mp (show (e₂-e₃)*(e₁+e₂+e₃+B)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h23)
    linear_combination h12'-h13'
  have hpair : C-(e₁*e₂+e₁*e₃+e₂*e₃)=0 := by
    linear_combination h12'-(e₁+e₂)*hsum
  have hprod : D+e₁*e₂*e₃=0 := by
    linear_combination h1-e₁^2*hsum-e₁*hpair
  linear_combination x^2*hsum+x*hpair+hprod

/-- The three literal two-torsion values split the normalized cubic. -/
theorem general_annular_split_cubic :
    ∀ {k : Type u} [Field k] [CharZero k], ∀ (m i : ℕ) (a : k),
      Admissible (2*m) i a →
      (tateY (2*m) i a)^2 =
        (tateX (2*m) i a - tateX (2*m) 0 (-1 : k)) *
        (tateX (2*m) i a - tateX (2*m) m (1 : k)) *
        (tateX (2*m) i a - tateX (2*m) m (-1 : k)) := by
  intro k _ _ m i a ha
  have hm : 0 < m := by have := ha.1; omega
  have h1 : Admissible (2*m) 0 (-1 : k) := by
    refine ⟨by omega, by omega, by norm_num, ?_⟩
    intro _
    norm_num
  have h2 : Admissible (2*m) m (1 : k) := by
    exact ⟨by omega, by omega, one_ne_zero, by omega⟩
  have h3 : Admissible (2*m) m (-1 : k) := by
    exact ⟨by omega, by omega, by norm_num, by omega⟩
  let j := toLaurent k
  have hinj : Function.Injective j := HahnSeries.ofPowerSeries_injective
  rcases general_two_torsion_distinct (k := k) m hm with ⟨h12,h13,h23⟩
  have hr1 := literal_tate_equation (2*m) 0 (-1 : k) h1
  have hr2 := literal_tate_equation (2*m) m (1 : k) h2
  have hr3 := literal_tate_equation (2*m) m (-1 : k) h3
  simp only [tateY_boundary_neg_one, map_zero, zero_pow (by decide : 2 ≠ 0)] at hr1
  simp only [tateY_midpoint_one m hm, map_zero, zero_pow (by decide : 2 ≠ 0)] at hr2
  simp only [tateY_midpoint_neg_one m hm, map_zero, zero_pow (by decide : 2 ≠ 0)] at hr3
  apply hinj
  simp only [map_pow, map_mul, map_sub]
  rw [literal_tate_equation (2*m) i a ha]
  exact split_cubic_of_roots _ _ _ _ _ _ _
    (fun h => h12 (hinj h)) (fun h => h13 (hinj h)) (fun h => h23 (hinj h))
    hr1.symm hr2.symm hr3.symm

end ArithmeticThetaTateIdentities
