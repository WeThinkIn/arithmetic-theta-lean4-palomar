import LaurentNormDefinitionsR0064

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaLaurentNormR0064

private def TrConverges {F : Type} [Field F] (f : ℕ → LaurentSeries F)
    (g : LaurentSeries F) : Prop :=
  ∀ n : ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ e : ℤ, e ≤ n →
    (f N).coeff e = g.coeff e

private theorem tr_unique {F : Type} [Field F] {f : ℕ → LaurentSeries F}
    {g h : LaurentSeries F} (hg : TrConverges f g) (hh : TrConverges f h) : g = h := by
  ext e
  obtain ⟨M, hM⟩ := hg e
  obtain ⟨N, hN⟩ := hh e
  exact (hM (max M N) (le_max_left _ _) e le_rfl).symm.trans
    (hN (max M N) (le_max_right _ _) e le_rfl)

private theorem tr_single {F : Type} [Field F] {f : ℕ → LaurentSeries F}
    {g : LaurentSeries F} (hg : TrConverges f g) (b : ℤ) (c : F) :
    TrConverges (fun N => HahnSeries.single b c * f N) (HahnSeries.single b c * g) := by
  intro n
  obtain ⟨M, hM⟩ := hg (n-b)
  refine ⟨M, fun N hN e he => ?_⟩
  simp only [HahnSeries.coeff_single_mul]
  rw [hM N hN (e-b) (by omega)]

private theorem tr_tail {F : Type} [Field F] {f : ℕ → LaurentSeries F}
    {g : LaurentSeries F} (hg : TrConverges f g) (b : ℕ → ℤ) (c : F)
    (hb : ∀ B : ℤ, ∃ M : ℕ, ∀ N ≥ M, B ≤ b N) :
    TrConverges (fun N => f N * (1 - HahnSeries.single (b N) c)) g := by
  intro n
  obtain ⟨M, hM⟩ := hg n
  obtain ⟨L, hL⟩ := hb (max 0 (n-g.order+1))
  refine ⟨max M L, fun N hN e he => ?_⟩
  have hbN := hL N (le_trans (le_max_right _ _) hN)
  have hnonneg : 0 ≤ b N := le_trans (le_max_left _ _) hbN
  have hsmall : e - b N < g.order := by
    have := le_trans (le_max_right 0 (n-g.order+1)) hbN
    omega
  simp only [mul_sub, mul_one, HahnSeries.coeff_sub, HahnSeries.coeff_mul_single]
  rw [hM N (le_trans (le_max_left _ _) hN) e he,
    hM N (le_trans (le_max_left _ _) hN) (e-b N) (by omega),
    HahnSeries.coeff_eq_zero_of_lt_order hsmall]
  simp

private theorem tr_succ {F : Type} [Field F] {f : ℕ → LaurentSeries F}
    {g : LaurentSeries F} (hg : TrConverges (fun N => f (N+1)) g) :
    TrConverges f g := by
  intro n
  obtain ⟨M, hM⟩ := hg n
  refine ⟨M+1, fun N hN e he => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ K, N = K+1 := ⟨N-1, by omega⟩
  exact hM N (by omega) e he

private theorem tr_partial_step (F : Type) [Field F] (d m N : ℕ) (a : F)
    (ha : a ≠ 0) :
    Partial F d (m+d) a (N+1) =
      HahnSeries.single (-(m : ℤ)) (-a⁻¹) * Partial F d m a N *
        (1 - HahnSeries.single ((d : ℤ)*N+m) a) *
        (1 - HahnSeries.single ((d : ℤ)*(N+1)+m) a) := by
  let f : ℕ → LaurentSeries F := fun l => 1 - HahnSeries.single ((d : ℤ)*l+m) a
  let b : ℕ → LaurentSeries F := fun l => 1 - HahnSeries.single ((d : ℤ)*(l+1)-m) a⁻¹
  let u : LaurentSeries F := HahnSeries.single (-(m : ℤ)) (-a⁻¹)
  have hu : u * f 0 = 1 - HahnSeries.single (-(m : ℤ)) a⁻¹ := by
    dsimp [u, f]
    simp only [mul_zero, zero_add, mul_sub, mul_one,
      HahnSeries.single_mul_single, neg_add_cancel, neg_mul, inv_mul_cancel₀ ha,
      HahnSeries.single_neg, HahnSeries.single_zero_one]
    ring
  have hf : (∏ l ∈ Finset.range N, f l) * f N * f (N+1) =
      f 0 * ∏ l ∈ Finset.range (N+1), f (l+1) := by
    rw [← Finset.prod_range_succ, ← Finset.prod_range_succ, Finset.prod_range_succ', mul_comm]
  have hforward : (∏ l ∈ Finset.range (N+1),
      (1 - HahnSeries.C a * HahnSeries.single ((d : ℤ)*l+(m+d)) (1 : F))) =
      ∏ l ∈ Finset.range (N+1), f (l+1) := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    dsimp [f]
    apply congrArg (fun e : ℤ => (1 - HahnSeries.single e a : LaurentSeries F))
    ring
  have hback : (∏ l ∈ Finset.range (N+1),
      (1 - HahnSeries.C a⁻¹ * HahnSeries.single ((d : ℤ)*(l+1)-(m+d)) (1 : F))) =
      (1 - HahnSeries.single (-(m : ℤ)) a⁻¹) * ∏ l ∈ Finset.range N, b l := by
    rw [Finset.prod_range_succ']
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    have h0 : (d : ℤ)*(0+1)-(m+d) = -(m : ℤ) := by push_cast; ring
    simp only [Nat.cast_zero]
    rw [h0, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    dsimp [b]
    apply congrArg (fun e : ℤ => (1 - HahnSeries.single e a⁻¹ : LaurentSeries F))
    ring
  unfold Partial
  simp only [Nat.cast_add]
  rw [hforward, hback]
  have hnorm : (∏ l ∈ Finset.range N,
      (1 - HahnSeries.C a * HahnSeries.single ((d : ℤ)*l+m) (1 : F))) *
      (∏ l ∈ Finset.range N,
      (1 - HahnSeries.C a⁻¹ * HahnSeries.single ((d : ℤ)*(l+1)-m) (1 : F))) =
      (∏ l ∈ Finset.range N, f l) * ∏ l ∈ Finset.range N, b l := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    rfl
  rw [hnorm, ← hu]
  change _ = u * ((∏ l ∈ Finset.range N, f l) * ∏ l ∈ Finset.range N, b l) * f N * f (N+1)
  calc
    _ = u * (f 0 * ∏ l ∈ Finset.range (N+1), f (l+1)) *
        (∏ l ∈ Finset.range N, b l) := by ring
    _ = _ := by rw [← hf]; ring

private theorem tr_step_limit (F : Type) [Field F] (d m : ℕ) (a : F)
    (hd : 0 < d) (ha : a ≠ 0) (g : LaurentSeries F) (hg : IsGamma F d m a g) :
    IsGamma F d (m+d) a (HahnSeries.single (-(m : ℤ)) (-a⁻¹) * g) := by
  have hb (j : ℕ) : ∀ B : ℤ, ∃ M : ℕ, ∀ N ≥ M, B ≤ (d : ℤ)*(N+j)+m := by
    intro B
    refine ⟨B.toNat, fun N hN => ?_⟩
    have hBN : B ≤ (N : ℤ) := by omega
    have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hNj : (N : ℤ) ≤ (d : ℤ)*(N+j)+m := by nlinarith
    exact hBN.trans hNj
  have h₁ := tr_tail (tr_single hg (-(m : ℤ)) (-a⁻¹))
    (fun N => (d : ℤ)*N+m) a (by simpa using hb 0)
  have h₂ := tr_tail h₁ (fun N => (d : ℤ)*(N+1)+m) a (by simpa using hb 1)
  apply tr_succ
  simpa only [tr_partial_step F d m _ a ha] using h₂

private theorem tr_monomial_inverse (F : Type) [Field F] (m : ℕ) (a : F)
    (ha : a ≠ 0) :
    HahnSeries.single (-(m : ℤ)) (-a⁻¹) = (-(HahnSeries.C a * t F ^ m))⁻¹ := by
  apply left_inv_eq_right_inv ?_ (inv_mul_cancel₀ ?_)
  · simp [t, HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single,
      ← HahnSeries.single_neg, ha]
  · simp [t, HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single, ha]

private theorem tr_triangle_succ (k : ℕ) :
    ArithmeticThetaNormFiniteR0063.triangle (k+1) =
      ArithmeticThetaNormFiniteR0063.triangle k + k := by
  unfold ArithmeticThetaNormFiniteR0063.triangle
  push_cast
  have he : ((k : ℤ)+1)*((k : ℤ)+1-1) = (k : ℤ)*((k : ℤ)-1)+(k : ℤ)*2 := by ring
  rw [he, Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- Iterated translation of the literal Laurent gamma product. -/
theorem gamma_translation (F : Type) [Field F] (d m k : ℕ) (a : F)
    (hd : 0 < d) (_hm : m < d) (ha : a ≠ 0) (g h : LaurentSeries F)
    (hg : IsGamma F d m a g) (hh : IsGamma F d (m+d*k) a h) :
    h = (-(HahnSeries.C a * t F ^ m)) ^ (-(k : ℤ)) *
      (t F ^ d) ^ (-ArithmeticThetaNormFiniteR0063.triangle k) * g := by
  have ht : t F ≠ 0 := by simp [t]
  have hz : -(HahnSeries.C a * t F ^ m) ≠ 0 := by
    simp [ha, ht, HahnSeries.C_apply]
  have hq : t F ^ d ≠ 0 := pow_ne_zero _ ht
  have hlim : ∀ k : ℕ, IsGamma F d (m+d*k) a
      ((-(HahnSeries.C a * t F ^ m)) ^ (-(k : ℤ)) *
        (t F ^ d) ^ (-ArithmeticThetaNormFiniteR0063.triangle k) * g) := by
    intro k
    induction k with
    | zero => simpa [ArithmeticThetaNormFiniteR0063.triangle] using hg
    | succ k ih =>
      have hs := tr_step_limit F d (m+d*k) a hd ha _ ih
      rw [tr_monomial_inverse F _ a ha] at hs
      have he : -(HahnSeries.C a * t F ^ (m+d*k)) =
          (-(HahnSeries.C a * t F ^ m)) * (t F ^ d)^k := by
        rw [pow_add, pow_mul]
        ring
      rw [he, mul_inv_rev, ← zpow_neg_one, ← zpow_natCast (t F ^ d) k,
        ← zpow_mul] at hs
      simp only [mul_neg_one] at hs
      rw [tr_triangle_succ]
      convert hs using 1
      · ring
      · simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [zpow_add₀ hz, zpow_add₀ hq]
        simp only [zpow_neg, zpow_one]
        ring
  exact tr_unique hh (hlim k)

end ArithmeticThetaLaurentNormR0064
