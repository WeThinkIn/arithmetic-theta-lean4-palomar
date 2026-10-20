module

public import DiscriminantDefinitions

@[expose] public section

namespace ArithmeticThetaDiscriminant

 theorem partial_step {R : Type*} [CommRing R] (a : R) (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (partialEuler a (N+1)) = PowerSeries.coeff d (partialEuler a N) := by
  simp [partialEuler, Finset.prod_range_succ, mul_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', show ¬N+1 ≤ d by omega]

 theorem partial_stable (R : Type) [CommRing R] (a : R) (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (partialEuler a N) = PowerSeries.coeff d (euler a) := by
  simp only [euler, PowerSeries.coeff_mk]
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih => rw [partial_step a d N h, ih]

 theorem euler_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    PowerSeries.map f (euler a) = euler (f a) := by
  apply PowerSeries.ext
  intro d
  simp [euler, partialEuler, PowerSeries.coeff_map, ← PowerSeries.coeff_map f,
    map_prod]

 theorem P_constant : PowerSeries.constantCoeff P = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  change PowerSeries.coeff 0 (euler (1 : ℚ)) = 1
  rw [← partial_stable ℚ 1 0 0 (by rfl)]
  simp [partialEuler]

 theorem swap_coeff (F : PowerSeries (PowerSeries ℚ)) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (swap F)) =
      PowerSeries.coeff i (PowerSeries.coeff j F) := by
  simp [swap]

 theorem swap_mul (F G : PowerSeries (PowerSeries ℚ)) : swap (F * G) = swap F * swap G := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp only [swap_coeff, PowerSeries.coeff_mul, map_sum]
  exact Finset.sum_comm

 theorem swap_add (F G : PowerSeries (PowerSeries ℚ)) : swap (F + G) = swap F + swap G := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp only [swap_coeff, map_add]

 theorem swap_one : swap 1 = 1 := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp only [swap_coeff, PowerSeries.coeff_one]
  split_ifs <;> simp_all

 theorem swap_ring :
    (∀ F G : PowerSeries (PowerSeries ℚ), swap (F * G) = swap F * swap G) ∧
    (∀ F G : PowerSeries (PowerSeries ℚ), swap (F + G) = swap F + swap G) ∧ swap 1 = 1 :=
  ⟨swap_mul, swap_add, swap_one⟩

 theorem swap_constant (F : PowerSeries (PowerSeries ℚ)) :
    PowerSeries.constantCoeff (swap F) = PowerSeries.map PowerSeries.constantCoeff F := by
  apply PowerSeries.ext
  intro j
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, swap_coeff]
  simp

 theorem swap_C_coeff (a : PowerSeries ℚ) (i : ℕ) :
    PowerSeries.coeff i (swap (PowerSeries.C a)) = PowerSeries.C (PowerSeries.coeff i a) := by
  apply PowerSeries.ext
  intro j
  rw [swap_coeff]
  simp only [PowerSeries.coeff_C]
  split_ifs <;> simp

 theorem z_constant (c : ℕ) : PowerSeries.constantCoeff ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) = 1 := by
  simp [zUnit]

 theorem z_inv_constant (c : ℕ) : PowerSeries.constantCoeff (((zUnit ^ c)⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (zUnit ^ c).val_inv
  simpa only [map_mul, map_one, z_constant, one_mul, Units.inv_eq_val_inv] using h

 theorem gamma_initial (c : ℕ) :
    PowerSeries.constantCoeff (gamma c) = 0 ∧
    PowerSeries.coeff 1 (gamma c) = -(c : PowerSeries ℚ) * P ^ 2 := by
  have ha : PowerSeries.constantCoeff (swap (euler ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ))) = P := by
    rw [swap_constant, euler_map, z_constant]
    rfl
  have hb : PowerSeries.constantCoeff (swap (euler (((zUnit ^ c)⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ))) = P := by
    rw [swap_constant, euler_map, z_inv_constant]
    rfl
  have hz : PowerSeries.constantCoeff (swap (PowerSeries.C (1 - ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ)))) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, swap_C_coeff]
    simp only [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_one, z_constant, sub_self, map_zero]
  have h1 : PowerSeries.coeff 1 (swap (PowerSeries.C (1 - ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ)))) = -(c : PowerSeries ℚ) := by
    rw [swap_C_coeff]
    simp [zUnit, PowerSeries.coeff_one_pow]
  simp only [gamma, gammaQ, swap_ring.1]
  constructor
  · simp only [map_mul, hz, zero_mul]
  · rw [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_mul]
    simp only [map_mul, hz, h1, ha, hb, mul_zero, add_zero, zero_mul]
    ring

end ArithmeticThetaDiscriminant

namespace ArithmeticThetaDiscriminant

instance : CharZero K := charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := ℚ))

 theorem p_ne_zero : p ≠ 0 := by
  intro h
  have hp : P = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [p, qEmbed] using h)
  have := congrArg PowerSeries.constantCoeff hp
  rw [P_constant, map_zero] at this
  exact one_ne_zero this

 theorem q_ne_zero : q ≠ 0 := by
  intro h
  have hx : (PowerSeries.X : PowerSeries ℚ) = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [q, qEmbed] using h)
  exact PowerSeries.X_ne_zero hx

 theorem embedded_initial_one (s : PowerSeries K) (h0 : PowerSeries.constantCoeff s = 0)
    (h1 : PowerSeries.coeff 1 s ≠ 0) :
    ((HahnSeries.ofPowerSeries ℤ K) s).order = 1 ∧
    ((HahnSeries.ofPowerSeries ℤ K) s).leadingCoeff = PowerSeries.coeff 1 s := by
  let f : T := (HahnSeries.ofPowerSeries ℤ K) s
  have hc : f.coeff 1 = PowerSeries.coeff 1 s := HahnSeries.ofPowerSeries_apply_coeff s 1
  have hf : f ≠ 0 := by intro h; apply h1; simpa [h] using hc.symm
  have ho : f.order = 1 := by
    apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (hc ▸ h1))
    apply (HahnSeries.le_order_iff_forall hf).mpr
    intro j hj
    change ((s : LaurentSeries K)).coeff j = 0
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · have : j = 0 := by omega
      subst j
      simpa using h0
  exact ⟨ho, by rw [HahnSeries.leadingCoeff_eq, ho, hc]⟩

 theorem embedded_initial_zero (s : PowerSeries K) (h0 : PowerSeries.constantCoeff s ≠ 0) :
    ((HahnSeries.ofPowerSeries ℤ K) s).order = 0 ∧
    ((HahnSeries.ofPowerSeries ℤ K) s).leadingCoeff = PowerSeries.constantCoeff s := by
  let f : T := (HahnSeries.ofPowerSeries ℤ K) s
  have hc : f.coeff 0 = PowerSeries.constantCoeff s := by
    simpa using HahnSeries.ofPowerSeries_apply_coeff s 0
  have hf : f ≠ 0 := by intro h; apply h0; simpa [h] using hc.symm
  have ho : f.order = 0 := by
    apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (hc ▸ h0))
    apply (HahnSeries.le_order_iff_forall hf).mpr
    intro j hj
    change ((s : LaurentSeries K)).coeff j = 0
    simp [PowerSeries.coeff_coe, hj]
  exact ⟨ho, by rw [HahnSeries.leadingCoeff_eq, ho, hc]⟩

 theorem gamma_laurent_initial (c : ℕ) (hc : c ≠ 0) :
    (tEmbed (gamma c)).order = 1 ∧
    (tEmbed (gamma c)).leadingCoeff = -(c : K) * p ^ 2 := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.map qEmbed (gamma c)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, (gamma_initial c).1, map_zero]
  have h1 : PowerSeries.coeff 1 (PowerSeries.map qEmbed (gamma c)) = -(c : K) * p ^ 2 := by
    simp only [PowerSeries.coeff_map, (gamma_initial c).2, map_mul, map_neg, map_natCast, map_pow, p]
  have hn : PowerSeries.coeff 1 (PowerSeries.map qEmbed (gamma c)) ≠ 0 := by
    rw [h1]
    exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) (pow_ne_zero _ p_ne_zero)
  have h := embedded_initial_one _ h0 hn
  simpa only [tEmbed, RingHom.comp_apply, h1] using h

 theorem tZ_initial : tZ.order = 0 ∧ tZ.leadingCoeff = 1 := by
  have h := embedded_initial_zero (1 + PowerSeries.X) (by simp : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries K) ≠ 0)
  simpa [tZ] using h

 theorem leading_pow (f : T) (n : ℕ) : (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

 theorem leading_inv (f : T) : (f⁻¹).leadingCoeff = f.leadingCoeff⁻¹ := by
  by_cases hf : f = 0
  · rw [hf, @inv_zero T _, HahnSeries.leadingCoeff_zero, @inv_zero K _]
  have h := congrArg (fun x : T => x.leadingCoeff) (mul_inv_cancel₀ hf)
  rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_one] at h
  exact eq_inv_of_mul_eq_one_right h

 theorem order_inv (f : T) (hf : f ≠ 0) : (f⁻¹).order = -f.order := by
  have h := congrArg (fun x : T => x.order) (mul_inv_cancel₀ hf)
  rw [HahnSeries.order_mul hf (inv_ne_zero hf), HahnSeries.order_one] at h
  omega

end ArithmeticThetaDiscriminant

namespace ArithmeticThetaDiscriminant

 theorem gamma_embed_ne_zero (c : ℕ) (hc : c ≠ 0) : tEmbed (gamma c) ≠ 0 := by
  intro h
  have ho := (gamma_laurent_initial c hc).1
  rw [h, HahnSeries.order_zero] at ho
  norm_num at ho

 theorem tZ_ne_zero : tZ ≠ 0 := by
  intro h
  have hl := tZ_initial.2
  rw [h, HahnSeries.leadingCoeff_zero] at hl
  exact zero_ne_one hl

 theorem f5_order : f5.order = 24 := by
  have hQ : (HahnSeries.single 0 (q ^ 2) : T) ≠ 0 :=
    HahnSeries.single_ne_zero (pow_ne_zero _ q_ne_zero)
  have hZ : (-tZ) ^ 10 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr tZ_ne_zero)
  have hG1 := gamma_embed_ne_zero 1 (by decide)
  have hG5 := gamma_embed_ne_zero 5 (by decide)
  simp only [f5, div_eq_mul_inv]
  rw [HahnSeries.order_mul (mul_ne_zero (mul_ne_zero hQ (@inv_ne_zero T _ _ hZ)) (pow_ne_zero 25 hG1)) (@inv_ne_zero T _ _ hG5),
    HahnSeries.order_mul (mul_ne_zero hQ (@inv_ne_zero T _ _ hZ)) (pow_ne_zero 25 hG1),
    HahnSeries.order_mul hQ (@inv_ne_zero T _ _ hZ),
    order_inv _ hZ, order_inv _ hG5,
    HahnSeries.order_single (pow_ne_zero 2 q_ne_zero),
    HahnSeries.order_pow, HahnSeries.order_pow, HahnSeries.order_neg,
    (gamma_laurent_initial 1 (by decide)).1,
    (gamma_laurent_initial 5 (by decide)).1, tZ_initial.1]
  norm_num


 theorem f5_coefficient : f5.coeff 24 = (1 / 5 : K) * q ^ 2 * p ^ 48 := by
  rw [← f5_order, ← HahnSeries.leadingCoeff_eq]
  simp only [f5, div_eq_mul_inv, HahnSeries.leadingCoeff_mul, leading_inv, leading_pow,
    HahnSeries.leadingCoeff_of_single, HahnSeries.leadingCoeff_neg, tZ_initial.2,
    (gamma_laurent_initial 1 (by decide)).2, (gamma_laurent_initial 5 (by decide)).2]
  norm_num
  field_simp [p_ne_zero]

 theorem D2_initial :
    (∀ k : ℤ, k < 24 → (5 * f5).coeff k = 0) ∧ (5 * f5).coeff 24 = q ^ 2 * p ^ 48 := by
  have hscale (k : ℤ) : (5 * f5).coeff k = 5 * f5.coeff k := by
    change ((HahnSeries.single 0 (5 : K)) * f5).coeff k = _
    exact HahnSeries.coeff_single_zero_mul
  constructor
  · intro k hk
    rw [hscale, HahnSeries.coeff_eq_zero_of_lt_order (by rw [f5_order]; exact hk), mul_zero]
  · rw [hscale, f5_coefficient]
    field_simp

end ArithmeticThetaDiscriminant
