import TateSeriesStabilization

noncomputable section
universe u
namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

private theorem constant_terms_inverse {k : Type u} [Field k] (a : k)
    (ha : a ≠ 0) (ha1 : a ≠ 1) :
    xTerm (monomial a⁻¹ 0) = xTerm (monomial a 0) ∧
    yTerm (monomial a⁻¹ 0) = -yTerm (monomial a 0) := by
  have h1 : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have h2 : 1 - a⁻¹ ≠ 0 := sub_ne_zero.mpr (by simpa using ha1)
  have hx : a⁻¹ * ((1-a⁻¹)⁻¹)^2 = a * ((1-a)⁻¹)^2 := by
    field_simp
    ring
  have hy : a⁻¹ * (1+a⁻¹) * ((1-a⁻¹)⁻¹)^3 = -(a * (1+a) * ((1-a)⁻¹)^3) := by
    field_simp
    ring
  simp only [monomial, pow_zero, mul_one, xTerm, yTerm]
  simp only [← map_one (PowerSeries.C (R := k)), ← map_sub, PowerSeries.C_inv,
    ← map_pow, ← map_mul, ← map_add, ← map_neg]
  exact ⟨congrArg PowerSeries.C hx, congrArg PowerSeries.C hy⟩

private theorem shift_sum {R : Type*} [AddCommGroup R] (f : ℕ → R) (N : ℕ)
    (h : f N = 0) : f 0 + ∑ j ∈ Finset.range N, f (j+1) = ∑ j ∈ Finset.range N, f j := by
  have hsum := Finset.sum_range_succ' f N
  rw [Finset.sum_range_succ, h, add_zero] at hsum
  simpa [add_comm] using hsum.symm

private theorem x_below {k : Type u} [Field k] (a : k) (m n : ℕ)
    (h : n < m) : PowerSeries.coeff n (xTerm (monomial a m)) = 0 := by
  rw [x_term_coeff a m n (by omega)]
  simp [Nat.div_eq_of_lt h]

private theorem y_below {k : Type u} [Field k] (a : k) (m n : ℕ)
    (h : n < m) : PowerSeries.coeff n (yTerm (monomial a m)) = 0 := by
  rw [y_term_coeff a m n (by omega)]
  simp [Nat.div_eq_of_lt h]

private theorem reindex_pair {R : Type*} [CommRing R] (f g : ℕ → R) (N : ℕ)
    (hf : f N = 0) (hg : g N = 0) :
    (g 0 + ∑ j ∈ Finset.range N, (g (j+1) + f j) =
      f 0 + ∑ j ∈ Finset.range N, (f (j+1) + g j)) ∧
    (g 0 + ∑ j ∈ Finset.range N, (g (j+1) - f j) =
      -(f 0 + ∑ j ∈ Finset.range N, (f (j+1) - g j))) := by
  have hf' := shift_sum f N hf
  have hg' := shift_sum g N hg
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  constructor
  · linear_combination hg' - hf'
  · linear_combination hg' + hf'

private theorem interior_reindex {k : Type u} [Field k] (d i n : ℕ) (a : k)
    (hi : 0 < i) (hid : i < d) (F : k → ℕ → k)
    (hF : ∀ b m, n < m → F b m = 0) :
    (F a⁻¹ (d-i) + ∑ j ∈ Finset.range (n+1),
        (F a⁻¹ (d*(j+1)+(d-i)) + F a (d*(j+1)-(d-i))) =
      F a i + ∑ j ∈ Finset.range (n+1),
        (F a (d*(j+1)+i) + F a⁻¹ (d*(j+1)-i))) ∧
    (F a⁻¹ (d-i) + ∑ j ∈ Finset.range (n+1),
        (F a⁻¹ (d*(j+1)+(d-i)) - F a (d*(j+1)-(d-i))) =
      -(F a i + ∑ j ∈ Finset.range (n+1),
        (F a (d*(j+1)+i) - F a⁻¹ (d*(j+1)-i)))) := by
  have hmul : n+1 ≤ d*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
  have hf : F a (d*(n+1)+i) = 0 := hF _ _ (by omega)
  have hg : F a⁻¹ (d*((n+1)+1)-i) = 0 := by
    apply hF
    have : d*((n+1)+1) = d*(n+1)+d := by ring
    omega
  have hs := reindex_pair (fun j => F a (d*j+i))
    (fun j => F a⁻¹ (d*(j+1)-i)) (n+1) hf hg
  have hplus : ∀ j, d*(j+1)+(d-i) = d*((j+1)+1)-i := by
    intro j
    have : d*((j+1)+1) = d*(j+1)+d := by ring
    omega
  have hminus : ∀ j, d*(j+1)-(d-i) = d*j+i := by
    intro j
    have : d*(j+1) = d*j+d := by ring
    omega
  simpa only [hplus, hminus, Nat.mul_zero, Nat.zero_add, Nat.zero_add,
    Nat.mul_one] using hs

private theorem constant_partial_inverse {k : Type u} [Field k] (d N : ℕ) (a : k)
    (ha : a ≠ 0) (ha1 : a ≠ 1) :
    partialX d 0 a⁻¹ N = partialX d 0 a N ∧
    partialY d 0 a⁻¹ N = -partialY d 0 a N := by
  obtain ⟨hx, hy⟩ := constant_terms_inverse a ha ha1
  constructor
  · simp only [partialX, Nat.add_zero, Nat.sub_zero, inv_inv, hx]
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    exact add_comm _ _
  · simp only [partialY, Nat.add_zero, Nat.sub_zero, inv_inv, hy]
    rw [← mul_neg]
    congr 1
    rw [neg_add, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (neg_sub _ _).symm

/-- Read any sufficiently long finite annular sum as the stable coefficient. -/
private theorem stable_coefficients {k : Type u} [Field k] [CharZero k]
    (d i : ℕ) (a : k) (ha : Admissible d i a) (n N : ℕ) (hN : n+1 ≤ N) :
    PowerSeries.coeff n (tateX d i a) = PowerSeries.coeff n (partialX d i a N) ∧
    PowerSeries.coeff n (tateY d i a) = PowerSeries.coeff n (partialY d i a N) := by
  obtain ⟨hx, hy⟩ := annular_stabilization d i a ha n N hN
  simpa only [tateX, tateY, PowerSeries.coeff_mk] using And.intro hx.symm hy.symm

/-- Inversion preserves X and reverses the normalized Y coordinate on both
    the constant chart and each interior annular chart. -/
theorem annular_inversion :
    (∀ {k : Type u} [Field k] [CharZero k] (d : ℕ) (a : k),
      0 < d → a ≠ 0 → a ≠ 1 →
      tateX d 0 a⁻¹ = tateX d 0 a ∧ tateY d 0 a⁻¹ = -tateY d 0 a) ∧
    (∀ {k : Type u} [Field k] [CharZero k] (d i : ℕ) (a : k),
      0 < i → i < d → a ≠ 0 →
      tateX d (d-i) a⁻¹ = tateX d i a ∧ tateY d (d-i) a⁻¹ = -tateY d i a) := by
  constructor
  · intro k _ _ d a hd ha ha1
    constructor
    · apply PowerSeries.ext
      intro n
      simp only [tateX, PowerSeries.coeff_mk]
      exact congrArg (PowerSeries.coeff n) (constant_partial_inverse d (n+1) a ha ha1).1
    · apply PowerSeries.ext
      intro n
      simp only [tateY, PowerSeries.coeff_mk, map_neg]
      simpa only [map_neg] using
        congrArg (PowerSeries.coeff n) (constant_partial_inverse d (n+1) a ha ha1).2
  · intro k _ _ d i a hi hid ha
    have hadm : Admissible d i a := ⟨by omega, hid, ha, by omega⟩
    have hadm' : Admissible d (d-i) a⁻¹ :=
      ⟨by omega, by omega, inv_ne_zero ha, by omega⟩
    constructor
    · apply PowerSeries.ext
      intro n
      rw [(stable_coefficients d (d-i) a⁻¹ hadm' n (n+1) le_rfl).1,
        (stable_coefficients d i a hadm n (n+1) le_rfl).1]
      have hr := (interior_reindex d i n a hi hid
        (fun b m => PowerSeries.coeff n (xTerm (monomial b m)))
        (fun b m h => x_below b m n h)).1
      simp only [partialX, inv_inv, two_mul, map_add, map_sub, map_sum]
      rw [hr]
    · apply PowerSeries.ext
      intro n
      rw [map_neg, (stable_coefficients d (d-i) a⁻¹ hadm' n (n+1) le_rfl).2,
        (stable_coefficients d i a hadm n (n+1) le_rfl).2]
      have hr := (interior_reindex d i n a hi hid
        (fun b m => PowerSeries.coeff n (yTerm (monomial b m)))
        (fun b m h => y_below b m n h)).2
      simp only [partialY, inv_inv, PowerSeries.coeff_C_mul, map_add, map_sub, map_sum]
      rw [hr, mul_neg]

end ArithmeticThetaTateBridges
