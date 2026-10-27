import TateIdentityDefinitions
import FormalNormProduct

/-! Literal gamma products on the fundamental annulus and their Laurent extension.
The two contract theorems include the zero-residue boundary; inversion never
cancels a gamma value. Dependencies are immutable accepted source snapshots. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaTateIdentities
open ArithmeticThetaFormalNorm ArithmeticThetaTateSeries
variable {k : Type u} [Field k]

lemma gamma_annulus (d i : ℕ) (a : k) (hi : i < d) :
    gammaLaurent d (i : ℤ) a = toLaurent k (fullGamma d i a a⁻¹) := by
  have hdiv : (i : ℤ) / (d : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have hmod : (i : ℤ) % (d : ℤ) = i := Int.emod_eq_of_lt (by omega) (by omega)
  simp [gammaLaurent, hdiv, hmod]

lemma gamma_constant (d i : ℕ) (a b : k) (hi : i < d) :
    PowerSeries.constantCoeff (fullGamma d i a b) = if i = 0 then 1-a else 1 := by
  have he : d - i ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_cases hi0 : i = 0 <;> simp [fullGamma, partialGamma, PowerSeries.coeff_zero_eq_constantCoeff, he, hi0, hd0]

theorem gamma_annular_unit [CharZero k] (d i : ℕ) (a : k)
    (h : Admissible d i a) :
    IsUnit (fullGamma d i a a⁻¹) ∧
    gammaLaurent d (i : ℤ) a = toLaurent k (fullGamma d i a a⁻¹) := by
  refine ⟨?_, gamma_annulus d i a h.2.1⟩
  rw [PowerSeries.isUnit_iff_constantCoeff, gamma_constant d i a a⁻¹ h.2.1]
  split_ifs with hi
  · exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm (h.2.2.2 hi)))
  · exact isUnit_one

/-- Reflection exchanges the two finite tails when the residue is positive. -/
lemma gamma_reflect (d r : ℕ) (a : k) (hr : 0 < r) (hrd : r < d) :
    fullGamma d (d-r) a⁻¹ a = fullGamma d r a a⁻¹ := by
  apply PowerSeries.ext
  intro n
  unfold fullGamma
  simp only [PowerSeries.coeff_mk]
  congr 1
  unfold partialGamma
  have he (j : ℕ) : d*j+(d-r) = d*(j+1)-r := by rw [Nat.mul_succ]; omega
  have he' (j : ℕ) : d*(j+1)-(d-r) = d*j+r := by
    rw [Nat.mul_succ]
    omega
  simp_rw [he, he']
  exact mul_comm _ _

lemma coeff_drop_factor (n e : ℕ) (f : PowerSeries k) (a : k) (he : n < e) :
    PowerSeries.coeff n (f * (1 - PowerSeries.C a * PowerSeries.X ^ e)) =
      PowerSeries.coeff n f := by
  simp [mul_sub, ← mul_assoc, PowerSeries.coeff_mul_X_pow', show ¬e ≤ n by omega]

lemma partial_zero_extend (d N : ℕ) (a b : k) :
    partialGamma d 0 a b N * (1 - PowerSeries.C a * PowerSeries.X^(d*N)) =
      PowerSeries.C (1-a) *
        ((∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X^(d*(j+1)))) *
        (∏ j ∈ Finset.range N, (1 - PowerSeries.C b * PowerSeries.X^(d*(j+1))))) := by
  have hf := Finset.prod_range_succ' (fun j => (1 - PowerSeries.C a * PowerSeries.X^(d*j) : PowerSeries k)) N
  rw [Finset.prod_range_succ] at hf
  simp only [Nat.mul_zero, pow_zero, mul_one] at hf
  unfold partialGamma
  simp only [Nat.add_zero, Nat.sub_zero]
  rw [mul_assoc, mul_comm (∏ j ∈ Finset.range N, _) (1 - _), ← mul_assoc, hf]
  rw [map_sub, map_one]
  ring

/-- At residue zero, isolate the horizontal factor and compare every coefficient. -/
lemma gamma_zero_inversion (d : ℕ) (a : k) (hd : 0 < d) (ha : a ≠ 0) :
    fullGamma d 0 a⁻¹ a = PowerSeries.C (-a⁻¹) * fullGamma d 0 a a⁻¹ := by
  apply PowerSeries.ext
  intro n
  have he : n < d*(n+1) := by nlinarith
  have hfinite : partialGamma d 0 a⁻¹ a (n+1) *
      (1 - PowerSeries.C a⁻¹ * PowerSeries.X^(d*(n+1))) =
      PowerSeries.C (-a⁻¹) * (partialGamma d 0 a a⁻¹ (n+1) *
      (1 - PowerSeries.C a * PowerSeries.X^(d*(n+1)))) := by
    rw [partial_zero_extend, partial_zero_extend,
      ← mul_assoc (PowerSeries.C (-a⁻¹)) (PowerSeries.C (1-a)), ← map_mul]
    have hc : -a⁻¹ * (1-a) = 1-a⁻¹ := by field_simp; ring
    rw [hc, mul_comm (∏ j ∈ Finset.range (n+1), _) (∏ j ∈ Finset.range (n+1), _)]
  have hc := congrArg (PowerSeries.coeff n) hfinite
  rw [coeff_drop_factor _ _ _ _ he, PowerSeries.coeff_C_mul,
    coeff_drop_factor _ _ _ _ he] at hc
  simpa [fullGamma, PowerSeries.coeff_C_mul] using hc

lemma gamma_decomposition (d r : ℕ) (h : ℤ) (a : k) (hr : r < d) :
    gammaLaurent d ((r : ℤ) + (d : ℤ)*h) a =
      HahnSeries.single (-(r : ℤ)*h - (d : ℤ)*(h*(h-1)/2)) ((-a)^(-h)) *
        toLaurent k (fullGamma d r a a⁻¹) := by
  have he := (Int.ediv_emod_unique (a := (r : ℤ) + (d : ℤ)*h)
    (b := (d : ℤ)) (r := (r : ℤ)) (q := h) (by omega)).mpr
    ⟨rfl, by omega, by omega⟩
  simp [gammaLaurent, he.1, he.2]

lemma triangle_succ (h : ℤ) : (h+1)*((h+1)-1)/2 = h*(h-1)/2+h := by
  have he : (h+1)*((h+1)-1) = h*(h-1)+h*2 := by ring
  rw [he, Int.add_mul_ediv_right _ _ (by decide)]

lemma triangle_neg (h : ℤ) : (-h)*(-h-1)/2 = h*(h-1)/2+h := by
  rw [show (-h)*(-h-1) = (h+1)*((h+1)-1) by ring, triangle_succ]

lemma triangle_neg_sub (h : ℤ) : (-h-1)*((-h-1)-1)/2 = h*(h-1)/2+2*h+1 := by
  rw [show (-h-1)*((-h-1)-1) = ((h+1)+1)*(((h+1)+1)-1) by ring,
    triangle_succ, triangle_succ]
  ring

lemma gamma_translation (d : ℕ) (i : ℤ) (a : k) (hd : 0 < d) (ha : a ≠ 0) :
    gammaLaurent d (i+(d : ℤ)) a =
      -HahnSeries.single (-i) a⁻¹ * gammaLaurent d i a := by
  let h := i / (d : ℤ)
  let r := (i % (d : ℤ)).toNat
  have hr0 : 0 ≤ i % (d : ℤ) := Int.emod_nonneg _ (by omega)
  have hr : r < d := by dsimp [r]; have := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < d); omega
  have hi : i = (r : ℤ) + (d : ℤ)*h := by
    dsimp [r, h]; rw [Int.toNat_of_nonneg hr0]; exact (Int.emod_add_mul_ediv i d).symm
  have hi' : i+(d : ℤ) = (r : ℤ)+(d : ℤ)*(h+1) := by rw [hi]; ring
  rw [hi', gamma_decomposition d r (h+1) a hr, hi, gamma_decomposition d r h a hr]
  rw [← HahnSeries.single_neg, ← mul_assoc, HahnSeries.single_mul_single, triangle_succ]
  have hc : (-a)^(-(h+1)) = -a⁻¹ * (-a)^(-h) := by
    rw [show -(h+1) = -1 + -h by ring, zpow_add₀ (neg_ne_zero.mpr ha)]
    simp
  rw [hc]
  congr 2
  ring

lemma gamma_inversion (d : ℕ) (i : ℤ) (a : k) (hd : 0 < d) (ha : a ≠ 0) :
    gammaLaurent d (-i) a⁻¹ =
      -HahnSeries.single (-i) a⁻¹ * gammaLaurent d i a := by
  let h := i / (d : ℤ)
  let r := (i % (d : ℤ)).toNat
  have hr0 : 0 ≤ i % (d : ℤ) := Int.emod_nonneg _ (by omega)
  have hr : r < d := by dsimp [r]; have := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < d); omega
  have hi : i = (r : ℤ) + (d : ℤ)*h := by
    dsimp [r, h]; rw [Int.toNat_of_nonneg hr0]; exact (Int.emod_add_mul_ediv i d).symm
  by_cases hz : r = 0
  · have hi' : -i = (0 : ℕ)+(d : ℤ)*(-h) := by rw [hi, hz]; simp
    rw [hi', gamma_decomposition d 0 (-h) a⁻¹ hd, inv_inv, gamma_zero_inversion d a hd ha,
      map_mul, toLaurent, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
    rw [hi, hz, gamma_decomposition d 0 h a hd]
    rw [← HahnSeries.single_neg, ← mul_assoc, ← mul_assoc, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single, triangle_neg]
    have hc : (-a⁻¹)^(- -h) = (-a)^(-h) := by simp [← inv_neg, zpow_neg]
    rw [hc, mul_comm ((-a)^(-h)) (-a⁻¹)]
    congr 2
    ring
  · have hpos : 0 < r := by omega
    have hdr : d-r < d := by omega
    have hi' : -i = ((d-r : ℕ) : ℤ)+(d : ℤ)*(-h-1) := by
      rw [hi, Nat.cast_sub (by omega : r ≤ d)]; ring
    rw [hi', gamma_decomposition d (d-r) (-h-1) a⁻¹ hdr, inv_inv,
      gamma_reflect d r a hpos hr, hi, gamma_decomposition d r h a hr]
    rw [← HahnSeries.single_neg, ← mul_assoc, HahnSeries.single_mul_single, triangle_neg_sub]
    have hc : (-a⁻¹)^(-(-h-1)) = -a⁻¹ * (-a)^(-h) := by
      rw [show -(-h-1) = 1+h by ring, zpow_add₀ (neg_ne_zero.mpr (inv_ne_zero ha))]
      simp [← inv_neg, zpow_neg]
    rw [hc]
    congr 2
    rw [Nat.cast_sub (by omega : r ≤ d)]
    ring

theorem gamma_translation_inversion [CharZero k] (d : ℕ) (i : ℤ) (a : k)
    (hd : 0 < d) (ha : a ≠ 0) :
    (gammaLaurent d (i+(d : ℤ)) a = -HahnSeries.single (-i) a⁻¹ * gammaLaurent d i a) ∧
    (gammaLaurent d (-i) a⁻¹ = -HahnSeries.single (-i) a⁻¹ * gammaLaurent d i a) :=
  ⟨gamma_translation d i a hd ha, gamma_inversion d i a hd ha⟩

end ArithmeticThetaTateIdentities

#print axioms ArithmeticThetaTateIdentities.gamma_annular_unit
#print axioms ArithmeticThetaTateIdentities.gamma_translation_inversion
