module

public import TateGammaAnnular
public import TatePartialXStabilization

@[expose] public section

/-! The general literal annular addition identity.
The proof constructs the universal differential identity, a summable diagonal
specialization, and reflection reductions for all admissible residues. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaTateIdentities
open ArithmeticThetaFormalNorm ArithmeticThetaTateSeries
variable {k : Type u} [Field k]

lemma fullGamma_identity (d : ℕ) : fullGamma d 0 (1 : k) 1 = 0 := by
  apply PowerSeries.ext
  intro n
  simp [fullGamma, partialGamma, Finset.prod_range_succ']

lemma gamma_identity (d : ℕ) (hd : 0 < d) : gammaLaurent d 0 (1 : k) = 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, gamma_annulus d 0 1 hd]
  simp [fullGamma_identity]

lemma gamma_period_zero (d : ℕ) (h : ℤ) (hd : 0 < d) :
    gammaLaurent d ((d : ℤ)*h) (1 : k) = 0 := by
  simpa [fullGamma_identity] using gamma_decomposition d 0 h (1 : k) hd

lemma gamma_admissible_ne_zero [CharZero k] (d i : ℕ) (a : k)
    (h : Admissible d i a) : gammaLaurent d (i : ℤ) a ≠ 0 := by
  obtain ⟨hu, he⟩ := gamma_annular_unit d i a h
  rw [he]
  exact (hu.map (toLaurent k)).ne_zero

/-- The literal numerator of the source difference formula. -/
def additionNumerator (d : ℕ) (i j : ℤ) (a b : k) : LaurentSeries k :=
  -HahnSeries.single j b *
    (toLaurent k (PowerSeries.map (Int.castRingHom k)
      (ArithmeticThetaUnaryProduct.etaProduct d)))^4 *
    gammaLaurent d (i-j) (a/b) * gammaLaurent d (i+j) (a*b)

/-- Exactly the cleared equality, with no restriction on coincidence. -/
def AnnularAddition (d i j : ℕ) (a b : k) : Prop :=
  (toLaurent k (tateX d i a) - toLaurent k (tateX d j b)) *
    (gammaLaurent d (i : ℤ) a)^2 * (gammaLaurent d (j : ℤ) b)^2 =
      additionNumerator d i j a b

lemma annular_addition_iff_quotient [CharZero k] (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b) :
    AnnularAddition d i j a b ↔
      toLaurent k (tateX d i a) - toLaurent k (tateX d j b) =
        additionNumerator d i j a b /
          ((gammaLaurent d (i : ℤ) a)^2 * (gammaLaurent d (j : ℤ) b)^2) := by
  have hz := mul_ne_zero (pow_ne_zero 2 (gamma_admissible_ne_zero d i a ha))
    (pow_ne_zero 2 (gamma_admissible_ne_zero d j b hb))
  rw [eq_div_iff hz]
  simp only [AnnularAddition, mul_assoc]

lemma annular_addition_diagonal (d i : ℕ) (a : k)
    (hd : 0 < d) (ha : a ≠ 0) : AnnularAddition d i i a a := by
  simp [AnnularAddition, additionNumerator, div_self ha, gamma_identity d hd]

lemma additionNumerator_swap (d : ℕ) (i j : ℤ) (a b : k)
    (hd : 0 < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    additionNumerator d j i b a = -additionNumerator d i j a b := by
  have hi := gamma_inversion d (i-j) (a/b) hd (div_ne_zero ha hb)
  rw [neg_sub, inv_div] at hi
  have hm : HahnSeries.single i a * HahnSeries.single (-(i-j)) (a/b)⁻¹ =
      (HahnSeries.single j b : LaurentSeries k) := by
    rw [HahnSeries.single_mul_single]
    rw [show i + -(i-j) = j by omega]
    congr 1
    field_simp
  unfold additionNumerator
  rw [hi, add_comm j i, mul_comm b a]
  calc
    _ = -(HahnSeries.single i a * HahnSeries.single (-(i-j)) (a/b)⁻¹) *
        -(toLaurent k (PowerSeries.map (Int.castRingHom k)
          (ArithmeticThetaUnaryProduct.etaProduct d)))^4 *
        gammaLaurent d (i-j) (a/b) * gammaLaurent d (i+j) (a*b) := by simp only [neg_sub, inv_div]; ring
    _ = _ := by rw [hm]; ring

lemma annular_addition_swap (d i j : ℕ) (a b : k)
    (hd : 0 < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    AnnularAddition d i j a b ↔ AnnularAddition d j i b a := by
  unfold AnnularAddition
  rw [additionNumerator_swap d (i : ℤ) (j : ℤ) a b hd ha hb]
  have he : (toLaurent k (tateX d j b) - toLaurent k (tateX d i a)) *
      gammaLaurent d (j : ℤ) b ^ 2 * gammaLaurent d (i : ℤ) a ^ 2 =
      -((toLaurent k (tateX d i a) - toLaurent k (tateX d j b)) *
      gammaLaurent d (i : ℤ) a ^ 2 * gammaLaurent d (j : ℤ) b ^ 2) := by ring
  rw [he, neg_inj]


lemma xTerm_coeff_below (a : k) (e n : ℕ) (hn : n < e) :
    PowerSeries.coeff n (xTerm (monomial a e)) = 0 := by
  rw [ArithmeticThetaTateBridges.x_term_coeff a e n (by omega)]
  simp [Nat.div_eq_of_lt hn]

/-- The reflection of the finite sum differs only by its two end terms. -/
lemma partialX_reflection (d i N : ℕ) (a : k) (hi : i < d) :
    partialX d (d-i) a⁻¹ N + xTerm (monomial a (d*N+i)) =
      partialX d i a N + xTerm (monomial a⁻¹ (d*(N+1)-i)) := by
  have h₁ (r : ℕ) : d*(r+1)+(d-i) = d*((r+1)+1)-i := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have h₂ (r : ℕ) : d*(r+1)-(d-i) = d*r+i := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hf := Finset.sum_range_succ' (fun r => xTerm (monomial a (d*r+i))) N
  have hb := Finset.sum_range_succ' (fun r => xTerm (monomial a⁻¹ (d*(r+1)-i))) N
  rw [Finset.sum_range_succ] at hf hb
  simp only [Nat.mul_zero, zero_add, Nat.mul_one] at hf hb
  unfold partialX
  simp only [inv_inv, h₁, h₂, Finset.sum_add_distrib]
  linear_combination hf - hb

lemma tateX_reflection (d i : ℕ) (a : k) (hi : 0 < i) (hid : i < d) :
    tateX d (d-i) a⁻¹ = tateX d i a := by
  apply PowerSeries.ext
  intro n
  have h := congrArg (PowerSeries.coeff n) (partialX_reflection d i (n+1) a hid)
  have he₁ : n < d*(n+1)+i := by nlinarith
  have he₂ : n < d*((n+1)+1)-i := by
    have hd : 0 < d := by omega
    have hn : n+1 ≤ d*(n+1) := Nat.le_mul_of_pos_left _ hd
    rw [show d*((n+1)+1) = d*(n+1)+d from Nat.mul_succ _ _]
    omega
  simpa only [map_add, xTerm_coeff_below a _ _ he₁,
    xTerm_coeff_below a⁻¹ _ _ he₂, add_zero, tateX, PowerSeries.coeff_mk] using h

lemma xTerm_constant_inversion (a : k) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    xTerm (monomial a⁻¹ 0) = xTerm (monomial a 0) := by
  simp only [xTerm, monomial, pow_zero, mul_one, ← map_one PowerSeries.C,
    ← map_sub, PowerSeries.C_inv, ← map_pow, ← map_mul]
  congr 1
  field_simp
  ring

lemma tateX_boundary_inversion (d : ℕ) (a : k) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    tateX d 0 a⁻¹ = tateX d 0 a := by
  apply PowerSeries.ext
  intro n
  simp only [tateX, PowerSeries.coeff_mk]
  congr 1
  unfold partialX
  rw [xTerm_constant_inversion a ha ha1]
  simp only [Nat.add_zero, Nat.sub_zero, inv_inv]
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  exact add_comm _ _

lemma annular_addition_inverse (d i : ℕ) (a : k) (hi : 0 < i)
    (hid : i < d) (ha : a ≠ 0) : AnnularAddition d i (d-i) a a⁻¹ := by
  have hsum : (i : ℤ) + ((d-i : ℕ) : ℤ) = (d : ℤ)*1 := by omega
  simp only [AnnularAddition, additionNumerator, tateX_reflection d i a hi hid,
    sub_self, zero_mul, mul_inv_cancel₀ ha, hsum, gamma_period_zero d 1 (by omega),
    mul_zero]

lemma annular_addition_boundary_inverse (d : ℕ) (a : k)
    (hd : 0 < d) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    AnnularAddition d 0 0 a a⁻¹ := by
  simp [AnnularAddition, additionNumerator, tateX_boundary_inversion d a ha ha1,
    mul_inv_cancel₀ ha, gamma_identity d hd]


lemma fullGamma_eq_zero_iff (d r : ℕ) (a : k) (hr : r < d) :
    fullGamma d r a a⁻¹ = 0 ↔ r = 0 ∧ a = 1 := by
  constructor
  · intro h
    have hc := congrArg PowerSeries.constantCoeff h
    rw [gamma_constant d r a a⁻¹ hr, map_zero] at hc
    by_cases hz : r = 0
    · simp only [hz, if_true] at hc
      exact ⟨hz, (sub_eq_zero.mp hc).symm⟩
    · simp [hz] at hc
  · rintro ⟨rfl, rfl⟩
    simpa using fullGamma_identity (k := k) d

/-- Gamma vanishes exactly at period-lattice representatives. -/
lemma gamma_eq_zero_iff (d : ℕ) (i : ℤ) (a : k) (hd : 0 < d) (ha : a ≠ 0) :
    gammaLaurent d i a = 0 ↔ (d : ℤ) ∣ i ∧ a = 1 := by
  have hr0 : 0 ≤ i % (d : ℤ) := Int.emod_nonneg _ (by omega)
  have hrlt : i % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos i (by omega)
  have hr : (i % (d : ℤ)).toNat < d := by omega
  have hs : (HahnSeries.single (-(i % (d : ℤ)) * (i / (d : ℤ)) -
      (d : ℤ) * ((i / (d : ℤ)) * ((i / (d : ℤ)) - 1) / 2))
        ((-a)^(-(i / (d : ℤ)))) : LaurentSeries k) ≠ 0 :=
    HahnSeries.single_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr ha))
  unfold gammaLaurent
  rw [mul_eq_zero, or_iff_right hs]
  have hinj : Function.Injective (toLaurent k) := HahnSeries.ofPowerSeries_injective
  rw [map_eq_zero_iff _ hinj, fullGamma_eq_zero_iff d _ a hr]
  have hmod : (i % (d : ℤ)).toNat = 0 ↔ (d : ℤ) ∣ i := by
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  rw [hmod]

lemma eta_laurent_ne_zero (d : ℕ) :
    toLaurent k (PowerSeries.map (Int.castRingHom k)
      (ArithmeticThetaUnaryProduct.etaProduct d)) ≠ 0 := by
  have hu : IsUnit (PowerSeries.map (Int.castRingHom k)
      (ArithmeticThetaUnaryProduct.etaProduct d)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ArithmeticThetaUnaryProduct.etaProduct, ArithmeticThetaUnaryProduct.etaPartial]
  exact (hu.map (toLaurent k)).ne_zero

lemma additionNumerator_eq_zero_iff (d : ℕ) (i j : ℤ) (a b : k)
    (hd : 0 < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    additionNumerator d i j a b = 0 ↔
      ((d : ℤ) ∣ (i-j) ∧ a = b) ∨ ((d : ℤ) ∣ (i+j) ∧ a*b = 1) := by
  have hs : (-HahnSeries.single j b : LaurentSeries k) ≠ 0 :=
    neg_ne_zero.mpr (HahnSeries.single_ne_zero hb)
  have hp : (toLaurent k (PowerSeries.map (Int.castRingHom k)
      (ArithmeticThetaUnaryProduct.etaProduct d)))^4 ≠ 0 :=
    pow_ne_zero _ (eta_laurent_ne_zero d)
  simp only [additionNumerator, mul_eq_zero, hs, hp, false_or,
    gamma_eq_zero_iff d (i-j) (a/b) hd (div_ne_zero ha hb),
    gamma_eq_zero_iff d (i+j) (a*b) hd (mul_ne_zero ha hb), div_eq_one_iff_eq hb]


lemma annulus_dvd_sub_iff (d i j : ℕ) (hi : i < d) (hj : j < d) :
    (d : ℤ) ∣ ((i : ℤ)-(j : ℤ)) ↔ i = j := by
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ i) (by omega : (i : ℤ) < d),
    Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ j) (by omega : (j : ℤ) < d)]
  exact Nat.cast_inj

lemma annulus_dvd_add_iff (d i j : ℕ) (hi : i < d) (hj : j < d) :
    (d : ℤ) ∣ ((i : ℤ)+(j : ℤ)) ↔ (i = 0 ∧ j = 0) ∨ i+j = d := by
  constructor
  · rintro ⟨q, hq⟩
    have hd : (0 : ℤ) < d := by omega
    have hq0 : 0 ≤ q := by
      by_contra h
      have : q ≤ -1 := by omega
      nlinarith
    have hq1 : q ≤ 1 := by
      by_contra h
      have : 2 ≤ q := by omega
      nlinarith
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl
    · simp only [mul_zero] at hq
      left
      omega
    · simp only [mul_one] at hq
      right
      omega
  · rintro (⟨rfl, rfl⟩ | h)
    · simp
    · have he : (i : ℤ)+(j : ℤ) = d := by omega
      rw [he]

/-- All cases where the product numerator vanishes satisfy the full identity. -/
lemma annular_addition_of_numerator_zero (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b)
    (hz : additionNumerator d i j a b = 0) : AnnularAddition d i j a b := by
  rw [additionNumerator_eq_zero_iff d i j a b ha.1 ha.2.2.1 hb.2.2.1,
    annulus_dvd_sub_iff d i j ha.2.1 hb.2.1,
    annulus_dvd_add_iff d i j ha.2.1 hb.2.1] at hz
  rcases hz with ⟨rfl, rfl⟩ | ⟨hij, hab⟩
  · exact annular_addition_diagonal d i a ha.1 ha.2.2.1
  · have he : b = a⁻¹ := by
      apply mul_left_cancel₀ ha.2.2.1
      rw [hab, mul_inv_cancel₀ ha.2.2.1]
    subst b
    rcases hij with ⟨rfl, rfl⟩ | hij
    · exact annular_addition_boundary_inverse d a ha.1 ha.2.2.1 (ha.2.2.2 rfl)
    · have hipos : 0 < i := by have := hb.2.1; omega
      have hjeq : j = d-i := by omega
      subst j
      exact annular_addition_inverse d i a hipos ha.2.1 ha.2.2.1


/-- Coefficientwise uniqueness of degree-two theta sections.  This abstract
lemma does not assert that the literal addition defect satisfies its premises. -/
lemma degree_two_theta_unique (F : ℤ → LaurentPolynomial k) (w : kˣ)
    (hw : (w : k) ≠ 1)
    (hnegative : ∀ n : ℤ, n < 0 → F n = 0)
    (hrec : ∀ n m : ℤ, (F n).coeff (m+2) = (F (n-m)).coeff m)
    (hvalue_one : ∀ n : ℤ, LaurentPolynomial.eval₂ (RingHom.id k) 1 (F n) = 0)
    (hvalue_w : ∀ n : ℤ, LaurentPolynomial.eval₂ (RingHom.id k) w (F n) = 0) :
    ∀ n : ℤ, F n = 0 := by
  have hnat : ∀ n : ℕ, F (n : ℤ) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hlow : ∀ l : ℤ, l < (n : ℤ) → F l = 0 := by
        intro l hl
        by_cases hl0 : l < 0
        · exact hnegative l hl0
        · have he : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (by omega)
          rw [← he]
          exact ih l.toNat (by omega)
      have hleft (m : ℤ) (hm : m < 0) : (F (n : ℤ)).coeff m = 0 := by
        have hr := hrec ((n : ℤ)+m) m
        rw [hlow _ (by omega), show (n : ℤ)+m-m = n by omega] at hr
        simpa using hr.symm
      have hright (m : ℤ) (hm : 2 < m) : (F (n : ℤ)).coeff m = 0 := by
        have hr := hrec (n : ℤ) (m-2)
        rw [hlow ((n : ℤ)-(m-2)) (by omega), show m-2+2 = m by omega] at hr
        simpa using hr
      have h02 : (F (n : ℤ)).coeff 2 = (F (n : ℤ)).coeff 0 := by
        simpa using hrec (n : ℤ) 0
      have hform : F (n : ℤ) =
          AddMonoidAlgebra.single 0 ((F (n : ℤ)).coeff 0) +
          AddMonoidAlgebra.single 1 ((F (n : ℤ)).coeff 1) +
          AddMonoidAlgebra.single 2 ((F (n : ℤ)).coeff 0) := by
        apply LaurentPolynomial.ext
        intro m
        by_cases h0 : m = 0
        · subst m; simp [-LaurentPolynomial.single_eq_C_mul_T]
        by_cases h1 : m = 1
        · subst m; simp [-LaurentPolynomial.single_eq_C_mul_T]
        by_cases h2 : m = 2
        · subst m; simpa [-LaurentPolynomial.single_eq_C_mul_T] using h02
        have hz : (F (n : ℤ)).coeff m = 0 := by
          rcases lt_or_gt_of_ne h0 with hm | hm
          · exact hleft m hm
          · exact hright m (by omega)
        simp [-LaurentPolynomial.single_eq_C_mul_T,
          AddMonoidAlgebra.coeff_single, hz, h0, h1, h2]
      have h1 := hvalue_one (n : ℤ)
      have hv := hvalue_w (n : ℤ)
      rw [hform] at h1 hv
      simp only [map_add, LaurentPolynomial.single_eq_C_mul_T,
        LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply,
        zpow_ofNat, Units.val_one, Units.val_pow_eq_pow_val,
        one_pow, mul_one] at h1 hv
      have hc : (F (n : ℤ)).coeff 0 * ((w : k)-1)^2 = 0 := by
        linear_combination hv - (w : k)*h1
      have hc0 : (F (n : ℤ)).coeff 0 = 0 :=
        (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr hw))
      have hc1 : (F (n : ℤ)).coeff 1 = 0 := by simpa [hc0] using h1
      rw [hform, hc0, hc1]
      simp
  intro n
  by_cases hn : n < 0
  · exact hnegative n hn
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using hnat n.toNat


/-- The actual logarithmic derivative in the Laurent variable: z d/dz. -/
def eulerLaurent (p : LaurentPolynomial k) : LaurentPolynomial k :=
  p.coeff.sum fun m a => AddMonoidAlgebra.single m ((m : k)*a)

@[simp] lemma eulerLaurent_coeff (p : LaurentPolynomial k) (m : ℤ) :
    (eulerLaurent p).coeff m = (m : k)*p.coeff m := by
  classical
  change (∑ l ∈ p.coeff.support, AddMonoidAlgebra.single l ((l : k)*p.coeff l)).coeff m = _
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b hb hbm
    simp [hbm]
  · intro hm
    simp [Finsupp.notMem_support_iff.mp hm]

@[simp] lemma eulerLaurent_add (p q : LaurentPolynomial k) :
    eulerLaurent (p+q) = eulerLaurent p + eulerLaurent q := by
  apply LaurentPolynomial.ext
  intro m
  simp [mul_add]

@[simp] lemma eulerLaurent_zero : eulerLaurent (0 : LaurentPolynomial k) = 0 := by
  apply LaurentPolynomial.ext
  intro m
  simp

lemma eulerLaurent_mul (p q : LaurentPolynomial k) :
    eulerLaurent (p*q) = eulerLaurent p * q + p * eulerLaurent q := by
  classical
  apply LaurentPolynomial.ext
  intro m
  rw [eulerLaurent_coeff]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  simp_rw [eulerLaurent_coeff]
  have hs : ∑ x ∈ (eulerLaurent p).coeff.support,
      (x : k)*p.coeff x*q.coeff (-x+m) =
      ∑ x ∈ p.coeff.support, (x : k)*p.coeff x*q.coeff (-x+m) := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finsupp.mem_support_iff, eulerLaurent_coeff] at hx ⊢
      exact (mul_ne_zero_iff.mp hx).2
    · intro x hx hnot
      rw [← eulerLaurent_coeff, Finsupp.notMem_support_iff.mp hnot, zero_mul]
  rw [Finset.mul_sum, hs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast
  ring


@[simp] lemma eulerLaurent_smul (a : k) (p : LaurentPolynomial k) :
    eulerLaurent (a • p) = a • eulerLaurent p := by
  apply LaurentPolynomial.ext
  intro m
  simp [mul_left_comm]

@[simp] lemma eulerLaurent_one : eulerLaurent (1 : LaurentPolynomial k) = 0 := by
  apply LaurentPolynomial.ext
  intro m
  by_cases hm : m = 0 <;> simp [hm, AddMonoidAlgebra.one_def, -LaurentPolynomial.single_eq_C_mul_T]

/-- The logarithmic Laurent derivative as an actual derivation. -/
def eulerLaurentDerivation : Derivation k (LaurentPolynomial k) (LaurentPolynomial k) where
  toFun := eulerLaurent
  map_add' := eulerLaurent_add
  map_smul' := eulerLaurent_smul
  map_one_eq_zero' := eulerLaurent_one
  leibniz' p q := by simpa [smul_eq_mul, add_comm, mul_comm] using eulerLaurent_mul p q

/-- Coefficientwise extension; the formal q parameter is held constant. -/
def eulerSeries (f : PowerSeries (LaurentPolynomial k)) : PowerSeries (LaurentPolynomial k) :=
  PowerSeries.mk fun n => eulerLaurent (PowerSeries.coeff n f)

@[simp] lemma eulerSeries_coeff (f : PowerSeries (LaurentPolynomial k)) (n : ℕ) :
    PowerSeries.coeff n (eulerSeries f) = eulerLaurent (PowerSeries.coeff n f) := by
  simp [eulerSeries]

lemma eulerSeries_add (f g : PowerSeries (LaurentPolynomial k)) :
    eulerSeries (f+g) = eulerSeries f + eulerSeries g := by
  ext n m
  simp

lemma eulerSeries_mul (f g : PowerSeries (LaurentPolynomial k)) :
    eulerSeries (f*g) = eulerSeries f*g + f*eulerSeries g := by
  apply PowerSeries.ext
  intro n
  rw [eulerSeries_coeff, PowerSeries.coeff_mul]
  change eulerLaurentDerivation (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g) = _
  rw [map_sum]
  simp only [show ∀ p : LaurentPolynomial k, eulerLaurentDerivation p = eulerLaurent p from
    fun _ => rfl, eulerLaurent_mul, map_add, PowerSeries.coeff_mul, eulerSeries_coeff,
    Finset.sum_add_distrib]


lemma eulerSeries_smul (a : k) (f : PowerSeries (LaurentPolynomial k)) :
    eulerSeries (a • f) = a • eulerSeries f := by
  ext n m
  simp

lemma eulerSeries_one : eulerSeries (1 : PowerSeries (LaurentPolynomial k)) = 0 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0 <;> simp [hn]

def eulerSeriesDerivation :
    Derivation k (PowerSeries (LaurentPolynomial k)) (PowerSeries (LaurentPolynomial k)) where
  toFun := eulerSeries
  map_add' := eulerSeries_add
  map_smul' := eulerSeries_smul
  map_one_eq_zero' := eulerSeries_one
  leibniz' f g := by simpa [smul_eq_mul, add_comm, mul_comm] using eulerSeries_mul f g

@[simp] lemma eulerSeriesDerivation_apply (f : PowerSeries (LaurentPolynomial k)) :
    eulerSeriesDerivation f = eulerSeries f := rfl

lemma eulerSeries_monomial (p : LaurentPolynomial k) (e : ℕ) :
    eulerSeries (PowerSeries.C p*PowerSeries.X^e) =
      PowerSeries.C (eulerLaurent p)*PowerSeries.X^e := by
  apply PowerSeries.ext
  intro n
  by_cases he : e ≤ n
  · simp only [eulerSeries_coeff, PowerSeries.coeff_mul_X_pow', if_pos he,
      PowerSeries.coeff_C]
    split_ifs <;> simp
  · simp [PowerSeries.coeff_mul_X_pow', he]

@[simp] lemma eulerLaurent_T (m : ℤ) :
    eulerLaurent (LaurentPolynomial.T m : LaurentPolynomial k) =
      (m : k) • LaurentPolynomial.T m := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : m = n <;> simp [hn]

@[simp] lemma eulerLaurent_C (a : k) : eulerLaurent (LaurentPolynomial.C a) = 0 := by
  apply LaurentPolynomial.ext
  intro m
  by_cases hm : m = 0 <;> simp [hm]

/-- Evaluate the actual Laurent variable in every q coefficient. -/
def evalLaurentSeries (w : kˣ) : PowerSeries (LaurentPolynomial k) →+* PowerSeries k :=
  PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id k) w)

@[simp] lemma evalLaurentSeries_coeff (w : kˣ) (f : PowerSeries (LaurentPolynomial k)) (n : ℕ) :
    PowerSeries.coeff n (evalLaurentSeries w f) =
      LaurentPolynomial.eval₂ (RingHom.id k) w (PowerSeries.coeff n f) := by
  simp [evalLaurentSeries]

@[simp] lemma evalLaurentSeries_monomial (w : kˣ) (p : LaurentPolynomial k) (e : ℕ) :
    evalLaurentSeries w (PowerSeries.C p*PowerSeries.X^e) =
      PowerSeries.C (LaurentPolynomial.eval₂ (RingHom.id k) w p)*PowerSeries.X^e := by
  simp [evalLaurentSeries]

/-- The literal universal annular-zero gamma, with its Laurent variable retained. -/
def universalGamma (d : ℕ) : PowerSeries (LaurentPolynomial k) :=
  fullGamma d 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))

/-- Denominator-cleared negative second logarithmic derivative. -/
def secondLogNumerator {A : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (f : A) : A := (D f)^2 - f*D (D f)

lemma secondLogNumerator_mul {A : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (f g : A) :
    secondLogNumerator D (f*g) =
      g^2*secondLogNumerator D f + f^2*secondLogNumerator D g := by
  simp only [secondLogNumerator, Derivation.leibniz, smul_eq_mul, map_add]
  ring

lemma secondLogNumerator_factor {A : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (v : A) (hv : D v = v ∨ D v = -v) :
    secondLogNumerator D (1-v) = v := by
  rcases hv with hv | hv <;>
    simp only [secondLogNumerator, map_sub, Derivation.map_one_eq_zero, hv,
      zero_sub, map_neg, neg_neg] <;> ring

lemma secondLogNumerator_prod {A I : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (s : Finset I) (f x : I → A)
    (hx : ∀ i ∈ s, secondLogNumerator D (f i) = (f i)^2*x i) :
    secondLogNumerator D (∏ i ∈ s, f i) = (∏ i ∈ s, f i)^2 * ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [secondLogNumerator, Derivation.map_one_eq_zero]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, secondLogNumerator_mul,
      hx i (Finset.mem_insert_self i s), ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]
    ring

/-- Finite logarithmic derivative identity for the actual geometric factors. -/
lemma finite_log_product {K I : Type*} [Field K] [Algebra k K]
    (D : Derivation k K K) (s : Finset I) (v : I → K)
    (hv : ∀ i ∈ s, D (v i) = v i ∨ D (v i) = -v i)
    (hne : ∀ i ∈ s, v i ≠ 1) :
    secondLogNumerator D (∏ i ∈ s, (1-v i)) =
      (∏ i ∈ s, (1-v i))^2 * ∑ i ∈ s, v i / (1-v i)^2 := by
  apply secondLogNumerator_prod
  intro i hi
  rw [secondLogNumerator_factor D (v i) (hv i hi)]
  have hz : (1-v i)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (hne i hi).symm)
  exact (mul_div_cancel₀ (v i) hz).symm.trans (by ring)


/-- Both positive-degree tails of the gamma product. -/
def gammaTailFinite {R : Type*} [CommRing R] (d N : ℕ) (a b : R) : PowerSeries R :=
  (∏ r ∈ Finset.range N, (1-PowerSeries.C a*PowerSeries.X^(d*(r+1)))) *
  (∏ r ∈ Finset.range N, (1-PowerSeries.C b*PowerSeries.X^(d*(r+1))))

lemma partialGamma_zero_extend {R : Type*} [CommRing R] (d N : ℕ) (a b : R) :
    partialGamma d 0 a b N * (1-PowerSeries.C a*PowerSeries.X^(d*N)) =
      PowerSeries.C (1-a)*gammaTailFinite d N a b := by
  have hf := Finset.prod_range_succ'
    (fun r => (1-PowerSeries.C a*PowerSeries.X^(d*r) : PowerSeries R)) N
  rw [Finset.prod_range_succ] at hf
  simp only [Nat.mul_zero, pow_zero, mul_one] at hf
  unfold partialGamma gammaTailFinite
  simp only [Nat.add_zero, Nat.sub_zero]
  rw [mul_assoc, mul_comm (∏ r ∈ Finset.range N, _) (1-_), ← mul_assoc, hf]
  rw [map_sub, map_one]
  ring

lemma coeff_drop_factor_ring {R : Type*} [CommRing R] (f : PowerSeries R)
    (a : R) (n e : ℕ) (hn : n < e) :
    PowerSeries.coeff n (f*(1-PowerSeries.C a*PowerSeries.X^e)) =
      PowerSeries.coeff n f := by
  simp [mul_sub, ← mul_assoc, PowerSeries.coeff_mul_X_pow', show ¬e ≤ n by omega]

lemma eval_gammaTailFinite (d N : ℕ) :
    evalLaurentSeries (1 : kˣ)
      (gammaTailFinite d N (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) =
      (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaPartial d N))^2 := by
  simp [gammaTailFinite, evalLaurentSeries, ArithmeticThetaUnaryProduct.etaPartial, pow_two]

lemma mapped_etaPartial_coeff (d n N : ℕ) (hd : 0 < d) (hn : n ≤ N) :
    PowerSeries.coeff n
      (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaPartial d N)) =
    PowerSeries.coeff n
      (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d)) := by
  simp only [PowerSeries.coeff_map, ArithmeticThetaUnaryProduct.etaProduct,
    PowerSeries.coeff_mk]
  rw [ArithmeticThetaUnaryProduct.etaPartial_stable d hd n N hn]

/-- Exact horizontal first derivative of the literal universal gamma product. -/
lemma universalGamma_horizontal_derivative (d : ℕ) (hd : 0 < d) :
    evalLaurentSeries (1 : kˣ) (eulerSeries (universalGamma d)) =
      -(PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d))^2 := by
  apply PowerSeries.ext
  intro n
  have he : n < d*(n+1) := by nlinarith
  have hc := congrArg (PowerSeries.coeff n)
    (partialGamma_zero_extend d (n+1)
      (LaurentPolynomial.T 1 : LaurentPolynomial k) (LaurentPolynomial.T (-1)))
  rw [coeff_drop_factor_ring _ _ _ _ he, PowerSeries.coeff_C_mul] at hc
  have hD := congrArg
    (fun p : LaurentPolynomial k => LaurentPolynomial.eval₂ (RingHom.id k) 1 (eulerLaurent p)) hc
  have hDfactor : eulerLaurent (1-LaurentPolynomial.T 1 : LaurentPolynomial k) =
      -LaurentPolynomial.T 1 := by
    change eulerLaurentDerivation (1-LaurentPolynomial.T 1) = _
    simp only [map_sub, Derivation.map_one_eq_zero, zero_sub]
    change -eulerLaurent (LaurentPolynomial.T 1 : LaurentPolynomial k) = _
    simp
  rw [eulerLaurent_mul, hDfactor] at hD
  simp only [map_add, map_mul, map_sub, map_neg, map_one,
    LaurentPolynomial.eval₂_T, zpow_one, Units.val_one,
    sub_self, zero_mul, add_zero, neg_one_mul] at hD
  rw [evalLaurentSeries_coeff, eulerSeries_coeff]
  simp only [universalGamma, fullGamma, PowerSeries.coeff_mk]
  rw [hD]
  rw [← evalLaurentSeries_coeff, eval_gammaTailFinite, map_neg]
  congr 1
  simp only [pow_two]
  apply coeff_mul_congr
  · intro r hr
    exact mapped_etaPartial_coeff d r (n+1) hd (by omega)
  · intro r hr
    exact mapped_etaPartial_coeff d r (n+1) hd (by omega)


lemma map_fullGamma {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d i : ℕ) (a b : R) :
    PowerSeries.map f (fullGamma d i a b) = fullGamma d i (f a) (f b) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, fullGamma, PowerSeries.coeff_mk]
  rw [← PowerSeries.coeff_map]
  simp [partialGamma]

lemma eval_universalGamma (d : ℕ) (w : kˣ) :
    evalLaurentSeries w (universalGamma d) = fullGamma d 0 (w : k) (w : k)⁻¹ := by
  rw [evalLaurentSeries, universalGamma, map_fullGamma]
  simp

lemma eval_universalGamma_one (d : ℕ) :
    evalLaurentSeries (1 : kˣ) (universalGamma d) = 0 := by
  rw [eval_universalGamma]
  simp [fullGamma_identity]

/-- The leading horizontal normalization is the fourth Euler power. -/
lemma universalGamma_horizontal_numerator (d : ℕ) (hd : 0 < d) :
    evalLaurentSeries (1 : kˣ)
      (secondLogNumerator eulerSeriesDerivation (universalGamma d)) =
        (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d))^4 := by
  rw [secondLogNumerator, map_sub, map_pow, map_mul, eval_universalGamma_one]
  simp only [eulerSeriesDerivation_apply, universalGamma_horizontal_derivative d hd,
    zero_mul, sub_zero, neg_sq]
  ring


lemma xTerm_clear (v : PowerSeries k) (hv : PowerSeries.constantCoeff v ≠ 1) :
    (1-v)^2*xTerm v = v := by
  have hunit : PowerSeries.constantCoeff (1-v) ≠ 0 := by
    simpa using sub_ne_zero.mpr hv.symm
  calc
    _ = v*((1-v)*(1-v)⁻¹)^2 := by unfold xTerm; ring
    _ = v := by rw [PowerSeries.mul_inv_cancel _ hunit]; simp

lemma map_secondLogNumerator_prod {A B I : Type*} [CommRing A] [CommRing B] [Algebra k A]
    (D : Derivation k A A) (φ : A →+* B) (s : Finset I) (f : I → A) (x : I → B)
    (hx : ∀ i ∈ s, φ (secondLogNumerator D (f i)) = (φ (f i))^2*x i) :
    φ (secondLogNumerator D (∏ i ∈ s, f i)) =
      (∏ i ∈ s, φ (f i))^2 * ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [secondLogNumerator, Derivation.map_one_eq_zero]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      secondLogNumerator_mul, map_add, map_mul, map_pow, map_mul, map_pow,
      map_prod, hx i (Finset.mem_insert_self i s),
      ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]
    ring

/-- One Laurent monomial times a nonnegative power of the formal parameter. -/
def universalMonomial (m : ℤ) (e : ℕ) : PowerSeries (LaurentPolynomial k) :=
  PowerSeries.C (LaurentPolynomial.T m)*PowerSeries.X^e

lemma euler_universalMonomial (m : ℤ) (e : ℕ) :
    eulerSeriesDerivation (universalMonomial m e : PowerSeries (LaurentPolynomial k)) =
      (m : k) • universalMonomial m e := by
  change eulerSeries (PowerSeries.C (LaurentPolynomial.T m)*PowerSeries.X^e) = _
  rw [eulerSeries_monomial, eulerLaurent_T]
  apply PowerSeries.ext
  intro n
  by_cases he : e ≤ n <;> by_cases hz : n-e = 0 <;>
    simp [universalMonomial, PowerSeries.coeff_mul_X_pow', he, PowerSeries.coeff_C, hz]

lemma eval_universalMonomial (w : kˣ) (m : ℤ) (e : ℕ) :
    evalLaurentSeries w (universalMonomial m e) = monomial ((w^m).val) e := by
  simp [universalMonomial, monomial]

lemma eval_finite_log_factors {I : Type*} (w : kˣ) (s : Finset I)
    (m : I → ℤ) (e : I → ℕ)
    (hm : ∀ i ∈ s, m i = 1 ∨ m i = -1)
    (he : ∀ i ∈ s, e i = 0 → (w^(m i)).val ≠ 1) :
    evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation
      (∏ i ∈ s, (1-universalMonomial (m i) (e i)))) =
      (∏ i ∈ s, (1-monomial (w^(m i)).val (e i)))^2 *
        ∑ i ∈ s, xTerm (monomial (w^(m i)).val (e i)) := by
  have hmap (i : I) : evalLaurentSeries w
      (1-universalMonomial (m i) (e i)) = 1-monomial (w^(m i)).val (e i) := by
    rw [map_sub, map_one, eval_universalMonomial]
  simp_rw [← hmap]
  apply map_secondLogNumerator_prod
  intro i hi
  have hv : eulerSeriesDerivation (universalMonomial (m i) (e i) : PowerSeries (LaurentPolynomial k)) =
      universalMonomial (m i) (e i) ∨
      eulerSeriesDerivation (universalMonomial (m i) (e i) : PowerSeries (LaurentPolynomial k)) =
      -universalMonomial (m i) (e i) := by
    rw [euler_universalMonomial]
    rcases hm i hi with hm | hm <;> simp [hm]
  rw [secondLogNumerator_factor _ _ hv, eval_universalMonomial, hmap]
  symm
  apply xTerm_clear
  by_cases hz : e i = 0
  · simpa [monomial, hz] using he i hi hz
  · simp [monomial, hz]

/-- The unnormalized finite annular sum corresponding to the exact finite product. -/
def rawPartialX (d i N : ℕ) (a : k) : PowerSeries k :=
  (∑ r ∈ Finset.range N, xTerm (monomial a (d*r+i))) +
  (∑ r ∈ Finset.range N, xTerm (monomial a⁻¹ (d*(r+1)-i)))

lemma eval_partialGamma_log (d i N : ℕ) (w : kˣ) (hi : i < d)
    (hw : i = 0 → (w : k) ≠ 1) :
    evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation
      (partialGamma d i (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N)) =
      (partialGamma d i (w : k) (w : k)⁻¹ N)^2 * rawPartialX d i N (w : k) := by
  have hp := eval_finite_log_factors w (Finset.range N) (fun _ => (1 : ℤ))
    (fun r => d*r+i) (by simp) (by
      intro r hr hz
      have hi0 : i = 0 := by omega
      simpa using hw hi0)
  have hn := eval_finite_log_factors w (Finset.range N) (fun _ => (-1 : ℤ))
    (fun r => d*(r+1)-i) (by simp) (by
      intro r hr hz
      have he : 0 < d*(r+1)-i := inverse_positive d i r (by omega) hi
      omega)
  simp only [zpow_one, zpow_neg_one, Units.val_inv_eq_inv_val] at hp hn
  simp only [partialGamma, secondLogNumerator_mul, map_add, map_mul, map_pow]
  dsimp only [universalMonomial] at hp hn
  rw [hp, hn]
  simp only [rawPartialX, evalLaurentSeries, map_prod, map_sub, map_one,
    map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one, Units.val_inv_eq_inv_val]
  unfold monomial
  ring


/-- The actual unnormalized annular sum, by stable coefficients. -/
def rawAnnularX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (rawPartialX d i (n+1) a)

lemma rawPartialX_coeff_stable (d i n N : ℕ) (a : k) (hi : i < d) (hN : n < N) :
    PowerSeries.coeff n (rawPartialX d i N a) = PowerSeries.coeff n (rawAnnularX d i a) := by
  have hd : 0 < d := by omega
  have hf (r : ℕ) (hr : n+1 ≤ r) : n < d*r+i := by
    have := Nat.le_mul_of_pos_left r hd
    omega
  have hb (r : ℕ) (hr : n+1 ≤ r) : n < d*(r+1)-i := by
    have := Nat.le_mul_of_pos_left r hd
    rw [Nat.mul_succ]
    omega
  simp only [rawAnnularX, PowerSeries.coeff_mk, rawPartialX, map_add, map_sum]
  congr 1
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ N))
    intro r hr hnot
    exact xTerm_coeff_below a _ _ (hf r (by simpa using hnot))
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ N))
    intro r hr hnot
    exact xTerm_coeff_below a⁻¹ _ _ (hb r (by simpa using hnot))

lemma partialGamma_stable_ring {R : Type*} [CommRing R] (d i n N : ℕ) (a b : R)
    (hi : i < d) (hN : n < N) :
    PowerSeries.coeff n (partialGamma d i a b N) = PowerSeries.coeff n (fullGamma d i a b) := by
  simp only [fullGamma, PowerSeries.coeff_mk]
  have hn : n+1 ≤ N := hN
  induction N, hn using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [partial_step d i a b n N (by omega) hi (by omega), ih (by omega)]

set_option maxHeartbeats 800000 in
lemma secondLog_coeff_congr (n : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (h : ∀ r ≤ n, PowerSeries.coeff r f = PowerSeries.coeff r g) :
    PowerSeries.coeff n (secondLogNumerator eulerSeriesDerivation f) =
      PowerSeries.coeff n (secondLogNumerator eulerSeriesDerivation g) := by
  simp only [secondLogNumerator, pow_two, map_sub]
  congr 1
  · apply coeff_mul_congr <;> intro r hr <;>
      simp only [eulerSeriesDerivation_apply, eulerSeries_coeff, h r hr]
  · apply coeff_mul_congr
    · exact h
    · intro r hr
      simp only [eulerSeriesDerivation_apply, eulerSeries_coeff, h r hr]

set_option maxHeartbeats 800000 in
/-- All-coefficient product/sum bridge, prior to the two-point theta identity. -/
lemma eval_fullGamma_log (d i : ℕ) (w : kˣ) (hi : i < d)
    (hw : i = 0 → (w : k) ≠ 1) :
    evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation
      (fullGamma d i (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))) =
      (fullGamma d i (w : k) (w : k)⁻¹)^2 * rawAnnularX d i (w : k) := by
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff n (evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation
        (partialGamma d i (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) (n+1)))) := by
      exact congrArg (LaurentPolynomial.eval₂ (RingHom.id k) w)
        (secondLog_coeff_congr n _ _ (fun r hr =>
          (partialGamma_stable_ring d i r (n+1) _ _ hi (by omega)).symm))
    _ = PowerSeries.coeff n ((partialGamma d i (w : k) (w : k)⁻¹ (n+1))^2 *
        rawPartialX d i (n+1) (w : k)) := by
      exact congrArg (PowerSeries.coeff n) (eval_partialGamma_log d i (n+1) w hi hw)
    _ = _ := by
      apply coeff_mul_congr
      · intro r hr
        simp only [pow_two]
        apply coeff_mul_congr <;> intro l hl <;>
          exact partialGamma_stable_ring d i l (n+1) _ _ hi (by omega)
      · intro r hr
        exact rawPartialX_coeff_stable d i r (n+1) (w : k) hi (by omega)

lemma rawPartialX_compare (d i N : ℕ) (a : k) :
    rawPartialX d i N a + xTerm (monomial a (d*N+i)) =
      partialX d i a N + 2*∑ r ∈ Finset.range N,
        PowerSeries.C ((r+1 : ℕ) : k)*monomial 1 (d*(r+1)) *
          (1-monomial 1 (d*(r+1)))⁻¹ := by
  have hf := Finset.sum_range_succ' (fun r => xTerm (monomial a (d*r+i))) N
  rw [Finset.sum_range_succ] at hf
  simp only [Nat.mul_zero, zero_add] at hf
  unfold rawPartialX partialX
  rw [Finset.sum_add_distrib]
  linear_combination hf

lemma rawAnnularX_difference (d i j : ℕ) (a b : k) (hd : 0 < d) :
    rawAnnularX d i a - rawAnnularX d j b = tateX d i a - tateX d j b := by
  apply PowerSeries.ext
  intro n
  have hf := congrArg (PowerSeries.coeff n) (rawPartialX_compare d i (n+1) a)
  have hg := congrArg (PowerSeries.coeff n) (rawPartialX_compare d j (n+1) b)
  have hi : n < d*(n+1)+i := by nlinarith
  have hj : n < d*(n+1)+j := by nlinarith
  rw [map_add, xTerm_coeff_below _ _ _ hi, add_zero, map_add] at hf
  rw [map_add, xTerm_coeff_below _ _ _ hj, add_zero, map_add] at hg
  simp only [map_sub, rawAnnularX, tateX, PowerSeries.coeff_mk]
  linear_combination hf - hg

/-- Literal Tate differences are exactly differences of the two logarithmic numerators. -/
lemma literal_difference_log_bridge (d i j : ℕ) (a b : kˣ)
    (hi : i < d) (hj : j < d) (ha : i = 0 → (a : k) ≠ 1) (hb : j = 0 → (b : k) ≠ 1) :
    evalLaurentSeries a (secondLogNumerator eulerSeriesDerivation
        (fullGamma d i (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))) *
        (fullGamma d j (b : k) (b : k)⁻¹)^2 -
      evalLaurentSeries b (secondLogNumerator eulerSeriesDerivation
        (fullGamma d j (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))) *
        (fullGamma d i (a : k) (a : k)⁻¹)^2 =
      (tateX d i (a : k)-tateX d j (b : k)) *
        (fullGamma d i (a : k) (a : k)⁻¹)^2 * (fullGamma d j (b : k) (b : k)⁻¹)^2 := by
  rw [eval_fullGamma_log d i a hi ha, eval_fullGamma_log d j b hj hb,
    ← rawAnnularX_difference d i j (a : k) (b : k) (by omega)]
  ring

/-- The Laurent variable as a unit, retaining its specified inverse. -/
def laurentVariable : (LaurentPolynomial k)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

@[simp] lemma laurentVariable_zpow (m : ℤ) :
    ((laurentVariable (k := k))^m).val = LaurentPolynomial.T m := by
  cases m with
  | ofNat n => simp [laurentVariable, LaurentPolynomial.T_pow]
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial k)^(n+1) = _
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega

/-- Cast the integral Jacobi product and replace its Laurent variable by -z. -/
def signedJacobiCast : LaurentPolynomial ℤ →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (Int.castRingHom k)) (-laurentVariable)

@[simp] lemma signedJacobiCast_T (m : ℤ) :
    signedJacobiCast (LaurentPolynomial.T m) =
      LaurentPolynomial.C ((-1 : k)^m)*LaurentPolynomial.T m := by
  simp only [signedJacobiCast, LaurentPolynomial.eval₂_T]
  have he : (-laurentVariable (k := k)) =
      (Units.map LaurentPolynomial.C.toMonoidHom (-1 : kˣ))*laurentVariable := by
    ext
    simp [laurentVariable]
  rw [he, mul_zpow, Units.val_mul, laurentVariable_zpow]
  rw [← map_zpow]
  simp only [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]
  rfl

@[simp] lemma signedJacobiCast_C (a : ℤ) :
    signedJacobiCast (LaurentPolynomial.C a) = LaurentPolynomial.C (a : k) := by
  simp [signedJacobiCast]

lemma signedJacobiCast_coeff (p : LaurentPolynomial ℤ) (m : ℤ) :
    (signedJacobiCast p : LaurentPolynomial k).coeff m = (-1 : k)^m*(p.coeff m : k) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | C_mul_T n a =>
    simp only [map_mul, signedJacobiCast_T, signedJacobiCast_C]
    rw [← mul_assoc, ← map_mul]
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = m
    · subst n
      simp only [if_true]
      ring
    · simp only [hn, if_false, Int.cast_zero, mul_zero]

lemma signedJacobi_finite (N : ℕ) :
    PowerSeries.map (signedJacobiCast (k := k))
      (ArithmeticThetaDurfee.normalizedFiniteProduct N) =
    PowerSeries.map (LaurentPolynomial.C.comp (Int.castRingHom k))
      (ArithmeticThetaUnaryProduct.etaPartial 1 N) *
      (PowerSeries.C (1-LaurentPolynomial.T 1) *
        gammaTailFinite 1 N (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) := by
  simp only [ArithmeticThetaDurfee.normalizedFiniteProduct, map_mul, map_add,
    map_one, PowerSeries.map_C, signedJacobiCast_T, zpow_one, zpow_neg_one,
    inv_neg, inv_one, map_neg, neg_mul, one_mul, map_prod, map_sub, map_pow,
    PowerSeries.map_X, ← sub_eq_add_neg]
  simp only [ArithmeticThetaUnaryProduct.etaPartial, gammaTailFinite, one_mul,
    map_prod, map_sub, map_one, map_pow, PowerSeries.map_X,
    Finset.prod_mul_distrib]
  ring

/-- The signed Jacobi product equals the actual gamma product times its Euler factor. -/
lemma signedJacobi_full :
    PowerSeries.map (signedJacobiCast (k := k)) ArithmeticThetaDurfee.fullProduct =
      PowerSeries.map (LaurentPolynomial.C.comp (Int.castRingHom k))
        (ArithmeticThetaUnaryProduct.etaProduct 1) * universalGamma 1 := by
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff n (PowerSeries.map (signedJacobiCast (k := k))
        (ArithmeticThetaDurfee.normalizedFiniteProduct (n+1))) := by
      simp only [PowerSeries.coeff_map, ArithmeticThetaDurfee.fullProduct, PowerSeries.coeff_mk]
      rw [ArithmeticThetaDurfee.normalized_partial_stable n (n+1) (by omega)]
    _ = _ := by
      rw [signedJacobi_finite]
      apply coeff_mul_congr
      · intro r hr
        simp only [PowerSeries.coeff_map, ArithmeticThetaUnaryProduct.etaProduct,
          PowerSeries.coeff_mk]
        rw [ArithmeticThetaUnaryProduct.etaPartial_stable 1 (by omega) r (n+1) (by omega)]
      · intro r hr
        have h := congrArg (PowerSeries.coeff r)
          (partialGamma_zero_extend 1 (n+1)
            (LaurentPolynomial.T 1 : LaurentPolynomial k) (LaurentPolynomial.T (-1)))
        rw [coeff_drop_factor_ring _ _ _ _ (by omega)] at h
        rw [← h]
        exact partialGamma_stable_ring 1 0 r (n+1) _ _ (by omega) (by omega)

/-- Exact double coefficients of the normalized literal universal gamma. -/
lemma normalized_universalGamma_coeff (n : ℕ) (m : ℤ) :
    (PowerSeries.coeff n
      (PowerSeries.map (LaurentPolynomial.C.comp (Int.castRingHom k))
        (ArithmeticThetaUnaryProduct.etaProduct 1) * universalGamma 1)).coeff m =
      if m*(m-1) = 2*(n : ℤ) then (-1 : k)^m else 0 := by
  rw [← signedJacobi_full, PowerSeries.coeff_map, signedJacobiCast_coeff,
    ArithmeticThetaDurfee.full_jacobi_double_coefficient]
  split_ifs <;> simp


/-- Nonnegative integral triangular exponent for every Laurent exponent. -/
def triangularIndex (m : ℤ) : ℕ := (m*(m-1)/2).toNat

lemma triangular_nonneg (m : ℤ) : 0 ≤ m*(m-1) := by
  by_cases hm : m ≤ 0
  · nlinarith
  · have : 1 ≤ m := by omega
    nlinarith

lemma triangularIndex_twice (m : ℤ) : 2*(triangularIndex m : ℤ) = m*(m-1) := by
  obtain ⟨r, hr⟩ := Int.even_mul_pred_self m
  have hp := triangular_nonneg m
  unfold triangularIndex
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hp (by omega))]
  omega

lemma triangularIndex_shift (m : ℤ) :
    (triangularIndex (m+1) : ℤ) = triangularIndex m + m := by
  have h := triangularIndex_twice m
  have h' := triangularIndex_twice (m+1)
  nlinarith

/-- A double coefficient, extended by zero to negative formal degrees. -/
def integerCoeff (f : PowerSeries (LaurentPolynomial k)) (n m : ℤ) : k :=
  if n < 0 then 0 else (PowerSeries.coeff n.toNat f).coeff m

/-- The actual normalized universal theta product. -/
def normalizedTheta : PowerSeries (LaurentPolynomial k) :=
  PowerSeries.map (LaurentPolynomial.C.comp (Int.castRingHom k))
    (ArithmeticThetaUnaryProduct.etaProduct 1) * universalGamma 1

lemma normalizedTheta_coeff (n : ℕ) (m : ℤ) :
    (PowerSeries.coeff n (normalizedTheta (k := k))).coeff m =
      if triangularIndex m = n then (-1 : k)^m else 0 := by
  rw [normalizedTheta, normalized_universalGamma_coeff]
  have ht := triangularIndex_twice m
  have he : m*(m-1) = 2*(n : ℤ) ↔ triangularIndex m = n := by omega
  simp only [he]

lemma normalizedTheta_integerCoeff (n m : ℤ) :
    integerCoeff (normalizedTheta (k := k)) n m =
      if (triangularIndex m : ℤ) = n then (-1 : k)^m else 0 := by
  unfold integerCoeff
  by_cases hn : n < 0
  · simp [hn, show ¬(triangularIndex m : ℤ) = n by omega]
  · rw [if_neg hn, normalizedTheta_coeff]
    have he : triangularIndex m = n.toNat ↔ (triangularIndex m : ℤ) = n := by omega
    simp only [he]

/-- Functional recurrence of the actual normalized gamma product. -/
lemma normalizedTheta_recurrence (n m : ℤ) :
    integerCoeff (normalizedTheta (k := k)) n (m+1) =
      -integerCoeff normalizedTheta (n-m) m := by
  simp only [normalizedTheta_integerCoeff, triangularIndex_shift]
  have he : (triangularIndex m : ℤ)+m = n ↔ (triangularIndex m : ℤ) = n-m := by omega
  simp only [he]
  split_ifs
  · rw [zpow_add₀ (by simp : (-1 : k) ≠ 0)]
    simp
  · simp

lemma laurent_coeff_mul_finsum (p q : LaurentPolynomial k) (m : ℤ) :
    (p*q).coeff m = ∑ᶠ l : ℤ, p.coeff l*q.coeff (m-l) := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (s := p.coeff.support)]
  · simpa [Finsupp.sum, sub_eq_add_neg, add_comm] using
      (AddMonoidAlgebra.coeff_mul_apply_left p q m)
  · intro l hl
    simp only [Function.mem_support, Finset.mem_coe, Finsupp.mem_support_iff] at hl ⊢
    exact fun hp => hl (by simp [hp])

/-- Finite quadratic convolution of two genuine theta coefficient sequences. -/
def thetaKernel (n m : ℤ) (W : ℤ → ℤ → k) : k :=
  ∑ᶠ p : ℤ, if ((triangularIndex p + triangularIndex (m-p) : ℕ) : ℤ) = n
    then W p (m-p)*(-1 : k)^m else 0

lemma thetaKernel_negative (n m : ℤ) (W : ℤ → ℤ → k) (hn : n < 0) :
    thetaKernel n m W = 0 := by
  unfold thetaKernel
  have he (p : ℤ) : ¬((triangularIndex p + triangularIndex (m-p) : ℕ) : ℤ) = n := by omega
  simp only [he, if_false, finsum_zero]

lemma thetaKernel_shift (n m : ℤ) (W : ℤ → ℤ → k)
    (hW : ∀ p q : ℤ, W (p+1) (q+1) = W p q) :
    thetaKernel n (m+2) W = thetaKernel (n-m) m W := by
  unfold thetaKernel
  apply finsum_eq_of_bijective (fun p : ℤ => p-1)
    (by
      constructor
      · intro a b h
        dsimp at h
        omega
      · intro a
        exact ⟨a+1, by dsimp; omega⟩)
  intro p
  have h1 := triangularIndex_shift (p-1)
  have h2 := triangularIndex_shift (m-(p-1))
  have he : ((triangularIndex p + triangularIndex (m+2-p) : ℕ) : ℤ) = n ↔
      ((triangularIndex (p-1) + triangularIndex (m-(p-1)) : ℕ) : ℤ) = n-m := by
    push_cast
    rw [show p = (p-1)+1 by omega] at h1
    have hp := triangularIndex_twice p
    have hq := triangularIndex_twice (m+2-p)
    have hp' := triangularIndex_twice (p-1)
    have hq' := triangularIndex_twice (m-(p-1))
    constructor <;> intro h <;> nlinarith
  simp only [he]
  split_ifs
  · have hw := hW (p-1) (m-(p-1))
    rw [show p-1+1 = p by omega, show m-(p-1)+1 = m+2-p by omega] at hw
    rw [hw, zpow_add₀ (by simp : (-1 : k) ≠ 0)]
    norm_num
  · rfl

lemma theta_product_coeff (f g : PowerSeries (LaurentPolynomial k))
    (A B : ℤ → k)
    (hf : ∀ r p, (PowerSeries.coeff r f).coeff p =
      if triangularIndex p = r then A p * (-1 : k)^p else 0)
    (hg : ∀ r p, (PowerSeries.coeff r g).coeff p =
      if triangularIndex p = r then B p * (-1 : k)^p else 0)
    (n : ℕ) (m : ℤ) :
    (PowerSeries.coeff n (f*g)).coeff m = thetaKernel n m (fun p q => A p*B q) := by
  classical
  rw [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [laurent_coeff_mul_finsum]
  rw [sum_finsum_comm]
  · unfold thetaKernel
    apply finsum_congr
    intro p
    simp_rw [hf, hg]
    by_cases hsum : triangularIndex p + triangularIndex (m-p) = n
    · rw [Finset.sum_eq_single (triangularIndex p, triangularIndex (m-p))]
      · simp only [if_true]
        simp only [hsum, if_true]
        rw [show A p * (-1 : k)^p * (B (m-p) * (-1 : k)^(m-p)) =
          (A p*B (m-p))*((-1 : k)^p * (-1 : k)^(m-p)) by ring,
          ← zpow_add₀ (by simp : (-1 : k) ≠ 0)]
        congr 2
        omega
      · intro rs hrs hne
        by_cases hr : triangularIndex p = rs.1
        · have hs : triangularIndex (m-p) ≠ rs.2 := by
            intro hs
            apply hne
            ext <;> simp_all
          simp [hs]
        · simp [hr]
      · intro hnot
        exact False.elim (hnot (by simpa using hsum))
    · rw [if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro rs hrs
      have hrs' : rs.1+rs.2 = n := by simpa using hrs
      by_cases hr : triangularIndex p = rs.1
      · have hs : triangularIndex (m-p) ≠ rs.2 := by omega
        simp [hs]
      · simp [hr]
  · intro rs hrs
    apply (PowerSeries.coeff rs.1 f).coeff.hasFiniteSupport.subset
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun hz => hp (by simp [hz])


lemma thetaKernel_finite (n m : ℤ) (W : ℤ → ℤ → k) :
    Function.HasFiniteSupport (fun p : ℤ =>
      if ((triangularIndex p + triangularIndex (m-p) : ℕ) : ℤ) = n
      then W p (m-p)*(-1 : k)^m else 0) := by
  apply (Finset.finite_toSet (Finset.Icc (-(n.toNat : ℤ)) ((n.toNat : ℤ)+1))).subset
  intro p hp
  simp only [Function.mem_support] at hp
  have he : ((triangularIndex p + triangularIndex (m-p) : ℕ) : ℤ) = n := by
    by_contra he
    exact hp (if_neg he)
  have hb := ArithmeticThetaDurfee.jacobi_support_bound (triangularIndex p) p
    (triangularIndex_twice p).symm
  simp only [Finset.mem_coe, Finset.mem_Icc]
  omega

lemma thetaKernel_sub (n m : ℤ) (W V : ℤ → ℤ → k) :
    thetaKernel n m (fun p q => W p q - V p q) = thetaKernel n m W - thetaKernel n m V := by
  unfold thetaKernel
  rw [← finsum_sub_distrib (thetaKernel_finite n m W) (thetaKernel_finite n m V)]
  apply finsum_congr
  intro p
  split_ifs <;> ring

lemma thetaKernel_smul (n m : ℤ) (c : k) (W : ℤ → ℤ → k) :
    thetaKernel n m (fun p q => c * W p q) = c * thetaKernel n m W := by
  unfold thetaKernel
  rw [mul_finsum]
  apply finsum_congr
  intro p
  split_ifs <;> ring

lemma thetaKernel_swap (n m : ℤ) (W : ℤ → ℤ → k) :
    thetaKernel n m (fun p q => W q p) = thetaKernel n m W := by
  unfold thetaKernel
  apply finsum_eq_of_bijective (fun p : ℤ => m-p)
    (by
      constructor
      · intro a b h
        dsimp at h
        omega
      · intro a
        exact ⟨m-a, by dsimp; omega⟩)
  intro p
  simp only [show m-(m-p) = p by omega, add_comm (triangularIndex p)]

lemma theta_product_integerCoeff (f g : PowerSeries (LaurentPolynomial k))
    (A B : ℤ → k)
    (hf : ∀ r p, (PowerSeries.coeff r f).coeff p =
      if triangularIndex p = r then A p * (-1 : k)^p else 0)
    (hg : ∀ r p, (PowerSeries.coeff r g).coeff p =
      if triangularIndex p = r then B p * (-1 : k)^p else 0)
    (n m : ℤ) : integerCoeff (f*g) n m = thetaKernel n m (fun p q => A p*B q) := by
  by_cases hn : n < 0
  · rw [integerCoeff, if_pos hn, thetaKernel_negative n m _ hn]
  · rw [integerCoeff, if_neg hn, theta_product_coeff f g A B hf hg,
      Int.toNat_of_nonneg (by omega : 0 ≤ n)]

lemma normalizedTheta_coeff_weight (r : ℕ) (p : ℤ) :
    (PowerSeries.coeff r (normalizedTheta (k := k))).coeff p =
      if triangularIndex p = r then 1*(-1 : k)^p else 0 := by
  simp only [normalizedTheta_coeff, one_mul]

lemma normalizedTheta_euler_coeff (r : ℕ) (p : ℤ) :
    (PowerSeries.coeff r (eulerSeries (normalizedTheta (k := k)))).coeff p =
      if triangularIndex p = r then (p : k)*(-1 : k)^p else 0 := by
  simp only [eulerSeries_coeff, eulerLaurent_coeff, normalizedTheta_coeff]
  split_ifs <;> simp

lemma normalizedTheta_euler_euler_coeff (r : ℕ) (p : ℤ) :
    (PowerSeries.coeff r (eulerSeries (eulerSeries (normalizedTheta (k := k))))).coeff p =
      if triangularIndex p = r then (p : k)^2*(-1 : k)^p else 0 := by
  simp only [eulerSeries_coeff, eulerLaurent_coeff, normalizedTheta_coeff]
  split_ifs <;> ring

@[simp] lemma integerCoeff_sub (f g : PowerSeries (LaurentPolynomial k)) (n m : ℤ) :
    integerCoeff (f-g) n m = integerCoeff f n m - integerCoeff g n m := by
  unfold integerCoeff
  split_ifs <;> simp

lemma normalizedTheta_square_kernel (n m : ℤ) :
    integerCoeff ((normalizedTheta (k := k))^2) n m = thetaKernel n m (fun _ _ => 1) := by
  simpa only [pow_two, one_mul] using theta_product_integerCoeff
    (normalizedTheta (k := k)) normalizedTheta (fun _ => 1) (fun _ => 1)
    normalizedTheta_coeff_weight normalizedTheta_coeff_weight n m

lemma normalizedTheta_log_kernel (n m : ℤ) :
    2*integerCoeff (secondLogNumerator eulerSeriesDerivation (normalizedTheta (k := k))) n m =
      -thetaKernel n m (fun p q => ((p : k)-(q : k))^2) := by
  have h1 := theta_product_integerCoeff (eulerSeries (normalizedTheta (k := k)))
    (eulerSeries normalizedTheta) (fun p => (p : k)) (fun q => (q : k))
    normalizedTheta_euler_coeff normalizedTheta_euler_coeff n m
  have h2 := theta_product_integerCoeff (normalizedTheta (k := k))
    (eulerSeries (eulerSeries normalizedTheta)) (fun _ => (1 : k)) (fun q => (q : k)^2)
    normalizedTheta_coeff_weight normalizedTheta_euler_euler_coeff n m
  have hs := thetaKernel_swap n m (fun (p q : ℤ) => (q : k)^2)
  simp only [secondLogNumerator, eulerSeriesDerivation_apply, pow_two, integerCoeff_sub]
  rw [h1]
  simp only [one_mul] at h2
  rw [h2]
  have hk : thetaKernel n m (fun p q => ((p : k)-(q : k))^2) =
      thetaKernel n m (fun p q => (p : k)^2) -
        (2*thetaKernel n m (fun p q => (p : k)*(q : k)) -
          thetaKernel n m (fun p q => (q : k)^2)) := by
    rw [← thetaKernel_smul, ← thetaKernel_sub, ← thetaKernel_sub]
    congr 1
    funext p q
    ring
  simp only [← pow_two]
  rw [hk, hs]
  ring

/-- The degree-two recurrence is proved for the literal normalized gamma square. -/
lemma normalizedTheta_square_recurrence (n m : ℤ) :
    integerCoeff ((normalizedTheta (k := k))^2) n (m+2) =
      integerCoeff (normalizedTheta^2) (n-m) m := by
  simp only [normalizedTheta_square_kernel]
  exact thetaKernel_shift n m _ (by intros; rfl)

/-- The same recurrence for the actual denominator-cleared logarithmic derivative. -/
lemma normalizedTheta_log_recurrence [CharZero k] (n m : ℤ) :
    integerCoeff (secondLogNumerator eulerSeriesDerivation (normalizedTheta (k := k))) n (m+2) =
      integerCoeff (secondLogNumerator eulerSeriesDerivation normalizedTheta) (n-m) m := by
  apply mul_left_cancel₀ (show (2 : k) ≠ 0 by norm_num)
  rw [normalizedTheta_log_kernel, normalizedTheta_log_kernel]
  congr 1
  apply thetaKernel_shift
  intro p q
  push_cast
  ring


/-- Embed scalar formal series as constant Laurent polynomials coefficientwise. -/
def scalarSeries : PowerSeries k →+* PowerSeries (LaurentPolynomial k) :=
  PowerSeries.map LaurentPolynomial.C

lemma integerCoeff_scalar_mul (c : PowerSeries k) (f : PowerSeries (LaurentPolynomial k))
    (n m : ℤ) (N : ℕ) (hN : n ≤ N) :
    integerCoeff (scalarSeries c*f) n m =
      ∑ r ∈ Finset.range (N+1), PowerSeries.coeff r c * integerCoeff f (n-r) m := by
  classical
  by_cases hn : n < 0
  · simp only [integerCoeff, if_pos hn]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [if_pos (by omega : n-(r : ℤ) < 0), mul_zero]
  · have hn0 : 0 ≤ n := by omega
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    rw [integerCoeff, if_neg hn, PowerSeries.coeff_mul,
      AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [scalarSeries, PowerSeries.coeff_map]
    simp_rw [← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc
      _ = ∑ r ∈ Finset.range (n.toNat+1), PowerSeries.coeff r c * integerCoeff f (n-r) m := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrn : r ≤ n.toNat := by simpa using hr
        rw [integerCoeff, if_neg (by omega)]
        have heq : n.toNat-r = (n-(r : ℤ)).toNat := by omega
        simp only [heq]
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro r hr hnot
        rw [integerCoeff, if_pos (by simp only [Finset.mem_range] at hnot; omega), mul_zero]

/-- Scalar series preserve the coefficient recurrence of degree-two sections. -/
lemma degree_two_scalar_mul (c : PowerSeries k) (f : PowerSeries (LaurentPolynomial k))
    (hf : ∀ n m : ℤ, integerCoeff f n (m+2) = integerCoeff f (n-m) m) (n m : ℤ) :
    integerCoeff (scalarSeries c*f) n (m+2) = integerCoeff (scalarSeries c*f) (n-m) m := by
  let N := max n.toNat (n-m).toNat
  rw [integerCoeff_scalar_mul c f n (m+2) N (by dsimp [N]; omega),
    integerCoeff_scalar_mul c f (n-m) m N (by dsimp [N]; omega)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hf, show n-(r : ℤ)-m = n-m-r by omega]

/-- Scale the genuine Laurent variable by a specified scalar unit. -/
def twistLaurent (w : kˣ) : LaurentPolynomial k →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C
    ((Units.map LaurentPolynomial.C.toMonoidHom w)*laurentVariable)

@[simp] lemma twistLaurent_C (w : kˣ) (a : k) :
    twistLaurent w (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  simp [twistLaurent]

@[simp] lemma twistLaurent_T (w : kˣ) (m : ℤ) :
    twistLaurent w (LaurentPolynomial.T m) =
      LaurentPolynomial.C ((w : k)^m)*LaurentPolynomial.T m := by
  simp only [twistLaurent, LaurentPolynomial.eval₂_T, mul_zpow, Units.val_mul,
    laurentVariable_zpow, ← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val]
  rfl

lemma twistLaurent_coeff (w : kˣ) (p : LaurentPolynomial k) (m : ℤ) :
    (twistLaurent w p).coeff m = (w : k)^m*p.coeff m := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | C_mul_T n a =>
    simp only [map_mul, twistLaurent_T, twistLaurent_C]
    rw [← mul_assoc, ← map_mul]
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = m
    · subst n
      simp only [if_true]
      ring
    · simp only [hn, if_false, mul_zero]

def twistSeries (w : kˣ) : PowerSeries (LaurentPolynomial k) →+* PowerSeries (LaurentPolynomial k) :=
  PowerSeries.map (twistLaurent w)

lemma twist_normalizedTheta_coeff (w : kˣ) (r : ℕ) (p : ℤ) :
    (PowerSeries.coeff r (twistSeries w normalizedTheta)).coeff p =
      if triangularIndex p = r then (w : k)^p*(-1 : k)^p else 0 := by
  simp only [twistSeries, PowerSeries.coeff_map, twistLaurent_coeff, normalizedTheta_coeff]
  split_ifs <;> simp

lemma normalizedTheta_twist_product_recurrence (w : kˣ) (n m : ℤ) :
    integerCoeff (twistSeries w⁻¹ normalizedTheta * twistSeries w normalizedTheta) n (m+2) =
      integerCoeff (twistSeries w⁻¹ normalizedTheta * twistSeries w normalizedTheta) (n-m) m := by
  rw [theta_product_integerCoeff _ _ _ _ (twist_normalizedTheta_coeff w⁻¹)
      (twist_normalizedTheta_coeff w),
    theta_product_integerCoeff _ _ _ _ (twist_normalizedTheta_coeff w⁻¹)
      (twist_normalizedTheta_coeff w)]
  apply thetaKernel_shift
  intro p q
  simp only [Units.val_inv_eq_inv_val,
    zpow_add₀ (inv_ne_zero w.ne_zero), zpow_add₀ w.ne_zero, zpow_one]
  field_simp


@[simp] lemma eval_scalarSeries (w : kˣ) (c : PowerSeries k) :
    evalLaurentSeries w (scalarSeries c) = c := by
  apply PowerSeries.ext
  intro n
  simp [scalarSeries, evalLaurentSeries_coeff, PowerSeries.coeff_map]

@[simp] lemma euler_scalarSeries (c : PowerSeries k) :
    eulerSeries (scalarSeries c) = 0 := by
  apply PowerSeries.ext
  intro n
  simp [scalarSeries, eulerSeries_coeff, PowerSeries.coeff_map]

lemma eval_twistLaurent (v w : kˣ) (p : LaurentPolynomial k) :
    LaurentPolynomial.eval₂ (RingHom.id k) v (twistLaurent w p) =
      LaurentPolynomial.eval₂ (RingHom.id k) (w*v) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a =>
    simp only [map_mul, twistLaurent_C, twistLaurent_T, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T, RingHom.id_apply, mul_zpow, Units.val_mul,
      Units.val_zpow_eq_zpow_val]

lemma eval_twistSeries (v w : kˣ) (f : PowerSeries (LaurentPolynomial k)) :
    evalLaurentSeries v (twistSeries w f) = evalLaurentSeries (w*v) f := by
  apply PowerSeries.ext
  intro n
  simp only [evalLaurentSeries_coeff, twistSeries, PowerSeries.coeff_map, eval_twistLaurent]

/-- Euler product in the scalar coefficient ring. -/
def scalarEta : PowerSeries k :=
  PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct 1)

lemma normalizedTheta_eq : (normalizedTheta (k := k)) = scalarSeries scalarEta * universalGamma 1 := by
  congr 1

lemma eval_normalizedTheta (w : kˣ) :
    evalLaurentSeries w (normalizedTheta (k := k)) = scalarEta * fullGamma 1 0 (w : k) (w : k)⁻¹ := by
  rw [normalizedTheta_eq, map_mul, eval_scalarSeries, eval_universalGamma]

lemma eval_normalizedTheta_one : evalLaurentSeries (1 : kˣ) normalizedTheta = 0 := by
  rw [normalizedTheta_eq, map_mul, eval_universalGamma_one, mul_zero]

lemma eval_normalizedTheta_inverse (w : kˣ) :
    evalLaurentSeries w⁻¹ normalizedTheta =
      PowerSeries.C (-(w : k)⁻¹) * evalLaurentSeries w normalizedTheta := by
  rw [eval_normalizedTheta, eval_normalizedTheta]
  simp only [Units.val_inv_eq_inv_val, inv_inv]
  rw [gamma_zero_inversion 1 (w : k) (by omega) w.ne_zero]
  ring

lemma normalizedTheta_log_eq :
    secondLogNumerator eulerSeriesDerivation (normalizedTheta (k := k)) =
      (scalarSeries scalarEta)^2 * secondLogNumerator eulerSeriesDerivation (universalGamma 1) := by
  rw [normalizedTheta_eq, secondLogNumerator_mul]
  have hz : secondLogNumerator eulerSeriesDerivation (scalarSeries (scalarEta (k := k))) = 0 := by
    have hD : eulerSeriesDerivation (scalarSeries (scalarEta (k := k))) = 0 :=
      euler_scalarSeries scalarEta
    rw [secondLogNumerator, hD, map_zero]
    ring
  rw [hz]
  ring

lemma eval_normalizedTheta_log_one :
    evalLaurentSeries (1 : kˣ) (secondLogNumerator eulerSeriesDerivation normalizedTheta) =
      (scalarEta (k := k))^6 := by
  rw [normalizedTheta_log_eq, map_mul, map_pow, eval_scalarSeries,
    universalGamma_horizontal_numerator 1 (by omega)]
  change scalarEta^2 * (scalarEta (k := k))^4 = _
  ring

/-- The actual two-point normalized differential defect, with no assumed identity. -/
def normalizedAdditionDefect (w : kˣ) : PowerSeries (LaurentPolynomial k) :=
  scalarSeries ((evalLaurentSeries w normalizedTheta)^2) *
    secondLogNumerator eulerSeriesDerivation normalizedTheta -
  scalarSeries (evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation normalizedTheta)) *
    normalizedTheta^2 +
  scalarSeries (PowerSeries.C (w : k) * scalarEta^6) *
    (twistSeries w⁻¹ normalizedTheta * twistSeries w normalizedTheta)

@[simp] lemma integerCoeff_add (f g : PowerSeries (LaurentPolynomial k)) (n m : ℤ) :
    integerCoeff (f+g) n m = integerCoeff f n m + integerCoeff g n m := by
  unfold integerCoeff
  split_ifs <;> simp

lemma normalizedAdditionDefect_recurrence [CharZero k] (w : kˣ) (n m : ℤ) :
    integerCoeff (normalizedAdditionDefect w) n (m+2) =
      integerCoeff (normalizedAdditionDefect w) (n-m) m := by
  simp only [normalizedAdditionDefect, integerCoeff_add, integerCoeff_sub]
  rw [degree_two_scalar_mul _ _ normalizedTheta_log_recurrence,
    degree_two_scalar_mul _ _ normalizedTheta_square_recurrence,
    degree_two_scalar_mul _ _ (normalizedTheta_twist_product_recurrence w)]

lemma normalizedAdditionDefect_at_one (w : kˣ) :
    evalLaurentSeries (1 : kˣ) (normalizedAdditionDefect w) = 0 := by
  simp only [normalizedAdditionDefect, map_add, map_sub, map_mul, map_pow,
    eval_scalarSeries, eval_normalizedTheta_log_one, eval_normalizedTheta_one,
    zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero, eval_twistSeries, mul_one,
    eval_normalizedTheta_inverse]
  have hw : PowerSeries.C (w : k) * PowerSeries.C (-(w : k)⁻¹) = (-1 : PowerSeries k) := by
    rw [← map_mul]
    simp [w.ne_zero]
  linear_combination (scalarEta (k := k))^6 * (evalLaurentSeries w normalizedTheta)^2 * hw

lemma normalizedAdditionDefect_at_w (w : kˣ) :
    evalLaurentSeries w (normalizedAdditionDefect w) = 0 := by
  simp only [normalizedAdditionDefect, map_add, map_sub, map_mul, map_pow,
    eval_scalarSeries, eval_twistSeries, inv_mul_cancel, eval_normalizedTheta_one,
    zero_mul, mul_zero, add_zero]
  ring

/-- The normalized two-point theta addition identity, with genuine literal products. -/
lemma normalizedAdditionDefect_zero [CharZero k] (w : kˣ) (hw : (w : k) ≠ 1) :
    normalizedAdditionDefect w = 0 := by
  let F : ℤ → LaurentPolynomial k := fun n =>
    if n < 0 then 0 else PowerSeries.coeff n.toNat (normalizedAdditionDefect w)
  have hcoeff (n m : ℤ) : (F n).coeff m = integerCoeff (normalizedAdditionDefect w) n m := by
    dsimp [F, integerCoeff]
    split_ifs <;> simp
  have hz := degree_two_theta_unique F w hw (by intro n hn; simp [F, hn])
    (by intro n m; simp only [hcoeff]; exact normalizedAdditionDefect_recurrence w n m)
    (by
      intro n
      dsimp [F]
      split_ifs
      · simp
      · rw [← evalLaurentSeries_coeff, normalizedAdditionDefect_at_one]
        simp)
    (by
      intro n
      dsimp [F]
      split_ifs
      · simp
      · rw [← evalLaurentSeries_coeff, normalizedAdditionDefect_at_w]
        simp)
  apply PowerSeries.ext
  intro n
  simpa [F] using hz (n : ℤ)


lemma scalarEta_ne_zero : (scalarEta (k := k)) ≠ 0 := by
  intro h
  have hn := eta_laurent_ne_zero (k := k) 1
  change toLaurent k scalarEta ≠ 0 at hn
  exact hn (by rw [h, map_zero])

lemma eval_normalizedTheta_log (w : kˣ) :
    evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation normalizedTheta) =
      scalarEta^2 * evalLaurentSeries w
        (secondLogNumerator eulerSeriesDerivation (universalGamma 1)) := by
  rw [normalizedTheta_log_eq, map_mul, map_pow, eval_scalarSeries]

/-- Two-point differential addition for the genuine unnormalized gamma product. -/
lemma universalGamma_differential_addition [CharZero k] (a b : kˣ) (hb : (b : k) ≠ 1) :
    evalLaurentSeries a (secondLogNumerator eulerSeriesDerivation (universalGamma 1)) *
        (fullGamma 1 0 (b : k) (b : k)⁻¹)^2 -
      evalLaurentSeries b (secondLogNumerator eulerSeriesDerivation (universalGamma 1)) *
        (fullGamma 1 0 (a : k) (a : k)⁻¹)^2 =
      -PowerSeries.C (b : k) * scalarEta^4 *
        fullGamma 1 0 ((a : k)/(b : k)) ((a : k)/(b : k))⁻¹ *
        fullGamma 1 0 ((a : k)*(b : k)) ((a : k)*(b : k))⁻¹ := by
  have h := congrArg (evalLaurentSeries a) (normalizedAdditionDefect_zero b hb)
  simp only [normalizedAdditionDefect, map_add, map_sub, map_mul, map_pow,
    map_zero, eval_scalarSeries, eval_normalizedTheta_log,
    eval_twistSeries, eval_normalizedTheta, Units.val_mul, Units.val_inv_eq_inv_val] at h
  rw [show (b : k)⁻¹*(a : k) = (a : k)/(b : k) by rw [div_eq_mul_inv, mul_comm],
    mul_comm (b : k) (a : k)] at h
  apply mul_left_cancel₀ (pow_ne_zero 4 (scalarEta_ne_zero (k := k)))
  linear_combination h

/-- Literal cleared addition on the horizontal fundamental annulus for q=t. -/
lemma annular_addition_horizontal_one [CharZero k] (a b : k)
    (ha : Admissible 1 0 a) (hb : Admissible 1 0 b) : AnnularAddition 1 0 0 a b := by
  let au : kˣ := Units.mk0 a ha.2.2.1
  let bu : kˣ := Units.mk0 b hb.2.2.1
  have hlog := universalGamma_differential_addition au bu (hb.2.2.2 rfl)
  have hbridge := literal_difference_log_bridge 1 0 0 au bu (by omega) (by omega)
    (fun _ => ha.2.2.2 rfl) (fun _ => hb.2.2.2 rfl)
  have hps : (tateX 1 0 a-tateX 1 0 b) * (fullGamma 1 0 a a⁻¹)^2 *
      (fullGamma 1 0 b b⁻¹)^2 = -PowerSeries.C b * scalarEta^4 *
        fullGamma 1 0 (a/b) (a/b)⁻¹ * fullGamma 1 0 (a*b) (a*b)⁻¹ := by
    exact hbridge.symm.trans hlog
  have h := congrArg (toLaurent k) hps
  unfold AnnularAddition additionNumerator
  simp only [Nat.cast_zero, sub_self, add_zero]
  have hann (c : k) : gammaLaurent 1 0 c = toLaurent k (fullGamma 1 0 c c⁻¹) :=
    gamma_annulus 1 0 c (by omega)
  simp only [hann]
  simpa only [map_mul, map_sub, map_pow, map_neg, scalarEta, toLaurent,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply] using h


lemma expand_partialGamma_zero {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0)
    (a b : R) (N : ℕ) :
    PowerSeries.expand d hd (partialGamma 1 0 a b N) = partialGamma d 0 a b N := by
  simp only [partialGamma, map_mul, map_prod, map_sub, map_one, map_pow,
    PowerSeries.expand_C, PowerSeries.expand_X, one_mul, add_zero, Nat.sub_zero, ← pow_mul]

lemma expand_fullGamma_zero {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) (a b : R) :
    PowerSeries.expand d hd (fullGamma 1 0 a b) = fullGamma d 0 a b := by
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff n (PowerSeries.expand d hd (partialGamma 1 0 a b (n+1))) := by
      rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      split_ifs
      · exact (partialGamma_stable_ring 1 0 (n/d) (n+1) a b (by omega)
          (by have := Nat.div_le_self n d; omega)).symm
      · rfl
    _ = _ := by
      rw [expand_partialGamma_zero]
      exact partialGamma_stable_ring d 0 n (n+1) a b (by omega) (by omega)

lemma expand_eta (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.expand d hd (scalarEta (k := k)) =
      PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d) := by
  have hfinite (N : ℕ) : PowerSeries.expand d hd
      (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaPartial 1 N)) =
      PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaPartial d N) := by
    simp [ArithmeticThetaUnaryProduct.etaPartial, ← pow_mul]
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff n (PowerSeries.expand d hd
        (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaPartial 1 (n+1)))) := by
      rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      split_ifs
      · exact (mapped_etaPartial_coeff 1 (n/d) (n+1) (by omega)
          (by have := Nat.div_le_self n d; omega)).symm
      · rfl
    _ = _ := by
      rw [hfinite]
      exact mapped_etaPartial_coeff d n (n+1) (by omega) (by omega)

lemma eulerSeries_expand (d : ℕ) (hd : d ≠ 0) (f : PowerSeries (LaurentPolynomial k)) :
    eulerSeries (PowerSeries.expand d hd f) = PowerSeries.expand d hd (eulerSeries f) := by
  apply PowerSeries.ext
  intro n
  simp only [eulerSeries_coeff, PowerSeries.coeff_expand]
  split_ifs <;> simp

lemma expand_eval_log (d : ℕ) (hd : d ≠ 0) (w : kˣ) :
    PowerSeries.expand d hd
      (evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation (universalGamma 1))) =
      evalLaurentSeries w (secondLogNumerator eulerSeriesDerivation (universalGamma d)) := by
  rw [evalLaurentSeries, ← PowerSeries.map_expand]
  congr 1
  simp only [secondLogNumerator, map_sub, map_pow, map_mul, eulerSeriesDerivation_apply]
  rw [← eulerSeries_expand, ← eulerSeries_expand, ← eulerSeries_expand]
  rw [universalGamma, expand_fullGamma_zero]
  rfl

lemma gamma_differential_addition [CharZero k] (d : ℕ) (hd : 0 < d)
    (a b : kˣ) (hb : (b : k) ≠ 1) :
    evalLaurentSeries a (secondLogNumerator eulerSeriesDerivation (universalGamma d)) *
        (fullGamma d 0 (b : k) (b : k)⁻¹)^2 -
      evalLaurentSeries b (secondLogNumerator eulerSeriesDerivation (universalGamma d)) *
        (fullGamma d 0 (a : k) (a : k)⁻¹)^2 =
      -PowerSeries.C (b : k) *
        (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d))^4 *
        fullGamma d 0 ((a : k)/(b : k)) ((a : k)/(b : k))⁻¹ *
        fullGamma d 0 ((a : k)*(b : k)) ((a : k)*(b : k))⁻¹ := by
  have h := congrArg (PowerSeries.expand d (by omega)) (universalGamma_differential_addition a b hb)
  simpa only [map_mul, map_sub, map_pow, map_neg, PowerSeries.expand_C, expand_fullGamma_zero,
    expand_eta, expand_eval_log] using h

/-- The exact addition formula at both residue-zero boundaries, for every d>0. -/
lemma annular_addition_horizontal [CharZero k] (d : ℕ) (a b : k)
    (ha : Admissible d 0 a) (hb : Admissible d 0 b) : AnnularAddition d 0 0 a b := by
  let au : kˣ := Units.mk0 a ha.2.2.1
  let bu : kˣ := Units.mk0 b hb.2.2.1
  have hlog := gamma_differential_addition d ha.1 au bu (hb.2.2.2 rfl)
  have hbridge := literal_difference_log_bridge d 0 0 au bu ha.2.1 hb.2.1
    (fun _ => ha.2.2.2 rfl) (fun _ => hb.2.2.2 rfl)
  have hps : (tateX d 0 a-tateX d 0 b) * (fullGamma d 0 a a⁻¹)^2 *
      (fullGamma d 0 b b⁻¹)^2 = -PowerSeries.C b *
        (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d))^4 *
        fullGamma d 0 (a/b) (a/b)⁻¹ * fullGamma d 0 (a*b) (a*b)⁻¹ := by
    exact hbridge.symm.trans hlog
  have h := congrArg (toLaurent k) hps
  unfold AnnularAddition additionNumerator
  simp only [Nat.cast_zero, sub_self, add_zero]
  have hann (c : k) : gammaLaurent d 0 c = toLaurent k (fullGamma d 0 c c⁻¹) :=
    gamma_annulus d 0 c ha.2.1
  simp only [hann]
  simpa only [map_mul, map_sub, map_pow, map_neg, toLaurent,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply] using h


/-- The Laurent-series parameter as a specified unit. -/
def hahnVariable : (LaurentSeries k)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by rw [HahnSeries.single_mul_single]; norm_num
  inv_val := by rw [HahnSeries.single_mul_single]; norm_num

lemma hahnVariable_zpow (m : ℤ) :
    ((hahnVariable (k := k))^m).val = HahnSeries.single m 1 := by
  cases m with
  | ofNat n => simp [hahnVariable, HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    change (HahnSeries.single (-1) 1 : LaurentSeries k)^(n+1) = _
    rw [HahnSeries.single_pow]
    congr 1 <;> simp [Int.negSucc_eq]

/-- The coefficient-preserving embedding of Laurent polynomials in Laurent series. -/
def laurentPolynomialSeries : LaurentPolynomial k →+* LaurentSeries k :=
  LaurentPolynomial.eval₂ HahnSeries.C hahnVariable

@[simp] lemma laurentPolynomialSeries_C (a : k) :
    laurentPolynomialSeries (LaurentPolynomial.C a) = HahnSeries.single 0 a := by
  simp [laurentPolynomialSeries, HahnSeries.C_apply]

@[simp] lemma laurentPolynomialSeries_T (m : ℤ) :
    laurentPolynomialSeries (LaurentPolynomial.T m : LaurentPolynomial k) = HahnSeries.single m 1 := by
  simp only [laurentPolynomialSeries, LaurentPolynomial.eval₂_T, hahnVariable_zpow]

@[simp] lemma laurentPolynomialSeries_coeff (p : LaurentPolynomial k) (m : ℤ) :
    (laurentPolynomialSeries p).coeff m = p.coeff m := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a =>
    rw [map_mul, laurentPolynomialSeries_C, laurentPolynomialSeries_T,
      HahnSeries.single_mul_single, ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [zero_add, mul_one, HahnSeries.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : m = n
    · subst m; simp
    · simp [h, Ne.symm h]

/-- A quantitative local-finiteness condition for setting q=t^d and z=t.
The bound is on the actual double coefficients, not a formal convergence premise. -/
def DiagonalBound (d : ℕ) (f : PowerSeries (LaurentPolynomial k)) : Prop :=
  ∃ C : ℤ, ∀ (n : ℕ) (m : ℤ), (PowerSeries.coeff n f).coeff m ≠ 0 →
    (n : ℤ) ≤ 2*((d : ℤ)*n+m)+C

lemma diagonalBound_zero (d : ℕ) : DiagonalBound d (0 : PowerSeries (LaurentPolynomial k)) := by
  refine ⟨0, ?_⟩
  simp

lemma diagonalBound_add (d : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (hg : DiagonalBound d g) : DiagonalBound d (f+g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨max C E, ?_⟩
  intro n m h
  by_cases hfn : (PowerSeries.coeff n f).coeff m = 0
  · have hgn : (PowerSeries.coeff n g).coeff m ≠ 0 := by simpa [hfn] using h
    have := hE n m hgn
    omega
  · have := hC n m hfn
    omega

lemma diagonalBound_neg (d : ℕ) (f : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) : DiagonalBound d (-f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  intro n m hn
  apply hC n m
  simpa using hn

lemma diagonalBound_one (d : ℕ) : DiagonalBound d (1 : PowerSeries (LaurentPolynomial k)) := by
  refine ⟨0, ?_⟩
  intro n m hn
  by_cases hn0 : n = 0
  · subst n
    by_cases hm0 : m = 0
    · subst m; simp
    · simp [hm0, PowerSeries.coeff_one, AddMonoidAlgebra.one_def,
        -LaurentPolynomial.single_eq_C_mul_T] at hn
  · simp [PowerSeries.coeff_one, hn0] at hn

lemma diagonalBound_mul (d : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (hg : DiagonalBound d g) : DiagonalBound d (f*g) := by
  classical
  obtain ⟨C, hC⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨C+E, ?_⟩
  intro n m hn
  simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hn
  obtain ⟨rs, hrs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : rs.1+rs.2 = n := by simpa using hrs
  rw [AddMonoidAlgebra.coeff_mul_apply_left] at hne
  simp only [Finsupp.sum] at hne
  obtain ⟨p, hp, hpq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hleft := hC rs.1 p (mul_ne_zero_iff.mp hpq).1
  have hright := hE rs.2 (-p+m) (mul_ne_zero_iff.mp hpq).2
  nlinarith

/-- Series for which this diagonal specialization is actually locally finite. -/
def diagonalSubring (d : ℕ) : Subring (PowerSeries (LaurentPolynomial k)) where
  carrier := DiagonalBound d
  zero_mem' := diagonalBound_zero d
  one_mem' := diagonalBound_one d
  add_mem' := diagonalBound_add d _ _
  neg_mem' := diagonalBound_neg d _
  mul_mem' := diagonalBound_mul d _ _

/-- The n-th q coefficient after the exact monomial substitution. -/
def diagonalTerm (d : ℕ) (f : PowerSeries (LaurentPolynomial k)) (n : ℕ) : LaurentSeries k :=
  HahnSeries.single ((d : ℤ)*n) 1 * laurentPolynomialSeries (PowerSeries.coeff n f)

@[simp] lemma diagonalTerm_coeff (d : ℕ) (f : PowerSeries (LaurentPolynomial k)) (n : ℕ) (m : ℤ) :
    (diagonalTerm d f n).coeff m = (PowerSeries.coeff n f).coeff (m-(d : ℤ)*n) := by
  simp [diagonalTerm, HahnSeries.coeff_single_mul]

/-- The bound proves both required conditions of an actual Hahn summable family. -/
def diagonalFamily (d : ℕ) (f : PowerSeries (LaurentPolynomial k)) (hf : DiagonalBound d f) :
    HahnSeries.SummableFamily ℤ k ℕ where
  toFun := diagonalTerm d f
  isPWO_iUnion_support' := by
    obtain ⟨C, hC⟩ := hf
    apply Set.IsWF.isPWO
    apply BddBelow.wellFoundedOn_lt
    refine ⟨-|C|, ?_⟩
    intro m hm
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
    have hne : (PowerSeries.coeff n f).coeff (m-(d : ℤ)*n) ≠ 0 := by
      simpa only [HahnSeries.mem_support, diagonalTerm_coeff] using hn
    have h := hC n (m-(d : ℤ)*n) hne
    have := le_abs_self C
    have := abs_nonneg C
    omega
  finite_co_support' := by
    obtain ⟨C, hC⟩ := hf
    intro m
    apply (Finset.finite_toSet (Finset.range ((2*m+C).toNat+1))).subset
    intro n hn
    have h := hC n (m-(d : ℤ)*n) (by simpa only [Set.mem_ofPred_eq, diagonalTerm_coeff] using hn)
    simp only [Finset.mem_coe, Finset.mem_range]
    omega

def diagonalValue (d : ℕ) (f : PowerSeries (LaurentPolynomial k)) (hf : DiagonalBound d f) :
    LaurentSeries k := (diagonalFamily d f hf).hsum

@[simp] lemma diagonalValue_coeff (d : ℕ) (f : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (m : ℤ) :
    (diagonalValue d f hf).coeff m = ∑ᶠ n : ℕ, (PowerSeries.coeff n f).coeff (m-(d : ℤ)*n) := by
  simp [diagonalValue, HahnSeries.SummableFamily.coeff_hsum, diagonalFamily]

lemma diagonalValue_add (d : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (hg : DiagonalBound d g) :
    diagonalValue d (f+g) (diagonalBound_add d f g hf hg) =
      diagonalValue d f hf + diagonalValue d g hg := by
  have h : diagonalFamily d (f+g) (diagonalBound_add d f g hf hg) =
      diagonalFamily d f hf + diagonalFamily d g hg := by
    apply HahnSeries.SummableFamily.ext
    intro n
    simp [diagonalFamily, diagonalTerm, mul_add]
  simp only [diagonalValue, h, HahnSeries.SummableFamily.hsum_add]

lemma diagonalTerm_mul (d : ℕ) (f g : PowerSeries (LaurentPolynomial k)) (n : ℕ) :
    diagonalTerm d (f*g) n =
      ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n,
        diagonalTerm d f rs.1 * diagonalTerm d g rs.2 := by
  classical
  unfold diagonalTerm
  rw [PowerSeries.coeff_mul, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hn : rs.1+rs.2 = n := by simpa using hrs
  rw [map_mul]
  have ht : (HahnSeries.single ((d : ℤ)*rs.1) 1 : LaurentSeries k) *
      HahnSeries.single ((d : ℤ)*rs.2) 1 = HahnSeries.single ((d : ℤ)*n) 1 := by
    rw [HahnSeries.single_mul_single, one_mul, ← hn]
    congr 1
    push_cast
    ring
  rw [← ht]
  ring


lemma finsum_nat_antidiagonal (u : ℕ × ℕ → k) (hu : Function.HasFiniteSupport u) :
    (∑ᶠ n : ℕ, ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n, u rs) = ∑ᶠ rs, u rs := by
  classical
  let S := hu.toFinset
  let T := S.image (fun rs => rs.1+rs.2)
  have hS (rs : ℕ × ℕ) : rs ∈ S ↔ u rs ≠ 0 := by
    exact Set.Finite.mem_toFinset hu
  have houter : Function.support (fun n : ℕ =>
      ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n, u rs) ⊆ T := by
    intro n hn
    obtain ⟨rs, hrs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have he : rs.1+rs.2 = n := by simpa using hrs
    exact Finset.mem_image.mpr ⟨rs, (hS rs).mpr hne, he⟩
  rw [finsum_eq_finsetSum_of_support_subset _ houter, finsum_eq_sum _ hu]
  change (∑ n ∈ T, ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n, u rs) = ∑ rs ∈ S, u rs
  have hinner (n : ℕ) : (∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n, u rs) =
      ∑ rs ∈ S with rs.1+rs.2 = n, u rs := by
    symm
    apply Finset.sum_subset
    · intro rs hrs
      simpa using (Finset.mem_filter.mp hrs).2
    · intro rs hrs hnot
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨(hS rs).mpr hne, by simpa using hrs⟩)
  simp_rw [hinner]
  apply Finset.sum_fiberwise_of_maps_to
  intro rs hrs
  exact Finset.mem_image.mpr ⟨rs, hrs, rfl⟩

lemma diagonalValue_mul (d : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (hg : DiagonalBound d g) :
    diagonalValue d (f*g) (diagonalBound_mul d f g hf hg) =
      diagonalValue d f hf * diagonalValue d g hg := by
  unfold diagonalValue
  rw [← HahnSeries.SummableFamily.hsum_mul]
  apply HahnSeries.ext
  funext m
  simp only [HahnSeries.SummableFamily.coeff_hsum]
  change (∑ᶠ n, (diagonalTerm d (f*g) n).coeff m) =
    ∑ᶠ rs : ℕ × ℕ, (diagonalTerm d f rs.1 * diagonalTerm d g rs.2).coeff m
  simp_rw [diagonalTerm_mul, HahnSeries.coeff_sum]
  apply finsum_nat_antidiagonal
  exact ((diagonalFamily d f hf).mul (diagonalFamily d g hg)).finite_co_support m

lemma diagonalValue_zero (d : ℕ) : diagonalValue d (0 : PowerSeries (LaurentPolynomial k))
    (diagonalBound_zero d) = 0 := by
  apply HahnSeries.ext
  funext m
  simp

lemma diagonalValue_one (d : ℕ) : diagonalValue d (1 : PowerSeries (LaurentPolynomial k))
    (diagonalBound_one d) = 1 := by
  apply HahnSeries.ext
  funext m
  rw [diagonalValue_coeff, finsum_eq_single _ 0]
  · by_cases hm : m = 0 <;> simp [hm, AddMonoidAlgebra.one_def,
      -LaurentPolynomial.single_eq_C_mul_T]
  · intro n hn
    simp [PowerSeries.coeff_one, hn]

/-- A ring homomorphism on the proved domain of locally finite diagonal substitution. -/
def diagonalHom (d : ℕ) : diagonalSubring (k := k) d →+* LaurentSeries k where
  toFun f := diagonalValue d f.val f.property
  map_zero' := diagonalValue_zero d
  map_one' := diagonalValue_one d
  map_add' f g := diagonalValue_add d f.val g.val f.property g.property
  map_mul' f g := diagonalValue_mul d f.val g.val f.property g.property


/-- A uniform coefficient support estimate; the numerical constant is retained. -/
def CoefficientGrowth (f : PowerSeries (LaurentPolynomial k)) (C : ℤ) : Prop :=
  ∀ (n : ℕ) (m : ℤ), (PowerSeries.coeff n f).coeff m ≠ 0 → (n : ℤ) ≤ 2*((n : ℤ)+m)+C

lemma coefficientGrowth_mono (f : PowerSeries (LaurentPolynomial k)) (C E : ℤ)
    (h : CoefficientGrowth f C) (hCE : C ≤ E) : CoefficientGrowth f E := by
  intro n m hn
  have := h n m hn
  omega

lemma coefficientGrowth_mul (f g : PowerSeries (LaurentPolynomial k)) (C E : ℤ)
    (hf : CoefficientGrowth f C) (hg : CoefficientGrowth g E) : CoefficientGrowth (f*g) (C+E) := by
  classical
  intro n m hn
  simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hn
  obtain ⟨rs, hrs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : rs.1+rs.2 = n := by simpa using hrs
  rw [AddMonoidAlgebra.coeff_mul_apply_left] at hne
  simp only [Finsupp.sum] at hne
  obtain ⟨p, hp, hpq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hl := hf rs.1 p (mul_ne_zero_iff.mp hpq).1
  have hr := hg rs.2 (-p+m) (mul_ne_zero_iff.mp hpq).2
  omega

lemma coefficientGrowth_sub (f g : PowerSeries (LaurentPolynomial k)) (C : ℤ)
    (hf : CoefficientGrowth f C) (hg : CoefficientGrowth g C) : CoefficientGrowth (f-g) C := by
  intro n m hn
  by_cases hfn : (PowerSeries.coeff n f).coeff m = 0
  · apply hg n m
    simpa [hfn] using hn
  · exact hf n m hfn

lemma coefficientGrowth_one : CoefficientGrowth (1 : PowerSeries (LaurentPolynomial k)) 0 := by
  intro n m hn
  by_cases hn0 : n = 0
  · subst n
    by_cases hm0 : m = 0
    · subst m; simp
    · simp [hm0, PowerSeries.coeff_one, AddMonoidAlgebra.one_def,
        -LaurentPolynomial.single_eq_C_mul_T] at hn
  · simp [PowerSeries.coeff_one, hn0] at hn

lemma coefficientGrowth_monomial (e : ℕ) (p : ℤ) (a : k) (C : ℤ)
    (h : (e : ℤ) ≤ 2*((e : ℤ)+p)+C) :
    CoefficientGrowth (PowerSeries.monomial e (AddMonoidAlgebra.single p a)) C := by
  intro n m hn
  by_cases hen : e = n
  · subst n
    by_cases hpm : p = m
    · subst m; exact h
    · simp [AddMonoidAlgebra.coeff_single,
        -LaurentPolynomial.single_eq_C_mul_T, hpm] at hn
  · simp [PowerSeries.coeff_monomial, Ne.symm hen] at hn

lemma coefficientGrowth_factor (e : ℕ) (p : ℤ) (C : ℤ) (hC : 0 ≤ C)
    (h : (e : ℤ) ≤ 2*((e : ℤ)+p)+C) :
    CoefficientGrowth (1-universalMonomial p e : PowerSeries (LaurentPolynomial k)) C := by
  apply coefficientGrowth_sub
  · exact coefficientGrowth_mono _ 0 C coefficientGrowth_one hC
  · simpa only [universalMonomial, PowerSeries.monomial_eq_C_mul_X_pow,
      LaurentPolynomial.T] using coefficientGrowth_monomial (k := k) e p 1 C h

lemma coefficientGrowth_prod {I : Type*} (s : Finset I) (f : I → PowerSeries (LaurentPolynomial k))
    (hf : ∀ i ∈ s, CoefficientGrowth (f i) 0) : CoefficientGrowth (∏ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefficientGrowth_one (k := k)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact coefficientGrowth_mul _ _ 0 0 (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The finite gamma products satisfy one bound independent of the cutoff. -/
lemma partialGamma_growth (N : ℕ) : CoefficientGrowth
    (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N :
      PowerSeries (LaurentPolynomial k)) 1 := by
  have hforward : CoefficientGrowth (∏ r ∈ Finset.range N,
      (1-universalMonomial 1 r : PowerSeries (LaurentPolynomial k))) 0 := by
    apply coefficientGrowth_prod
    intro r hr
    exact coefficientGrowth_factor r 1 0 (by omega) (by omega)
  have hbackward : CoefficientGrowth (∏ r ∈ Finset.range N,
      (1-universalMonomial (-1) (r+1) : PowerSeries (LaurentPolynomial k))) 1 := by
    cases N with
    | zero =>
      simpa using coefficientGrowth_mono (1 : PowerSeries (LaurentPolynomial k)) 0 1
        coefficientGrowth_one (by omega)
    | succ N =>
      rw [Finset.prod_range_succ']
      apply coefficientGrowth_mul _ _ 0 1
      · apply coefficientGrowth_prod
        intro r hr
        exact coefficientGrowth_factor (r+1+1) (-1) 0 (by omega) (by omega)
      · exact coefficientGrowth_factor 1 (-1) 1 (by omega) (by omega)
  simpa only [partialGamma, one_mul, add_zero, zero_add, Nat.sub_zero, universalMonomial] using
    coefficientGrowth_mul _ _ 0 1 hforward hbackward

lemma universalGamma_growth : CoefficientGrowth (universalGamma 1 : PowerSeries (LaurentPolynomial k)) 1 := by
  intro n m hn
  simp only [universalGamma, fullGamma, PowerSeries.coeff_mk] at hn
  exact partialGamma_growth (n+1) n m hn

lemma coefficientGrowth_euler (f : PowerSeries (LaurentPolynomial k)) (C : ℤ)
    (hf : CoefficientGrowth f C) : CoefficientGrowth (eulerSeries f) C := by
  intro n m hn
  apply hf n m
  simp only [eulerSeries_coeff, eulerLaurent_coeff] at hn
  exact (mul_ne_zero_iff.mp hn).2


/-- Substitute the genuine Laurent monomial a*x^i for a Laurent variable. -/
def parameterLaurent (a : kˣ) (i : ℕ) : LaurentPolynomial k →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C
    ((Units.map LaurentPolynomial.C.toMonoidHom a)*laurentVariable^(i : ℤ))

@[simp] lemma parameterLaurent_C (a : kˣ) (i : ℕ) (c : k) :
    parameterLaurent a i (LaurentPolynomial.C c) = LaurentPolynomial.C c := by
  simp [parameterLaurent]

@[simp] lemma parameterLaurent_T (a : kˣ) (i : ℕ) (m : ℤ) :
    parameterLaurent a i (LaurentPolynomial.T m) =
      LaurentPolynomial.C ((a : k)^m) * LaurentPolynomial.T ((i : ℤ)*m) := by
  simp only [parameterLaurent, LaurentPolynomial.eval₂_T, mul_zpow, ← map_zpow,
    Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, ← zpow_mul,
    laurentVariable_zpow]
  rfl

lemma parameterLaurent_support (a : kˣ) (i : ℕ) (p : LaurentPolynomial k) (m : ℤ)
    (hm : (parameterLaurent a i p).coeff m ≠ 0) :
    ∃ l : ℤ, p.coeff l ≠ 0 ∧ m = (i : ℤ)*l := by
  classical
  have hp := AddMonoidAlgebra.sum_coeff_single p
  rw [← hp] at hm
  simp only [Finsupp.sum, map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    LaurentPolynomial.single_eq_C_mul_T, map_mul, parameterLaurent_C, parameterLaurent_T] at hm
  obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨l, Finsupp.mem_support_iff.mp hl, ?_⟩
  rw [← mul_assoc, ← map_mul, ← LaurentPolynomial.single_eq_C_mul_T] at hne
  by_contra he
  simp [AddMonoidAlgebra.coeff_single, -LaurentPolynomial.single_eq_C_mul_T,
    he, Ne.symm he] at hne

def parameterSeries (a : kˣ) (i : ℕ) :
    PowerSeries (LaurentPolynomial k) →+* PowerSeries (LaurentPolynomial k) :=
  PowerSeries.map (parameterLaurent a i)

lemma parameter_growth (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (f : PowerSeries (LaurentPolynomial k)) (C : ℤ) (hf : CoefficientGrowth f C) :
    ∀ (n : ℕ) (m : ℤ), (PowerSeries.coeff n (parameterSeries a i f)).coeff m ≠ 0 →
      (n : ℤ) ≤ 2*((d : ℤ)*n+m)+(i : ℤ)*C := by
  intro n m hn
  simp only [parameterSeries, PowerSeries.coeff_map] at hn
  obtain ⟨l, hl, rfl⟩ := parameterLaurent_support a i (PowerSeries.coeff n f) m hn
  have h := hf n l hl
  have hmul := mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ i by omega)
  have hdi : (i : ℤ)+1 ≤ 2*d := by omega
  have hmul' := mul_le_mul_of_nonneg_right hdi (show (0 : ℤ) ≤ n by omega)
  nlinarith

lemma parameter_diagonalBound (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (f : PowerSeries (LaurentPolynomial k)) (C : ℤ) (hf : CoefficientGrowth f C) :
    DiagonalBound d (parameterSeries a i f) :=
  ⟨(i : ℤ)*C, parameter_growth d i a hd hi f C hf⟩

/-- The uniform bound supplies the local finiteness needed for literal gamma. -/
lemma gamma_parameter_diagonalBound (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    DiagonalBound d (parameterSeries a i (universalGamma 1)) :=
  parameter_diagonalBound d i a hd hi _ 1 universalGamma_growth

lemma parameter_partial_stable (a : kˣ) (i n N : ℕ) (hn : n < N) :
    PowerSeries.coeff n
      (parameterSeries a i (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N)) =
    PowerSeries.coeff n (parameterSeries a i (universalGamma 1)) := by
  simp only [parameterSeries, PowerSeries.coeff_map, universalGamma]
  congr 1
  exact partialGamma_stable_ring 1 0 n N _ _ (by omega) hn

/-- Coefficient comparison after specialization uses the proved local-finiteness bound. -/
lemma diagonal_coeff_stable (d : ℕ) (f g : PowerSeries (LaurentPolynomial k))
    (hf : DiagonalBound d f) (hg : DiagonalBound d g) (C : ℤ) (m : ℤ) (N : ℕ)
    (hN : 2*m+C < N)
    (hfb : ∀ n p, (PowerSeries.coeff n f).coeff p ≠ 0 →
      (n : ℤ) ≤ 2*((d : ℤ)*n+p)+C)
    (hgb : ∀ n p, (PowerSeries.coeff n g).coeff p ≠ 0 →
      (n : ℤ) ≤ 2*((d : ℤ)*n+p)+C)
    (heq : ∀ n < N, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    (diagonalValue d f hf).coeff m = (diagonalValue d g hg).coeff m := by
  rw [diagonalValue_coeff, diagonalValue_coeff]
  apply finsum_congr
  intro n
  by_cases hn : n < N
  · rw [heq n hn]
  · have hz (s : PowerSeries (LaurentPolynomial k))
        (hs : ∀ n p, (PowerSeries.coeff n s).coeff p ≠ 0 →
          (n : ℤ) ≤ 2*((d : ℤ)*n+p)+C) :
        (PowerSeries.coeff n s).coeff (m-(d : ℤ)*n) = 0 := by
      by_contra hc
      have h := hs n (m-(d : ℤ)*n) hc
      omega
    rw [hz f hfb, hz g hgb]

lemma parameter_gamma_coeff_stable (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (m : ℤ) (N : ℕ) (hN : 2*m+(i : ℤ) < N) :
    (diagonalValue d (parameterSeries a i
        (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N))
      (parameter_diagonalBound d i a hd hi _ 1 (partialGamma_growth N))).coeff m =
    (diagonalValue d (parameterSeries a i (universalGamma 1))
      (gamma_parameter_diagonalBound d i a hd hi)).coeff m := by
  apply diagonal_coeff_stable d _ _ _ _ (i : ℤ) m N hN
  · simpa using parameter_growth d i a hd hi _ 1 (partialGamma_growth N)
  · simpa using parameter_growth d i a hd hi _ 1 universalGamma_growth
  · intro n hn
    exact parameter_partial_stable a i n N hn

lemma diagonalBound_monomial (d e : ℕ) (p : ℤ) (a : k) :
    DiagonalBound d (PowerSeries.monomial e (AddMonoidAlgebra.single p a)) := by
  refine ⟨(e : ℤ)-2*((d : ℤ)*e+p), ?_⟩
  intro n m hn
  by_cases hen : n = e
  · subst n
    by_cases hpm : p = m
    · subst m; omega
    · simp [AddMonoidAlgebra.coeff_single,
        -LaurentPolynomial.single_eq_C_mul_T, hpm] at hn
  · simp [PowerSeries.coeff_monomial, hen] at hn

lemma diagonalValue_monomial (d e : ℕ) (p : ℤ) (a : k)
    (h : DiagonalBound d (PowerSeries.monomial e (AddMonoidAlgebra.single p a))) :
    diagonalValue d (PowerSeries.monomial e (AddMonoidAlgebra.single p a)) h =
      HahnSeries.single ((d : ℤ)*e+p) a := by
  apply HahnSeries.ext
  funext m
  rw [diagonalValue_coeff, finsum_eq_single _ e]
  · simp only [PowerSeries.coeff_monomial, if_true,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, HahnSeries.coeff_single]
    have he : p = m-(d : ℤ)*e ↔ m = (d : ℤ)*e+p := by omega
    simp only [he]
    split_ifs <;> rfl
  · intro n hn
    simp [PowerSeries.coeff_monomial, hn]


/-- A polynomial monomial bundled in the actual specialization domain. -/
def diagonalMonomial (d e : ℕ) (p : ℤ) (a : k) : diagonalSubring (k := k) d :=
  ⟨PowerSeries.monomial e (AddMonoidAlgebra.single p a), diagonalBound_monomial d e p a⟩

@[simp] lemma diagonalHom_monomial (d e : ℕ) (p : ℤ) (a : k) :
    diagonalHom d (diagonalMonomial d e p a) = HahnSeries.single ((d : ℤ)*e+p) a :=
  diagonalValue_monomial d e p a _

def gammaFiniteLift (d i : ℕ) (a : kˣ) (N : ℕ) : diagonalSubring (k := k) d :=
  (∏ r ∈ Finset.range N, (1-diagonalMonomial d r (i : ℤ) (a : k))) *
  (∏ r ∈ Finset.range N, (1-diagonalMonomial d (r+1) (-(i : ℤ)) (a : k)⁻¹))

lemma gammaFiniteLift_val (d i : ℕ) (a : kˣ) (N : ℕ) :
    (gammaFiniteLift d i a N).val = parameterSeries a i
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N) := by
  change (diagonalSubring (k := k) d).subtype (gammaFiniteLift d i a N) = _
  simp only [gammaFiniteLift, map_mul, map_prod, map_sub, map_one,
    Subring.subtype_apply, diagonalMonomial, partialGamma, parameterSeries, map_mul, map_prod, map_sub, map_one,
    map_pow, PowerSeries.map_X, PowerSeries.map_C, parameterLaurent_T, one_mul,
    add_zero, Nat.sub_zero, zpow_one, zpow_neg_one, mul_one, mul_neg_one,
    PowerSeries.monomial_eq_C_mul_X_pow, LaurentPolynomial.single_eq_C_mul_T]

lemma toLaurent_monomial (a : k) (e : ℕ) :
    toLaurent k (monomial a e) = HahnSeries.single (e : ℤ) a := by
  simp [monomial, toLaurent, HahnSeries.single_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single]

lemma diagonalHom_gammaFiniteLift (d i : ℕ) (a : kˣ) (N : ℕ) (hi : i ≤ d) :
    diagonalHom d (gammaFiniteLift d i a N) =
      toLaurent k (partialGamma d i (a : k) (a : k)⁻¹ N) := by
  simp only [gammaFiniteLift, map_mul, map_prod, map_sub, map_one, diagonalHom_monomial,
    partialGamma]
  congr 1
  · apply Finset.prod_congr rfl
    intro r hr
    rw [← map_mul]
    change 1-HahnSeries.single ((d : ℤ)*r+i) (a : k) = 1-toLaurent k (monomial (a : k) (d*r+i))
    rw [toLaurent_monomial]
    congr 2
  · apply Finset.prod_congr rfl
    intro r hr
    rw [← map_mul]
    change 1-HahnSeries.single ((d : ℤ)*(r+1)+ -(i : ℤ)) (a : k)⁻¹ =
      1-toLaurent k (monomial (a : k)⁻¹ (d*(r+1)-i))
    rw [toLaurent_monomial]
    have hie : i ≤ d*(r+1) := by nlinarith
    congr 2
    push_cast [Nat.cast_sub hie]
    ring

lemma diagonalValue_partialGamma (d i : ℕ) (a : kˣ) (N : ℕ) (hi : i ≤ d)
    (hf : DiagonalBound d (parameterSeries a i
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N))) :
    diagonalValue d (parameterSeries a i
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N)) hf =
      toLaurent k (partialGamma d i (a : k) (a : k)⁻¹ N) := by
  change diagonalHom d ⟨_, hf⟩ = _
  have he : (⟨parameterSeries a i
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N), hf⟩ :
        diagonalSubring d) = gammaFiniteLift d i a N := by
    apply Subtype.ext
    exact (gammaFiniteLift_val d i a N).symm
  rw [he, diagonalHom_gammaFiniteLift d i a N hi]

/-- Actual coefficientwise monomial specialization of the universal gamma product. -/
lemma diagonalValue_universalGamma (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i < d) :
    diagonalValue d (parameterSeries a i (universalGamma 1))
      (gamma_parameter_diagonalBound d i a hd hi.le) =
      toLaurent k (fullGamma d i (a : k) (a : k)⁻¹) := by
  apply HahnSeries.ext
  funext m
  let N : ℕ := (2*m+(i : ℤ)).toNat + m.toNat + 1
  have hN : 2*m+(i : ℤ) < N := by dsimp [N]; omega
  rw [← parameter_gamma_coeff_stable d i a hd hi.le m N hN,
    diagonalValue_partialGamma d i a N hi.le]
  change (partialGamma d i (a : k) (a : k)⁻¹ N : LaurentSeries k).coeff m =
    (fullGamma d i (a : k) (a : k)⁻¹ : LaurentSeries k).coeff m
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · have hm : m.natAbs = m.toNat := by omega
    rw [hm]
    exact partialGamma_stable_ring d i m.toNat N _ _ hi (by dsimp [N]; omega)


lemma eval_parameterLaurent (v a : kˣ) (i : ℕ) (p : LaurentPolynomial k) :
    LaurentPolynomial.eval₂ (RingHom.id k) v (parameterLaurent a i p) =
      LaurentPolynomial.eval₂ (RingHom.id k) (a*v^i) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n c =>
    simp only [map_mul, parameterLaurent_C, parameterLaurent_T,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.id_apply,
      mul_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      ← zpow_natCast, ← zpow_mul]

lemma eval_parameterSeries (v a : kˣ) (i : ℕ) (f : PowerSeries (LaurentPolynomial k)) :
    evalLaurentSeries v (parameterSeries a i f) = evalLaurentSeries (a*v^i) f := by
  apply PowerSeries.ext
  intro n
  simp only [evalLaurentSeries_coeff, parameterSeries, PowerSeries.coeff_map, eval_parameterLaurent]

lemma laurent_eq_zero_of_eval_units [Infinite k] (p : LaurentPolynomial k)
    (hp : ∀ w : kˣ, LaurentPolynomial.eval₂ (RingHom.id k) w p = 0) : p = 0 := by
  obtain ⟨N, P, hP⟩ := LaurentPolynomial.exists_T_pow p
  have hroot (x : k) (hx : x ≠ 0) : P.eval x = 0 := by
    have h := congrArg (LaurentPolynomial.eval₂ (RingHom.id k) (Units.mk0 x hx)) hP
    simpa [LaurentPolynomial.eval₂_toLaurent, hp] using h
  have hXP : Polynomial.X*P = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hroot x hx]
  have hP0 : P = 0 := (mul_eq_zero.mp hXP).resolve_left Polynomial.X_ne_zero
  have hz : p*LaurentPolynomial.T (N : ℤ) = 0 := by simpa [hP0] using hP.symm
  exact (mul_eq_zero.mp hz).resolve_right (LaurentPolynomial.isUnit_T _).ne_zero

lemma laurent_eq_zero_away [Infinite k] (p q : LaurentPolynomial k) (hq : q ≠ 0)
    (hp : ∀ w : kˣ, LaurentPolynomial.eval₂ (RingHom.id k) w q ≠ 0 →
      LaurentPolynomial.eval₂ (RingHom.id k) w p = 0) : p = 0 := by
  have h : p*q = 0 := by
    apply laurent_eq_zero_of_eval_units
    intro w
    rw [map_mul]
    by_cases hw : LaurentPolynomial.eval₂ (RingHom.id k) w q = 0
    · simp [hw]
    · simp [hp w hw]
  exact (mul_eq_zero.mp h).resolve_right hq

lemma parameter_horizontal_factor_ne_zero (j : ℕ) (b : kˣ) (hb : j = 0 → (b : k) ≠ 1) :
    (1-LaurentPolynomial.C (b : k)*LaurentPolynomial.T (j : ℤ) : LaurentPolynomial k) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : LaurentPolynomial k => p.coeff (j : ℤ)) h
  by_cases hj : j = 0
  · subst j
    have hb' := hb rfl
    simp only [Nat.cast_zero, LaurentPolynomial.T_zero, mul_one] at h
    have hc0 := congrArg (fun p : LaurentPolynomial k => p.coeff 0) h
    have he : (b : k) = 1 := by simpa using (sub_eq_zero.mp h : 1 = LaurentPolynomial.C (b : k)).symm |> congrArg (fun p => p.coeff 0)
    exact hb' he
  · simp [hj, AddMonoidAlgebra.one_def, -LaurentPolynomial.single_eq_C_mul_T,
      ← LaurentPolynomial.single_eq_C_mul_T] at hc

/-- The polynomial parameter form of the actual unnormalized two-point identity. -/
def parameterAdditionDefect (i j : ℕ) (a b : kˣ) : PowerSeries (LaurentPolynomial k) :=
  parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1)) *
      (parameterSeries b j (universalGamma 1))^2 -
    parameterSeries b j (secondLogNumerator eulerSeriesDerivation (universalGamma 1)) *
      (parameterSeries a i (universalGamma 1))^2 +
    PowerSeries.C (LaurentPolynomial.C (b : k)*LaurentPolynomial.T (j : ℤ)) *
      (scalarSeries scalarEta)^4 *
      parameterSeries (a/b) (i-j) (universalGamma 1) *
      parameterSeries (a*b) (i+j) (universalGamma 1)

lemma parameterAdditionDefect_zero [CharZero k] (i j : ℕ) (a b : kˣ)
    (hji : j ≤ i) (hb : j = 0 → (b : k) ≠ 1) : parameterAdditionDefect i j a b = 0 := by
  have heval (v : kˣ)
      (hv : LaurentPolynomial.eval₂ (RingHom.id k) v
        (1-LaurentPolynomial.C (b : k)*LaurentPolynomial.T (j : ℤ)) ≠ 0) :
      evalLaurentSeries v (parameterAdditionDefect i j a b) = 0 := by
    have hbv : ((b*v^j : kˣ) : k) ≠ 1 := by
      simp only [map_sub, map_one, map_mul, LaurentPolynomial.eval₂_C,
        LaurentPolynomial.eval₂_T, RingHom.id_apply, zpow_natCast,
        Units.val_pow_eq_pow_val] at hv
      simpa using (sub_ne_zero.mp hv).symm
    have h := universalGamma_differential_addition (a*v^i) (b*v^j) hbv
    have hdiv : (a/b)*v^(i-j) = (a*v^i)/(b*v^j) := by
      rw [pow_sub v hji]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
    have hmul : (a*b)*v^(i+j) = (a*v^i)*(b*v^j) := by
      rw [pow_add]
      ac_rfl
    simp only [parameterAdditionDefect, map_add, map_sub, map_mul, map_pow,
      eval_parameterSeries, eval_scalarSeries, eval_universalGamma,
      hdiv, hmul]
    have hC : evalLaurentSeries v
        (PowerSeries.C (LaurentPolynomial.C (b : k)*LaurentPolynomial.T (j : ℤ))) =
        PowerSeries.C (((b*v^j : kˣ) : k)) := by
      simp [evalLaurentSeries]
    simp only [map_mul] at hC
    rw [hC]
    simpa only [Units.val_div_eq_div_val, Units.val_mul, neg_mul, sub_neg_eq_add] using (sub_eq_zero.mpr h)
  apply PowerSeries.ext
  intro n
  simp only [map_zero]
  apply laurent_eq_zero_away _ _ (parameter_horizontal_factor_ne_zero j b hb)
  intro v hv
  have h := congrArg (PowerSeries.coeff n) (heval v hv)
  simpa only [evalLaurentSeries_coeff, map_zero] using h


lemma diagonalBound_parameter (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (f : PowerSeries (LaurentPolynomial k)) (hf : DiagonalBound 1 f) :
    DiagonalBound d (parameterSeries a i f) := by
  obtain ⟨C, hC⟩ := hf
  apply parameter_diagonalBound d i a hd hi f C
  simpa only [CoefficientGrowth, Nat.cast_one, one_mul] using hC

def parameterLift (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalSubring (k := k) 1 →+* diagonalSubring (k := k) d where
  toFun f := ⟨parameterSeries a i f.val, diagonalBound_parameter d i a hd hi f.val f.property⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_mul' f g := Subtype.ext (map_mul _ f.val g.val)
  map_add' f g := Subtype.ext (map_add _ f.val g.val)

/-- The specified substitution q=t^d, z=a*t^i on its proved domain. -/
def specializationHom (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalSubring (k := k) 1 →+* LaurentSeries k :=
  (diagonalHom d).comp (parameterLift d i a hd hi)

lemma coefficientGrowth_log (f : PowerSeries (LaurentPolynomial k)) (C : ℤ)
    (hf : CoefficientGrowth f C) :
    CoefficientGrowth (secondLogNumerator eulerSeriesDerivation f) (C+C) := by
  simp only [secondLogNumerator, eulerSeriesDerivation_apply, pow_two]
  apply coefficientGrowth_sub
  · simpa only [secondLogNumerator, pow_two] using coefficientGrowth_mul
      (eulerSeries f) (eulerSeries f) C C (coefficientGrowth_euler f C hf)
      (coefficientGrowth_euler f C hf)
  · exact coefficientGrowth_mul f (eulerSeries (eulerSeries f)) C C hf
      (coefficientGrowth_euler _ C (coefficientGrowth_euler f C hf))

lemma diagonalBound_log (f : PowerSeries (LaurentPolynomial k)) (hf : DiagonalBound 1 f) :
    DiagonalBound 1 (secondLogNumerator eulerSeriesDerivation f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C+C, ?_⟩
  have h := coefficientGrowth_log f C (by simpa only [CoefficientGrowth, Nat.cast_one, one_mul] using hC)
  simpa only [CoefficientGrowth, Nat.cast_one, one_mul] using h

def logNumeratorLift (f : diagonalSubring (k := k) 1) : diagonalSubring (k := k) 1 :=
  ⟨secondLogNumerator eulerSeriesDerivation f.val, diagonalBound_log f.val f.property⟩

lemma logNumeratorLift_mul (f g : diagonalSubring (k := k) 1) :
    logNumeratorLift (f*g) = g^2*logNumeratorLift f + f^2*logNumeratorLift g := by
  apply Subtype.ext
  exact secondLogNumerator_mul eulerSeriesDerivation f.val g.val

@[simp] lemma logNumeratorLift_one : logNumeratorLift (1 : diagonalSubring (k := k) 1) = 0 := by
  apply Subtype.ext
  change secondLogNumerator eulerSeriesDerivation (1 : PowerSeries (LaurentPolynomial k)) = 0
  rw [secondLogNumerator, Derivation.map_one_eq_zero, map_zero]
  ring

lemma map_logNumeratorLift_prod {B I : Type*} [CommRing B]
    (φ : diagonalSubring (k := k) 1 →+* B) (s : Finset I)
    (f : I → diagonalSubring (k := k) 1) (x : I → B)
    (hx : ∀ i ∈ s, φ (logNumeratorLift (f i)) = (φ (f i))^2*x i) :
    φ (logNumeratorLift (∏ i ∈ s, f i)) = (∏ i ∈ s, φ (f i))^2 * ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      logNumeratorLift_mul, map_add, map_mul, map_pow, map_mul, map_pow,
      map_prod, hx i (Finset.mem_insert_self i s),
      ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]
    ring

lemma specializationHom_monomial (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (e : ℕ) (p : ℤ) (c : k) :
    specializationHom d i a hd hi (diagonalMonomial 1 e p c) =
      HahnSeries.single ((d : ℤ)*e+(i : ℤ)*p) (c*(a : k)^p) := by
  have he : parameterSeries a i (PowerSeries.monomial e (AddMonoidAlgebra.single p c)) =
      PowerSeries.monomial e (AddMonoidAlgebra.single ((i : ℤ)*p) (c*(a : k)^p)) := by
    simp only [parameterSeries, PowerSeries.monomial_eq_C_mul_X_pow,
      LaurentPolynomial.single_eq_C_mul_T, map_mul, map_pow, PowerSeries.map_C,
      PowerSeries.map_X, parameterLaurent_C, parameterLaurent_T]
    rw [← mul_assoc, ← map_mul]
  have hb : parameterLift d i a hd hi (diagonalMonomial 1 e p c) =
      diagonalMonomial d e ((i : ℤ)*p) (c*(a : k)^p) := by
    apply Subtype.ext
    exact he
  change diagonalHom d (parameterLift d i a hd hi (diagonalMonomial 1 e p c)) = _
  rw [hb, diagonalHom_monomial]

lemma logNumeratorLift_factor (m : ℤ) (e : ℕ) (hm : m = 1 ∨ m = -1) :
    logNumeratorLift (1-diagonalMonomial (k := k) 1 e m 1) = diagonalMonomial 1 e m 1 := by
  apply Subtype.ext
  change secondLogNumerator eulerSeriesDerivation
    (1-PowerSeries.monomial e (AddMonoidAlgebra.single m 1)) =
      PowerSeries.monomial e (AddMonoidAlgebra.single m 1)
  have hv : (PowerSeries.monomial e (AddMonoidAlgebra.single m 1) :
      PowerSeries (LaurentPolynomial k)) = universalMonomial m e := by
    rw [PowerSeries.monomial_eq_C_mul_X_pow]
    rfl
  rw [hv]
  apply secondLogNumerator_factor
  rw [euler_universalMonomial]
  rcases hm with hm | hm <;> simp [hm]

lemma specialization_log_factors {I : Type*} (d i : ℕ) (a : kˣ)
    (hd : 0 < d) (hi : i ≤ d) (s : Finset I) (m : I → ℤ) (e E : I → ℕ)
    (hm : ∀ r ∈ s, m r = 1 ∨ m r = -1)
    (hE : ∀ r ∈ s, (d : ℤ)*e r+(i : ℤ)*m r = E r)
    (hunit : ∀ r ∈ s, E r = 0 → (a : k)^(m r) ≠ 1) :
    specializationHom d i a hd hi (logNumeratorLift
      (∏ r ∈ s, (1-diagonalMonomial 1 (e r) (m r) 1))) =
      (∏ r ∈ s, (1-toLaurent k (monomial ((a : k)^(m r)) (E r))))^2 *
        ∑ r ∈ s, toLaurent k (xTerm (monomial ((a : k)^(m r)) (E r))) := by
  have hfactor (r : I) (hr : r ∈ s) : specializationHom d i a hd hi
      (1-diagonalMonomial 1 (e r) (m r) 1) =
        1-toLaurent k (monomial ((a : k)^(m r)) (E r)) := by
    rw [map_sub, map_one, specializationHom_monomial, one_mul, hE r hr, toLaurent_monomial]
  rw [← Finset.prod_congr rfl hfactor]
  apply map_logNumeratorLift_prod
  intro r hr
  rw [logNumeratorLift_factor _ _ (hm r hr), specializationHom_monomial,
    one_mul, hE r hr, hfactor r hr, ← toLaurent_monomial]
  have hx : PowerSeries.constantCoeff (monomial ((a : k)^(m r)) (E r)) ≠ 1 := by
    by_cases he : E r = 0
    · simpa [monomial, he] using hunit r hr he
    · simp [monomial, he]
  have h := congrArg (toLaurent k) (xTerm_clear _ hx)
  simpa only [map_mul, map_pow, map_sub, map_one] using h.symm



def universalPartialLift (N : ℕ) : diagonalSubring (k := k) 1 :=
  (∏ r ∈ Finset.range N, (1-diagonalMonomial 1 r 1 1)) *
  (∏ r ∈ Finset.range N, (1-diagonalMonomial 1 (r+1) (-1) 1))

lemma universalPartialLift_val (N : ℕ) :
    (universalPartialLift (k := k) N).val =
      partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N := by
  change (diagonalSubring (k := k) 1).subtype (universalPartialLift N) = _
  simp only [universalPartialLift, map_mul, map_prod, map_sub, map_one,
    Subring.subtype_apply, diagonalMonomial, partialGamma, one_mul,
    add_zero, Nat.sub_zero, PowerSeries.monomial_eq_C_mul_X_pow,
    LaurentPolynomial.single_eq_C_mul_T, map_one]

set_option maxHeartbeats 1600000 in
lemma specialization_partialGamma_log (d i N : ℕ) (a : kˣ) (hd : 0 < d)
    (hi : i < d) (ha : i = 0 → (a : k) ≠ 1) :
    specializationHom d i a hd hi.le (logNumeratorLift (universalPartialLift N)) =
      toLaurent k ((partialGamma d i (a : k) (a : k)⁻¹ N)^2 * rawPartialX d i N (a : k)) := by
  have hp := specialization_log_factors d i a hd hi.le (Finset.range N)
    (fun _ => (1 : ℤ)) (fun r => r) (fun r => d*r+i) (by simp)
    (by intros; push_cast; ring) (by
      intro r hr hz
      simpa using ha (by omega))
  have hn := specialization_log_factors d i a hd hi.le (Finset.range N)
    (fun _ => (-1 : ℤ)) (fun r => r+1) (fun r => d*(r+1)-i) (by simp)
    (by
      intro r hr
      have hie : i ≤ d*(r+1) := by nlinarith
      push_cast [Nat.cast_sub hie]
      ring) (by
      intro r hr hz
      have := inverse_positive d i r hd hi
      omega)
  simp only [zpow_one, zpow_neg_one] at hp hn
  have hf (r : ℕ) : specializationHom d i a hd hi.le (1-diagonalMonomial 1 r 1 1) =
      1-toLaurent k (monomial (a : k) (d*r+i)) := by
    rw [map_sub, map_one, specializationHom_monomial, one_mul, zpow_one,
      mul_one, toLaurent_monomial]
    congr 2
  have hb (r : ℕ) : specializationHom d i a hd hi.le (1-diagonalMonomial 1 (r+1) (-1) 1) =
      1-toLaurent k (monomial (a : k)⁻¹ (d*(r+1)-i)) := by
    rw [map_sub, map_one, specializationHom_monomial, one_mul, zpow_neg_one,
      toLaurent_monomial]
    have hie : i ≤ d*(r+1) := by nlinarith
    congr 2
    push_cast [Nat.cast_sub hie]
    ring
  rw [universalPartialLift, logNumeratorLift_mul, map_add, map_mul, map_mul,
    map_pow, map_pow, hp, hn]
  simp only [map_prod, hf, hb, partialGamma, rawPartialX, map_mul, map_add,
    map_pow, map_prod, map_sum, map_sub, map_one]
  simp only [monomial, map_mul, map_pow]
  ring

set_option maxHeartbeats 1600000 in
lemma diagonalValue_partialGamma_log (d i N : ℕ) (a : kˣ) (hd : 0 < d)
    (hi : i < d) (ha : i = 0 → (a : k) ≠ 1)
    (hf : DiagonalBound d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N)))) :
    diagonalValue d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation
      (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N))) hf =
      toLaurent k ((partialGamma d i (a : k) (a : k)⁻¹ N)^2 * rawPartialX d i N (a : k)) := by
  have he : (⟨_, hf⟩ : diagonalSubring d) =
      parameterLift d i a hd hi.le (logNumeratorLift (universalPartialLift N)) := by
    apply Subtype.ext
    change _ = parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalPartialLift N).val)
    rw [universalPartialLift_val]
  change diagonalHom d ⟨_, hf⟩ = _
  rw [he]
  exact specialization_partialGamma_log d i N a hd hi ha

lemma log_parameter_diagonalBound (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    DiagonalBound d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1))) :=
  parameter_diagonalBound d i a hd hi _ 2 (coefficientGrowth_log _ 1 universalGamma_growth)

set_option maxHeartbeats 1600000 in
lemma parameter_log_coeff_stable (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d)
    (m : ℤ) (N : ℕ) (hN : 2*m+2*(i : ℤ) < N) :
    (diagonalValue d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation
        (partialGamma 1 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) N)))
      (parameter_diagonalBound d i a hd hi _ 2 (coefficientGrowth_log _ 1 (partialGamma_growth N)))).coeff m =
    (diagonalValue d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1)))
      (log_parameter_diagonalBound d i a hd hi)).coeff m := by
  apply diagonal_coeff_stable d _ _ _ _ (2*(i : ℤ)) m N hN
  · simpa [mul_comm] using parameter_growth d i a hd hi _ 2
      (coefficientGrowth_log _ 1 (partialGamma_growth N))
  · simpa [mul_comm] using parameter_growth d i a hd hi _ 2
      (coefficientGrowth_log _ 1 universalGamma_growth)
  · intro n hn
    simp only [parameterSeries, PowerSeries.coeff_map]
    exact congrArg (parameterLaurent a i) (secondLog_coeff_congr n _ _ (fun r hr =>
      partialGamma_stable_ring 1 0 r N _ _ (by omega) (by omega)))

set_option maxHeartbeats 1600000 in
/-- The specialized universal logarithmic numerator is the literal annular sum times gamma squared. -/
lemma diagonalValue_universalGamma_log (d i : ℕ) (a : kˣ) (hd : 0 < d)
    (hi : i < d) (ha : i = 0 → (a : k) ≠ 1) :
    diagonalValue d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1)))
      (log_parameter_diagonalBound d i a hd hi.le) =
      toLaurent k ((fullGamma d i (a : k) (a : k)⁻¹)^2 * rawAnnularX d i (a : k)) := by
  apply HahnSeries.ext
  funext m
  let N : ℕ := (2*m+2*(i : ℤ)).toNat + m.toNat + 1
  have hN : 2*m+2*(i : ℤ) < N := by dsimp [N]; omega
  rw [← parameter_log_coeff_stable d i a hd hi.le m N hN,
    diagonalValue_partialGamma_log d i N a hd hi ha]
  change (HahnSeries.ofPowerSeries ℤ k ((partialGamma d i (a : k) (a : k)⁻¹ N)^2 * rawPartialX d i N (a : k))).coeff m =
    (HahnSeries.ofPowerSeries ℤ k ((fullGamma d i (a : k) (a : k)⁻¹)^2 * rawAnnularX d i (a : k))).coeff m
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · have hm : m.natAbs = m.toNat := by omega
    rw [hm]
    apply coeff_mul_congr
    · intro r hr
      simp only [pow_two]
      apply coeff_mul_congr <;> intro l hl <;>
        exact partialGamma_stable_ring d i l N _ _ hi (by dsimp [N]; omega)
    · intro r hr
      exact rawPartialX_coeff_stable d i r N _ hi (by dsimp [N]; omega)


lemma diagonalBound_scalar (d : ℕ) (hd : 0 < d) (f : PowerSeries k) :
    DiagonalBound d (scalarSeries f) := by
  refine ⟨0, ?_⟩
  intro n m hm
  have hm0 : m = 0 := by
    by_contra h
    simp [scalarSeries, LaurentPolynomial.C, AddMonoidAlgebra.coeff_single,
      -LaurentPolynomial.single_eq_C_mul_T, Ne.symm h] at hm
  subst m
  have hdn : (n : ℤ) ≤ (d : ℤ)*n := by exact_mod_cast Nat.le_mul_of_pos_left n hd
  omega

def scalarLift (d : ℕ) (hd : 0 < d) (f : PowerSeries k) : diagonalSubring (k := k) d :=
  ⟨scalarSeries f, diagonalBound_scalar d hd f⟩

lemma diagonalHom_scalar (d : ℕ) (hd : 0 < d) (f : PowerSeries k) :
    diagonalHom d (scalarLift d hd f) = toLaurent k (PowerSeries.expand d (by omega) f) := by
  apply HahnSeries.ext
  funext m
  change (diagonalValue d (scalarSeries f) (diagonalBound_scalar d hd f)).coeff m =
    (PowerSeries.expand d (by omega) f : LaurentSeries k).coeff m
  rw [diagonalValue_coeff, PowerSeries.coeff_coe]
  have hc (n : ℕ) : (PowerSeries.coeff n (scalarSeries f)).coeff (m-(d : ℤ)*n) =
      if m = (d : ℤ)*n then PowerSeries.coeff n f else 0 := by
    simp only [scalarSeries, PowerSeries.coeff_map, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    have he : (0 : ℤ) = m-(d : ℤ)*n ↔ m = (d : ℤ)*n := by omega
    simp only [he]
  simp only [hc]
  split_ifs with hm
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro n
    have hn : (0 : ℤ) ≤ (d : ℤ)*n := by positivity
    simp [show m ≠ (d : ℤ)*n by omega]
  · have hm' : m = (m.natAbs : ℤ) := by omega
    rw [PowerSeries.coeff_expand]
    split_ifs with hdiv
    · rw [finsum_eq_single _ (m.natAbs/d)]
      · have he : m = (d : ℤ)*(m.natAbs/d : ℕ) := by
          calc
            m = (m.natAbs : ℤ) := hm'
            _ = (d : ℤ)*(m.natAbs/d : ℕ) := by
              exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
        rw [if_pos he]
      · intro n hn
        have hne : m ≠ (d : ℤ)*n := by
          intro he
          have he' : m.natAbs = d*n := by exact_mod_cast hm'.symm.trans he
          have : m.natAbs/d = n := by rw [he', Nat.mul_div_cancel_left _ hd]
          omega
        simp [hne]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro n
      have hne : m ≠ (d : ℤ)*n := by
        intro he
        apply hdiv
        have he' : m.natAbs = d*n := by exact_mod_cast hm'.symm.trans he
        exact ⟨n, he'⟩
      simp [hne]

lemma partialGamma_endpoint {R : Type*} [CommRing R] (d N : ℕ) (a b : R) :
    partialGamma d d a b N = partialGamma d 0 b a N := by
  simp only [partialGamma, Nat.add_zero, Nat.sub_zero, Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  exact mul_comm _ _

lemma fullGamma_endpoint {R : Type*} [CommRing R] (d : ℕ) (a b : R) :
    fullGamma d d a b = fullGamma d 0 b a := by
  apply PowerSeries.ext
  intro n
  simp only [fullGamma, PowerSeries.coeff_mk, partialGamma_endpoint]

lemma partialGamma_stable_closed {R : Type*} [CommRing R] (d i n N : ℕ) (a b : R)
    (hd : 0 < d) (hi : i ≤ d) (hN : n < N) :
    PowerSeries.coeff n (partialGamma d i a b N) = PowerSeries.coeff n (fullGamma d i a b) := by
  rcases hi.eq_or_lt with hi | hi
  · subst i
    rw [partialGamma_endpoint, fullGamma_endpoint]
    exact partialGamma_stable_ring d 0 n N b a hd hN
  · exact partialGamma_stable_ring d i n N a b hi hN

lemma gamma_closed_annulus (d i : ℕ) (a : k) (hd : 0 < d) (hi : i ≤ d) (ha : a ≠ 0) :
    gammaLaurent d (i : ℤ) a = toLaurent k (fullGamma d i a a⁻¹) := by
  rcases hi.eq_or_lt with hi | hi
  · subst i
    rw [fullGamma_endpoint, gamma_zero_inversion d a hd ha]
    have h := gamma_translation d 0 a hd ha
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, gamma_annulus d 0 a hd] at h
    simpa [map_mul, toLaurent, HahnSeries.C_apply] using h
  · exact gamma_annulus d i a hi

lemma diagonalValue_universalGamma_closed (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalValue d (parameterSeries a i (universalGamma 1))
      (gamma_parameter_diagonalBound d i a hd hi) = gammaLaurent d (i : ℤ) (a : k) := by
  rw [gamma_closed_annulus d i (a : k) hd hi a.ne_zero]
  apply HahnSeries.ext
  funext m
  let N : ℕ := (2*m+(i : ℤ)).toNat + m.toNat + 1
  have hN : 2*m+(i : ℤ) < N := by dsimp [N]; omega
  rw [← parameter_gamma_coeff_stable d i a hd hi m N hN,
    diagonalValue_partialGamma d i a N hi]
  change (partialGamma d i (a : k) (a : k)⁻¹ N : LaurentSeries k).coeff m =
    (fullGamma d i (a : k) (a : k)⁻¹ : LaurentSeries k).coeff m
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · have hm : m.natAbs = m.toNat := by omega
    rw [hm]
    exact partialGamma_stable_closed d i m.toNat N _ _ hd hi (by dsimp [N]; omega)


lemma gamma_reflection (d : ℕ) (s : ℤ) (a : k) (hd : 0 < d) (ha : a ≠ 0) :
    gammaLaurent d ((d : ℤ)-s) a⁻¹ = gammaLaurent d s a := by
  have ht := gamma_translation d (-s) a⁻¹ hd (inv_ne_zero ha)
  rw [gamma_inversion d s a hd ha] at ht
  have hm : (HahnSeries.single s a : LaurentSeries k) * HahnSeries.single (-s) a⁻¹ = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, mul_inv_cancel₀ ha, HahnSeries.single_zero_one]
  simpa only [neg_add_eq_sub, neg_neg, inv_inv, neg_mul_neg, ← mul_assoc, hm, one_mul] using ht

lemma additionNumerator_reflection (d : ℕ) (i j : ℤ) (a b : k)
    (hd : 0 < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    additionNumerator d ((d : ℤ)-i) j a⁻¹ b = additionNumerator d i j a b := by
  have h₁ : a⁻¹/b = (a*b)⁻¹ := by simp [div_eq_mul_inv, mul_comm]
  have h₂ : a⁻¹*b = (a/b)⁻¹ := by simp [div_eq_mul_inv, mul_comm]
  unfold additionNumerator
  rw [show (d : ℤ)-i-j = d-(i+j) by omega,
    show (d : ℤ)-i+j = d-(i-j) by omega, h₁, h₂,
    gamma_reflection d (i+j) (a*b) hd (mul_ne_zero ha hb),
    gamma_reflection d (i-j) (a/b) hd (div_ne_zero ha hb)]
  ring

lemma annular_addition_reflect_first (d i j : ℕ) (a b : k)
    (hi : 0 < i) (hid : i < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    AnnularAddition d (d-i) j a⁻¹ b ↔ AnnularAddition d i j a b := by
  unfold AnnularAddition
  rw [tateX_reflection d i a hi hid, Nat.cast_sub hid.le,
    gamma_reflection d i a (by omega) ha,
    additionNumerator_reflection d i j a b (by omega) ha hb]

lemma annular_addition_reflect_second (d i j : ℕ) (a b : k)
    (hj : 0 < j) (hjd : j < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    AnnularAddition d i (d-j) a b⁻¹ ↔ AnnularAddition d i j a b := by
  rw [annular_addition_swap d i (d-j) a b⁻¹ (by omega) ha (inv_ne_zero hb),
    annular_addition_reflect_first d j i b a hj hjd hb ha,
    annular_addition_swap d j i b a (by omega) hb ha]


def gammaSpecializedLift (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalSubring (k := k) d :=
  ⟨parameterSeries a i (universalGamma 1), gamma_parameter_diagonalBound d i a hd hi⟩

def logSpecializedLift (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalSubring (k := k) d :=
  ⟨parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1)),
    log_parameter_diagonalBound d i a hd hi⟩

lemma diagonalHom_gammaSpecializedLift (d i : ℕ) (a : kˣ) (hd : 0 < d) (hi : i ≤ d) :
    diagonalHom d (gammaSpecializedLift d i a hd hi) = gammaLaurent d (i : ℤ) (a : k) :=
  diagonalValue_universalGamma_closed d i a hd hi

lemma diagonalHom_logSpecializedLift (d i : ℕ) (a : kˣ) (hd : 0 < d)
    (hi : i < d) (ha : i = 0 → (a : k) ≠ 1) :
    diagonalHom d (logSpecializedLift d i a hd hi.le) =
      (gammaLaurent d (i : ℤ) (a : k))^2 * toLaurent k (rawAnnularX d i (a : k)) := by
  change diagonalValue d (parameterSeries a i (secondLogNumerator eulerSeriesDerivation (universalGamma 1)))
    (log_parameter_diagonalBound d i a hd hi.le) = _
  rw [diagonalValue_universalGamma_log d i a hd hi ha, map_mul, map_pow,
    gamma_annulus d i (a : k) hi]

set_option maxHeartbeats 1600000 in
lemma annular_addition_chamber_units [CharZero k] (d i j : ℕ) (a b : kˣ)
    (hd : 0 < d) (hi : i < d) (hj : j < d) (hji : j ≤ i) (hs : i+j ≤ d)
    (ha : i = 0 → (a : k) ≠ 1) (hb : j = 0 → (b : k) ≠ 1) :
    AnnularAddition d i j (a : k) (b : k) := by
  have hdiff : i-j ≤ d := by omega
  have he : logSpecializedLift d i a hd hi.le * (gammaSpecializedLift d j b hd hj.le)^2 -
      logSpecializedLift d j b hd hj.le * (gammaSpecializedLift d i a hd hi.le)^2 +
      diagonalMonomial d 0 (j : ℤ) (b : k) * (scalarLift d hd scalarEta)^4 *
      gammaSpecializedLift d (i-j) (a/b) hd hdiff * gammaSpecializedLift d (i+j) (a*b) hd hs = 0 := by
    apply_fun (diagonalSubring (k := k) d).subtype using Subtype.val_injective
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, Subring.subtype_apply]
    dsimp only [logSpecializedLift, gammaSpecializedLift, diagonalMonomial, scalarLift]
    simpa only [parameterAdditionDefect, PowerSeries.monomial_eq_C_mul_X_pow, pow_zero, mul_one,
      LaurentPolynomial.single_eq_C_mul_T] using parameterAdditionDefect_zero i j a b hji hb
  have h := congrArg (diagonalHom d) he
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    diagonalHom_gammaSpecializedLift, diagonalHom_logSpecializedLift d i a hd hi ha,
    diagonalHom_logSpecializedLift d j b hd hj hb, diagonalHom_monomial,
    Nat.cast_zero, mul_zero, zero_add, diagonalHom_scalar, expand_eta,
    Units.val_div_eq_div_val, Units.val_mul, Nat.cast_sub hji, Nat.cast_add] at h
  unfold AnnularAddition additionNumerator
  rw [← map_sub, ← rawAnnularX_difference d i j (a : k) (b : k) hd, map_sub]
  linear_combination h

lemma annular_addition_chamber [CharZero k] (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b) (hji : j ≤ i) (hs : i+j ≤ d) :
    AnnularAddition d i j a b := by
  exact annular_addition_chamber_units d i j (Units.mk0 a ha.2.2.1)
    (Units.mk0 b hb.2.2.1) ha.1 ha.2.1 hb.2.1 hji hs ha.2.2.2 hb.2.2.2

lemma annular_addition_small_sum [CharZero k] (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b) (hs : i+j ≤ d) :
    AnnularAddition d i j a b := by
  by_cases hji : j ≤ i
  · exact annular_addition_chamber d i j a b ha hb hji hs
  · apply (annular_addition_swap d i j a b ha.1 ha.2.2.1 hb.2.2.1).mpr
    exact annular_addition_chamber d j i b a hb ha (by omega) (by omega)

lemma admissible_reflection (d i : ℕ) (a : k) (ha : Admissible d i a) (hi : 0 < i) :
    Admissible d (d-i) a⁻¹ := by
  have hid := ha.2.1
  refine ⟨ha.1, by omega, inv_ne_zero ha.2.2.1, ?_⟩
  intro hz
  have := ha.2.1
  omega

/-- General addition reduced by the proved reflection symmetries to the closed small-sum chamber. -/
lemma annular_addition_all [CharZero k] (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b) : AnnularAddition d i j a b := by
  by_cases hi : 2*i ≤ d
  · by_cases hj : 2*j ≤ d
    · exact annular_addition_small_sum d i j a b ha hb (by omega)
    · have hj0 : 0 < j := by omega
      apply (annular_addition_reflect_second d i j a b hj0 hb.2.1 ha.2.2.1 hb.2.2.1).mp
      exact annular_addition_small_sum d i (d-j) a b⁻¹ ha (admissible_reflection d j b hb hj0) (by omega)
  · have hi0 : 0 < i := by omega
    apply (annular_addition_reflect_first d i j a b hi0 ha.2.1 ha.2.2.1 hb.2.2.1).mp
    by_cases hj : 2*j ≤ d
    · exact annular_addition_small_sum d (d-i) j a⁻¹ b (admissible_reflection d i a ha hi0) hb (by omega)
    · have hj0 : 0 < j := by omega
      apply (annular_addition_reflect_second d (d-i) j a⁻¹ b hj0 hb.2.1
        (inv_ne_zero ha.2.2.1) hb.2.2.1).mp
      exact annular_addition_small_sum d (d-i) (d-j) a⁻¹ b⁻¹
        (admissible_reflection d i a ha hi0) (admissible_reflection d j b hb hj0) (by omega)

/-- The full literal Tate addition formula, including negative differences and wrapped sums. -/
theorem general_annular_addition [CharZero k] (d i j : ℕ) (a b : k)
    (ha : Admissible d i a) (hb : Admissible d j b) :
    (toLaurent k (tateX d i a) - toLaurent k (tateX d j b)) *
      (gammaLaurent d (i : ℤ) a)^2 * (gammaLaurent d (j : ℤ) b)^2 =
    -HahnSeries.single (j : ℤ) b *
      (toLaurent k (PowerSeries.map (Int.castRingHom k)
        (ArithmeticThetaUnaryProduct.etaProduct d)))^4 *
      gammaLaurent d ((i : ℤ)-(j : ℤ)) (a/b) *
      gammaLaurent d ((i : ℤ)+(j : ℤ)) (a*b) :=
  annular_addition_all d i j a b ha hb

end ArithmeticThetaTateIdentities



#print axioms ArithmeticThetaTateIdentities.gamma_eq_zero_iff
#print axioms ArithmeticThetaTateIdentities.annular_addition_iff_quotient
#print axioms ArithmeticThetaTateIdentities.annular_addition_swap
#print axioms ArithmeticThetaTateIdentities.additionNumerator_eq_zero_iff
#print axioms ArithmeticThetaTateIdentities.annular_addition_of_numerator_zero

#print axioms ArithmeticThetaTateIdentities.degree_two_theta_unique

#print axioms ArithmeticThetaTateIdentities.eulerSeries_mul
#print axioms ArithmeticThetaTateIdentities.finite_log_product

#print axioms ArithmeticThetaTateIdentities.universalGamma_horizontal_derivative

#print axioms ArithmeticThetaTateIdentities.universalGamma_horizontal_numerator

#print axioms ArithmeticThetaTateIdentities.eval_partialGamma_log

#print axioms ArithmeticThetaTateIdentities.literal_difference_log_bridge

#print axioms ArithmeticThetaTateIdentities.normalized_universalGamma_coeff

#print axioms ArithmeticThetaTateIdentities.theta_product_coeff

#print axioms ArithmeticThetaTateIdentities.normalizedTheta_log_recurrence

#print axioms ArithmeticThetaTateIdentities.normalizedAdditionDefect_zero

#print axioms ArithmeticThetaTateIdentities.annular_addition_horizontal_one

#print axioms ArithmeticThetaTateIdentities.annular_addition_horizontal

#print axioms ArithmeticThetaTateIdentities.diagonalValue_mul

#print axioms ArithmeticThetaTateIdentities.partialGamma_growth

#print axioms ArithmeticThetaTateIdentities.parameter_gamma_coeff_stable

#print axioms ArithmeticThetaTateIdentities.diagonalValue_universalGamma

#print axioms ArithmeticThetaTateIdentities.parameterAdditionDefect_zero

#print axioms ArithmeticThetaTateIdentities.specialization_log_factors

#print axioms ArithmeticThetaTateIdentities.general_annular_addition
