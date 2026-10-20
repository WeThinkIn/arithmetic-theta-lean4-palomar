module

public import FormalJacobiTripleProduct

@[expose] public section

namespace ArithmeticThetaUnaryProduct

noncomputable def coneEmbedding : PowerSeries (Polynomial ℤ) →+* PowerSeries (LaurentPolynomial ℤ) :=
  (PowerSeries.rescale (LaurentPolynomial.T (-1))).comp (PowerSeries.map Polynomial.toLaurent)

theorem coneEmbedding_coeff (F : PowerSeries (Polynomial ℤ)) (d : ℕ) :
    PowerSeries.coeff d (coneEmbedding F) =
      LaurentPolynomial.T (-(d : ℤ)) * (PowerSeries.coeff d F).toLaurent := by
  simp [coneEmbedding, PowerSeries.coeff_rescale, PowerSeries.coeff_map, LaurentPolynomial.T_pow]

theorem coneEmbedding_injective : Function.Injective coneEmbedding := by
  intro F G h
  apply PowerSeries.ext
  intro d
  have hd := congrArg (PowerSeries.coeff d) h
  rw [coneEmbedding_coeff, coneEmbedding_coeff] at hd
  apply Polynomial.toLaurent_injective
  exact (mul_right_inj_of_invertible (LaurentPolynomial.T (-(d : ℤ)))).mp hd

theorem coneEmbedding_C (p : Polynomial ℤ) :
    coneEmbedding (PowerSeries.C p) = PowerSeries.C p.toLaurent := by
  apply PowerSeries.ext
  intro d
  rw [coneEmbedding_coeff]
  by_cases hd : d = 0
  · subst d
    simp
  · simp [PowerSeries.coeff_C, hd]

theorem coneEmbedding_X : coneEmbedding PowerSeries.X =
    PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X := by
  simp [coneEmbedding, PowerSeries.map_X, PowerSeries.rescale_X]

theorem coneEmbedding_monomial (r s : ℕ) :
    coneEmbedding (PowerSeries.C (Polynomial.X ^ r) * PowerSeries.X ^ s) =
      PowerSeries.C (LaurentPolynomial.T ((r : ℤ)-(s : ℤ))) * PowerSeries.X ^ s := by
  rw [map_mul, coneEmbedding_C, Polynomial.toLaurent_X_pow,
    map_pow coneEmbedding, coneEmbedding_X, mul_pow, ← map_pow, LaurentPolynomial.T_pow]
  rw [← mul_assoc, ← map_mul, ← LaurentPolynomial.T_add]
  simp only [sub_eq_add_neg, mul_neg_one]

noncomputable def conePartial (N : ℕ) : PowerSeries (Polynomial ℤ) :=
  (1 + PowerSeries.C Polynomial.X) *
    ∏ j ∈ Finset.range N,
      (1 - PowerSeries.C (Polynomial.X ^ (j+1)) * PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (Polynomial.X ^ (j+2)) * PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (Polynomial.X ^ j) * PowerSeries.X ^ (j+1))

theorem coneEmbedding_partial (N : ℕ) :
    coneEmbedding (conePartial N) = ArithmeticThetaDurfee.normalizedFiniteProduct N := by
  unfold conePartial
  rw [map_mul, map_add, map_one, coneEmbedding_C, Polynomial.toLaurent_X, map_prod]
  unfold ArithmeticThetaDurfee.normalizedFiniteProduct
  apply congrArg (fun F : PowerSeries (LaurentPolynomial ℤ) => (1+PowerSeries.C (LaurentPolynomial.T 1))*F)
  apply Finset.prod_congr rfl
  intro j hj
  rw [map_mul, map_mul, map_sub, map_one, coneEmbedding_monomial,
    map_add, map_one, coneEmbedding_monomial, map_add, map_one, coneEmbedding_monomial]
  have h0 : ((j+1 : ℕ) : ℤ)-((j+1 : ℕ) : ℤ)=0 := by omega
  have h1 : ((j+2 : ℕ) : ℤ)-((j+1 : ℕ) : ℤ)=1 := by omega
  have hn : (j : ℤ)-((j+1 : ℕ) : ℤ) = -1 := by omega
  simp only [h0, h1, hn, LaurentPolynomial.T_zero, map_one, one_mul]

noncomputable def coneProduct : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (conePartial d))

theorem coneEmbedding_product : coneEmbedding coneProduct = ArithmeticThetaDurfee.fullProduct := by
  apply PowerSeries.ext
  intro d
  rw [coneEmbedding_coeff]
  simp only [coneProduct, ArithmeticThetaDurfee.fullProduct, PowerSeries.coeff_mk]
  rw [← coneEmbedding_partial, coneEmbedding_coeff]

theorem conePartial_stable (d N : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d (conePartial N) = PowerSeries.coeff d (conePartial d) := by
  have h := ArithmeticThetaDurfee.normalized_partial_stable d N hd
  rw [← coneEmbedding_partial, ← coneEmbedding_partial, coneEmbedding_coeff, coneEmbedding_coeff] at h
  apply Polynomial.toLaurent_injective
  exact (mul_right_inj_of_invertible (LaurentPolynomial.T (-(d : ℤ)))).mp h

open scoped PowerSeries.WithPiTopology

local instance : UniformSpace (Polynomial ℤ) := ⊥
local instance : DiscreteUniformity (Polynomial ℤ) := ⟨rfl⟩

noncomputable def innerEvaluation (A : ℕ) : Polynomial ℤ →+* PowerSeries ℤ :=
  Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.X ^ A)

noncomputable def specialization (D A : ℕ) (hAD : A < D) :
    PowerSeries (Polynomial ℤ) →+* PowerSeries ℤ :=
  PowerSeries.eval₂Hom (φ := innerEvaluation A) continuous_of_discreteTopology
    (PowerSeries.HasSubst.X_pow (Nat.sub_ne_zero_of_lt hAD)).hasEval

theorem specialization_C (D A : ℕ) (hAD : A < D) (p : Polynomial ℤ) :
    specialization D A hAD (PowerSeries.C p) = innerEvaluation A p := by
  rw [specialization, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

theorem specialization_X (D A : ℕ) (hAD : A < D) :
    specialization D A hAD PowerSeries.X = PowerSeries.X^(D-A) := by
  rw [specialization, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

theorem specialization_monomial (D A : ℕ) (hAD : A < D) (r s : ℕ) :
    specialization D A hAD (PowerSeries.C (Polynomial.X^r) * PowerSeries.X^s) =
      PowerSeries.X ^ (A*r + (D-A)*s) := by
  rw [map_mul, specialization_C, map_pow (specialization D A hAD), specialization_X]
  simp only [innerEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, ← pow_mul, ← pow_add]

noncomputable def specializedPartial (D A N : ℕ) : PowerSeries ℤ :=
  (1+PowerSeries.X^A) * ∏ j ∈ Finset.range N,
    (1-PowerSeries.X^(D*(j+1))) * (1+PowerSeries.X^(D*(j+1)+A)) *
      (1+PowerSeries.X^(D*(j+1)-A))

theorem specialization_partial (D A : ℕ) (hAD : A < D) (N : ℕ) :
    specialization D A hAD (conePartial N) = specializedPartial D A N := by
  unfold conePartial
  rw [map_mul, map_add, map_one, specialization_C, map_prod]
  have hi : innerEvaluation A Polynomial.X = (PowerSeries.X : PowerSeries ℤ)^A := by
    simp [innerEvaluation]
  rw [hi]
  unfold specializedPartial
  apply congrArg (fun F : PowerSeries ℤ => (1+PowerSeries.X^A)*F)
  apply Finset.prod_congr rfl
  intro j hj
  rw [map_mul, map_mul, map_sub, map_one, specialization_monomial,
    map_add, map_one, specialization_monomial, map_add, map_one, specialization_monomial]
  have hDA : D-A+A=D := Nat.sub_add_cancel (Nat.le_of_lt hAD)
  have h0 : A*(j+1)+(D-A)*(j+1)=D*(j+1) := by nlinarith
  have h1 : A*(j+2)+(D-A)*(j+1)=D*(j+1)+A := by nlinarith
  have hn : A*j+(D-A)*(j+1)=D*(j+1)-A := by
    have hbound : A ≤ D*(j+1) := by nlinarith
    have heq : A*j+(D-A)*(j+1)+A=D*(j+1) := by nlinarith
    omega
  rw [h0, h1, hn]

theorem specializedPartial_step (D A : ℕ) (hAD : A < D) (d N : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d (specializedPartial D A (N+1)) =
      PowerSeries.coeff d (specializedPartial D A N) := by
  have hD : 1 ≤ D := by omega
  have h0 : d < D*(N+1) := by nlinarith
  have h1 : d < D*(N+1)+A := by omega
  have hn : d < D*(N+1)-A := by
    have hb : A+(N+1) ≤ D*(N+1) := by nlinarith
    omega
  have hp (f : PowerSeries ℤ) (e : ℕ) (he : d < e) :
      PowerSeries.coeff d (f*(1+PowerSeries.X^e)) = PowerSeries.coeff d f := by
    simp [mul_add, PowerSeries.coeff_mul_X_pow', show ¬e≤d by omega]
  have hm (f : PowerSeries ℤ) (e : ℕ) (he : d < e) :
      PowerSeries.coeff d (f*(1-PowerSeries.X^e)) = PowerSeries.coeff d f := by
    simp [mul_sub, PowerSeries.coeff_mul_X_pow', show ¬e≤d by omega]
  have heq : specializedPartial D A (N+1) = specializedPartial D A N *
      (1-PowerSeries.X^(D*(N+1))) * (1+PowerSeries.X^(D*(N+1)+A)) *
      (1+PowerSeries.X^(D*(N+1)-A)) := by
    simp [specializedPartial, Finset.prod_range_succ, mul_assoc]
  rw [heq, hp _ _ hn, hp _ _ h1, hm _ _ h0]

theorem specializedPartial_stable (D A : ℕ) (hAD : A < D) (d N : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d (specializedPartial D A N) =
      PowerSeries.coeff d (specializedPartial D A d) := by
  induction N, hd using Nat.le_induction with
  | base => rfl
  | succ N h ih => rw [specializedPartial_step D A hAD d N h, ih]

noncomputable def specializedProduct (D A : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (specializedPartial D A d))

theorem tendsto_conePartial : Filter.Tendsto conePartial Filter.atTop (nhds coneProduct) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto (Polynomial ℤ) _ _ _).mpr
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d)
  intro N hN
  simpa only [coneProduct, PowerSeries.coeff_mk] using conePartial_stable d N hN

theorem tendsto_specializedPartial (D A : ℕ) (hAD : A < D) :
    Filter.Tendsto (specializedPartial D A) Filter.atTop (nhds (specializedProduct D A)) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mpr
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d)
  intro N hN
  simpa only [specializedProduct, PowerSeries.coeff_mk] using specializedPartial_stable D A hAD d N hN

theorem continuous_specialization (D A : ℕ) (hAD : A < D) : Continuous (specialization D A hAD) := by
  rw [specialization, PowerSeries.coe_eval₂Hom]
  exact PowerSeries.continuous_eval₂ continuous_of_discreteTopology
    (PowerSeries.HasSubst.X_pow (Nat.sub_ne_zero_of_lt hAD)).hasEval

theorem specialization_product (D A : ℕ) (hAD : A < D) :
    specialization D A hAD coneProduct = specializedProduct D A := by
  have h := (continuous_specialization D A hAD).tendsto coneProduct |>.comp tendsto_conePartial
  simp only [Function.comp_def, specialization_partial] at h
  exact tendsto_nhds_unique h (tendsto_specializedPartial D A hAD)

theorem shifted_polynomial_coefficient (p : Polynomial ℤ) (d l : ℕ) :
    (LaurentPolynomial.T (-(d : ℤ)) * p.toLaurent).coeff ((l : ℤ)-(d : ℤ)) = p.coeff l := by
  rw [mul_comm]
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [add_mul, hp, hr]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, LaurentPolynomial.mul_T_assoc,
      ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Polynomial.coeff_monomial]
    have hiff : (n : ℤ)+ -(d : ℤ)=(l : ℤ)-(d : ℤ) ↔ n=l := by omega
    simp only [hiff, eq_comm]

theorem coneProduct_coefficient (d l : ℕ) :
    (PowerSeries.coeff d coneProduct).coeff l =
      if ((l : ℤ)-(d : ℤ))*((l : ℤ)-(d : ℤ)-1)=2*(d : ℤ) then 1 else 0 := by
  have h := congrArg (fun F : PowerSeries (LaurentPolynomial ℤ) =>
    (PowerSeries.coeff d F).coeff ((l : ℤ)-(d : ℤ))) coneEmbedding_product
  rw [coneEmbedding_coeff, shifted_polynomial_coefficient,
    ArithmeticThetaDurfee.full_jacobi_double_coefficient] at h
  exact h

theorem coneProduct_coeff_polynomial (d : ℕ) :
    PowerSeries.coeff d coneProduct =
      ∑ l ∈ Finset.range (2*d+2), Polynomial.monomial l
        (if ((l : ℤ)-(d : ℤ))*((l : ℤ)-(d : ℤ)-1)=2*(d : ℤ) then (1 : ℤ) else 0) := by
  apply Polynomial.ext
  intro l
  rw [coneProduct_coefficient, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single l]
  · simp
  · intro j hj hne
    simp [Polynomial.coeff_monomial, hne]
  · intro hl
    have hn : ¬ ((l : ℤ)-(d : ℤ))*((l : ℤ)-(d : ℤ)-1)=2*(d : ℤ) := by
      intro h
      have hb := ArithmeticThetaDurfee.jacobi_support_bound d ((l : ℤ)-(d : ℤ)) h
      simp only [Finset.mem_range] at hl
      omega
    simp [hn]

theorem specialization_coefficient (D A : ℕ) (hAD : A < D)
    (F : PowerSeries (Polynomial ℤ)) (n : ℕ) :
    PowerSeries.coeff n (specialization D A hAD F) =
      ∑ d ∈ Finset.range (n+1), PowerSeries.coeff n
        (innerEvaluation A (PowerSeries.coeff d F) * PowerSeries.X ^ ((D-A)*d)) := by
  rw [specialization, PowerSeries.coe_eval₂Hom]
  have hs := PowerSeries.hasSum_eval₂ (φ := innerEvaluation A) continuous_of_discreteTopology
    (PowerSeries.HasSubst.X_pow (Nat.sub_ne_zero_of_lt hAD)).hasEval F
  have hc := hs.map (PowerSeries.coeff n).toAddMonoidHom
    (PowerSeries.WithPiTopology.continuous_coeff ℤ n)
  simp only [LinearMap.toAddMonoidHom_coe, Function.comp_def, ← pow_mul] at hc
  rw [← hc.tsum_eq]
  apply tsum_eq_sum
  intro d hd
  have hn : n < d := by simp only [Finset.mem_range] at hd; omega
  have he : n < (D-A)*d := by
    have hpos : 1 ≤ D-A := by omega
    nlinarith
  rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]

theorem specialized_product_double_sum (D A : ℕ) (hAD : A < D) (n : ℕ) :
    PowerSeries.coeff n (specializedProduct D A) =
      ∑ d ∈ Finset.range (n+1), ∑ l ∈ Finset.range (2*d+2),
        if ((l : ℤ)-(d : ℤ))*((l : ℤ)-(d : ℤ)-1)=2*(d : ℤ) ∧
            n=A*l+(D-A)*d then (1 : ℤ) else 0 := by
  rw [← specialization_product D A hAD, specialization_coefficient]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coneProduct_coeff_polynomial, map_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [innerEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  by_cases htri : ((l : ℤ)-(d : ℤ))*((l : ℤ)-(d : ℤ)-1)=2*(d : ℤ)
  · simp [htri, ← pow_mul, ← pow_add, PowerSeries.coeff_X_pow]
  · simp [htri]

theorem triangular_exists (k : ℤ) : ∃ d : ℕ, k*(k-1)=2*(d : ℤ) := by
  cases k with
  | ofNat k => exact ⟨k*(k-1)/2, (ArithmeticThetaDurfee.integer_triangular_nonneg_iff k _).mpr rfl⟩
  | negSucc k =>
    refine ⟨(k+1)*(k+2)/2, ?_⟩
    simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, neg_add_rev] using (ArithmeticThetaDurfee.integer_triangular_neg_iff (k+1) ((k+1)*(k+2)/2)).mpr (by congr 1; ring)

theorem weighted_triangular_bound (D A n d : ℕ) (k : ℤ) (hAD : A < D)
    (ht : k*(k-1)=2*(d : ℤ))
    (hw : (D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ)) :
    d ≤ n ∧ -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ)+1 := by
  have hb := ArithmeticThetaDurfee.jacobi_support_bound d k ht
  have hDa : (A : ℤ)+1 ≤ D := by exact_mod_cast hAD
  have hA : (0 : ℤ) ≤ A := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  have hp := mul_nonneg hA (show 0 ≤ (d : ℤ)+k by omega)
  have hp' := mul_nonneg (show 0 ≤ (D : ℤ)-A-1 by omega) hd
  have he : (D : ℤ)*(d : ℤ)+(A : ℤ)*k=n := by nlinarith [ht]
  have hdN : (d : ℤ) ≤ n := by nlinarith
  constructor
  · exact_mod_cast hdN
  · omega

theorem weighted_witness (D A n : ℕ) (k : ℤ) (hAD : A < D)
    (hw : (D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ)) :
    ∃ d l : ℕ, d < n+1 ∧ l < 2*d+2 ∧
      (l : ℤ)-(d : ℤ)=k ∧ k*(k-1)=2*(d : ℤ) ∧ n=A*l+(D-A)*d := by
  obtain ⟨d, ht⟩ := triangular_exists k
  have hb := ArithmeticThetaDurfee.jacobi_support_bound d k ht
  have hdn := (weighted_triangular_bound D A n d k hAD ht hw).1
  let l := ((d : ℤ)+k).toNat
  have hl : (l : ℤ)=(d : ℤ)+k := Int.toNat_of_nonneg (by omega)
  refine ⟨d, l, by omega, by omega, by omega, ht, ?_⟩
  have hsub : ((D-A : ℕ) : ℤ)=(D : ℤ)-(A : ℤ) := Int.natCast_sub (by omega)
  have he : (n : ℤ)=(A : ℤ)*l+((D-A : ℕ) : ℤ)*d := by rw [hsub, hl]; nlinarith [ht]
  exact_mod_cast he

theorem specialized_product_coefficient (D A : ℕ) (hAD : A < D) (n : ℕ) :
    PowerSeries.coeff n (specializedProduct D A) =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1),
        if (D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ) then (1 : ℤ) else 0 := by
  classical
  rw [specialized_product_double_sum D A hAD n, Finset.sum_sigma']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun (p : (d : ℕ) × ℕ) _ => (p.2 : ℤ)-(p.1 : ℤ))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hp
    obtain ⟨⟨hd, hl⟩, ht, hw⟩ := hp
    have hsub : ((D-A : ℕ) : ℤ)=(D : ℤ)-(A : ℤ) := Int.natCast_sub (by omega)
    have hwZ : (n : ℤ)=(A : ℤ)*p.2+((D-A : ℕ) : ℤ)*p.1 := by exact_mod_cast hw
    rw [hsub] at hwZ
    have he : (D : ℤ)*((p.2 : ℤ)-(p.1 : ℤ))*((p.2 : ℤ)-(p.1 : ℤ)-1)+
        2*(A : ℤ)*((p.2 : ℤ)-(p.1 : ℤ))=2*(n : ℤ) := by nlinarith [ht]
    have hb := (weighted_triangular_bound D A n p.1 ((p.2 : ℤ)-(p.1 : ℤ)) hAD ht he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hb, he⟩
  · intro p hp q hq heq
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hp hq
    have ht1 := hp.2.1
    have ht2 := hq.2.1
    rw [heq] at ht1
    have hd : p.1=q.1 := by omega
    have hl : p.2=q.2 := by omega
    cases p
    cases q
    simp_all
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨d,l,hd,hl,hk',ht,hw⟩ := weighted_witness D A n k hAD hk.2
    refine ⟨⟨d,l⟩, ?_, hk'⟩
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]
    exact ⟨⟨hd,hl⟩, by rw [hk']; exact ht, hw⟩
  · intro p hp
    rfl

theorem formal_specialized_jacobi (D A : ℕ) (hAD : A < D) :
    specializedProduct D A = PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1),
        if (D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ) then (1 : ℤ) else 0) := by
  apply PowerSeries.ext
  intro n
  simpa only [PowerSeries.coeff_mk] using specialized_product_coefficient D A hAD n

theorem weighted_nonnegative (D A : ℕ) (hAD : A < D) (k : ℤ) :
    0 ≤ (D : ℤ)*k*(k-1)+2*(A : ℤ)*k := by
  obtain ⟨d, ht⟩ := triangular_exists k
  have hb := ArithmeticThetaDurfee.jacobi_support_bound d k ht
  have hp := mul_nonneg (show (0 : ℤ) ≤ A by positivity)
    (show 0 ≤ (d : ℤ)+k by omega)
  have hp' := mul_nonneg (show 0 ≤ (D : ℤ)-A by omega) (show (0 : ℤ) ≤ d by positivity)
  nlinarith [ht]

theorem shifted_product_coefficient (D A B : ℕ) (hAD : A < D) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X^B * specializedProduct D A) =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1),
        if 2*(B : ℤ)+(D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ) then (1 : ℤ) else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hB : B ≤ n
  · rw [if_pos hB, specialized_product_coefficient D A hAD]
    have hsub : ((n-B : ℕ) : ℤ)=(n : ℤ)-(B : ℤ) := Int.natCast_sub hB
    have heq : ∀ k : ℤ,
        ((D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*((n-B : ℕ) : ℤ)) ↔
        (2*(B : ℤ)+(D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*(n : ℤ)) := by
      intro k
      rw [hsub]
      constructor <;> intro h <;> linarith
    simp only [heq]
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hnot
      apply if_neg
      intro he
      obtain ⟨d, ht⟩ := triangular_exists k
      have hw : (D : ℤ)*k*(k-1)+2*(A : ℤ)*k=2*((n-B : ℕ) : ℤ) := (heq k).mpr he
      have hb := (weighted_triangular_bound D A (n-B) d k hAD ht hw).2
      exact hnot (Finset.mem_Icc.mpr hb)
  · rw [if_neg hB]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    apply if_neg
    have hp := weighted_nonnegative D A hAD k
    omega

noncomputable def unaryA (m : ℕ) (ν : ℤ) : ℕ :=
  (12*(m : ℤ)^2+24*(m : ℤ)*ν).toNat
noncomputable def unaryB (ν : ℤ) : ℕ := (12*ν^2).toNat

theorem unary_parameters (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    (unaryA m ν : ℤ)=12*(m : ℤ)^2+24*(m : ℤ)*ν ∧ unaryA m ν < 24*m^2 := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hpos := mul_nonneg (show 0 ≤ 12*(m : ℤ) by positivity) (show 0 ≤ (m : ℤ)+2*ν by omega)
  have hlt := mul_pos (show 0 < 12*(m : ℤ) by positivity) (show 0 < (m : ℤ)-2*ν by omega)
  have hA : (unaryA m ν : ℤ)=12*(m : ℤ)^2+24*(m : ℤ)*ν := by
    unfold unaryA
    apply Int.toNat_of_nonneg
    nlinarith
  refine ⟨hA, ?_⟩
  have hh : (unaryA m ν : ℤ) < (24*m^2 : ℕ) := by push_cast; nlinarith
  exact_mod_cast hh

theorem unaryB_cast (ν : ℤ) : (unaryB ν : ℤ)=12*ν^2 := by
  apply Int.toNat_of_nonneg
  positivity

theorem unary_exponent_identity (m : ℕ) (ν k : ℤ) :
    2*(12*ν^2)+(24*(m : ℤ)^2)*k*(k-1)+2*(12*(m : ℤ)^2+24*(m : ℤ)*ν)*k =
      2*(12*((m : ℤ)*k+ν)^2) := by ring

noncomputable def clearedUnaryTheta (m : ℕ) (ν : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1),
    if 12*((m : ℤ)*k+ν)^2=(n : ℤ) then (1 : ℤ) else 0)

theorem cleared_unary_product (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    clearedUnaryTheta m ν = PowerSeries.X^(unaryB ν) * specializedProduct (24*m^2) (unaryA m ν) := by
  obtain ⟨hA, hAD⟩ := unary_parameters m ν hm hν
  apply PowerSeries.ext
  intro n
  rw [shifted_product_coefficient _ _ _ hAD]
  simp only [clearedUnaryTheta, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [unaryB_cast, hA]
  have hD : ((24*m^2 : ℕ) : ℤ)=24*(m : ℤ)^2 := by push_cast; rfl
  rw [hD, unary_exponent_identity]
  have hi : (12*((m : ℤ)*k+ν)^2=(n : ℤ)) ↔ (2*(12*((m : ℤ)*k+ν)^2)=2*(n : ℤ)) := by omega
  simp only [hi]

noncomputable def etaPartial (D N : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range N, (1-PowerSeries.X^(D*(j+1)))
noncomputable def siegelPartial (D A N : ℕ) : PowerSeries ℤ :=
  (1+PowerSeries.X^A) * ∏ j ∈ Finset.range N,
    (1+PowerSeries.X^(D*(j+1)+A))*(1+PowerSeries.X^(D*(j+1)-A))
noncomputable def etaProduct (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (etaPartial D d))
noncomputable def siegelProduct (D A : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (siegelPartial D A d))

theorem etaPartial_stable (D : ℕ) (hD : 0<D) (d N : ℕ) (hd : d≤N) :
    PowerSeries.coeff d (etaPartial D N) = PowerSeries.coeff d (etaPartial D d) := by
  induction N, hd using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    rw [etaPartial, Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      PowerSeries.coeff_mul_X_pow', if_neg (by nlinarith), sub_zero]
    exact ih

theorem siegelPartial_stable (D A : ℕ) (hAD : A<D) (d N : ℕ) (hd : d≤N) :
    PowerSeries.coeff d (siegelPartial D A N) = PowerSeries.coeff d (siegelPartial D A d) := by
  induction N, hd using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    have hD : 0<D := by omega
    have hp : d<D*(N+1)+A := by nlinarith
    have hn : d<D*(N+1)-A := by
      have hh : A+N+1≤D*(N+1) := by nlinarith
      omega
    have he : siegelPartial D A (N+1) = siegelPartial D A N *
        (1+PowerSeries.X^(D*(N+1)+A))*(1+PowerSeries.X^(D*(N+1)-A)) := by
      simp [siegelPartial, Finset.prod_range_succ, mul_assoc]
    have hs (F : PowerSeries ℤ) (e : ℕ) (he : d<e) :
        PowerSeries.coeff d (F*(1+PowerSeries.X^e))=PowerSeries.coeff d F := by
      simp [mul_add, PowerSeries.coeff_mul_X_pow', show ¬e≤d by omega]
    rw [he, hs _ _ hn, hs _ _ hp, ih]

theorem tendsto_etaPartial (D : ℕ) (hD : 0<D) :
    Filter.Tendsto (etaPartial D) Filter.atTop (nhds (etaProduct D)) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mpr
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d)
  intro N hN
  simpa only [etaProduct, PowerSeries.coeff_mk] using etaPartial_stable D hD d N hN

theorem tendsto_siegelPartial (D A : ℕ) (hAD : A<D) :
    Filter.Tendsto (siegelPartial D A) Filter.atTop (nhds (siegelProduct D A)) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mpr
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d)
  intro N hN
  simpa only [siegelProduct, PowerSeries.coeff_mk] using siegelPartial_stable D A hAD d N hN

theorem eta_mul_siegel (D A : ℕ) (hAD : A<D) :
    etaProduct D * siegelProduct D A = specializedProduct D A := by
  have he (N : ℕ) : etaPartial D N * siegelPartial D A N = specializedPartial D A N := by
    unfold etaPartial siegelPartial specializedPartial
    simp only [Finset.prod_mul_distrib]
    ring
  have h := (tendsto_etaPartial D (by omega)).mul (tendsto_siegelPartial D A hAD)
  simp only [he] at h
  exact tendsto_nhds_unique h (tendsto_specializedPartial D A hAD)

theorem bernoulli_prefactor (a : ℚ) :
    1/24+(a^2-a+1/6)/2=(a-1/2)^2/2 := by ring

theorem cleared_siegel_exponent (m : ℕ) (ν : ℤ) (hm : 0 < m) :
    (24*(m : ℚ)^2)*(((ν : ℚ)/m+1/2)^2-((ν : ℚ)/m+1/2)+1/6)/2 =
      12*(ν : ℚ)^2-(m : ℚ)^2 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hmQ]
  ring

theorem rational_characteristic_range (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    0≤(ν : ℚ)/m+1/2 ∧ (ν : ℚ)/m+1/2<1 := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hlo : -(m : ℚ)≤2*(ν : ℚ) := by exact_mod_cast hν.1
  have hhi : 2*(ν : ℚ)<(m : ℚ) := by exact_mod_cast hν.2
  constructor
  · have h : -(1/2 : ℚ) ≤ (ν : ℚ)/m := (le_div_iff₀ hmQ).mpr (by linarith)
    linarith
  · have h : (ν : ℚ)/m < (1/2 : ℚ) := (div_lt_iff₀ hmQ).mpr (by linarith)
    linarith

noncomputable def unaryPhase (m : ℕ) (ν : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (((ν : ℂ)/(m : ℂ)+1/2)-1)/2)

noncomputable def complexLaurent : PowerSeries ℤ →+* LaurentSeries ℂ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map (Int.castRingHom ℂ))

noncomputable def clearedEta (m : ℕ) : LaurentSeries ℂ :=
  HahnSeries.single ((m : ℤ)^2) 1 * complexLaurent (etaProduct (24*m^2))

noncomputable def clearedSiegel (m : ℕ) (ν : ℤ) : LaurentSeries ℂ :=
  HahnSeries.single (12*ν^2-(m : ℤ)^2) (-unaryPhase m ν) *
    complexLaurent (siegelProduct (24*m^2) (unaryA m ν))

theorem complexLaurent_X_pow (B : ℕ) :
    complexLaurent (PowerSeries.X^B) = HahnSeries.single (B : ℤ) 1 := by
  simp [complexLaurent, HahnSeries.ofPowerSeries_X_pow]

theorem unary_phase_cancel (m : ℕ) (ν : ℤ) :
    (-((unaryPhase m ν)⁻¹))*(-unaryPhase m ν)=1 := by
  simp [unaryPhase, Complex.exp_ne_zero]

theorem cleared_unary_eta_siegel (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    complexLaurent (clearedUnaryTheta m ν) =
      HahnSeries.single 0 (-((unaryPhase m ν)⁻¹)) * clearedEta m * clearedSiegel m ν := by
  obtain ⟨hA,hAD⟩ := unary_parameters m ν hm hν
  rw [cleared_unary_product m ν hm hν, map_mul, complexLaurent_X_pow, unaryB_cast]
  unfold clearedEta clearedSiegel
  have hrearr :
      HahnSeries.single 0 (-((unaryPhase m ν)⁻¹)) *
        (HahnSeries.single ((m : ℤ)^2) 1 * complexLaurent (etaProduct (24*m^2))) *
        (HahnSeries.single (12*ν^2-(m : ℤ)^2) (-unaryPhase m ν) *
          complexLaurent (siegelProduct (24*m^2) (unaryA m ν))) =
      (HahnSeries.single 0 (-((unaryPhase m ν)⁻¹)) * HahnSeries.single ((m : ℤ)^2) 1 *
        HahnSeries.single (12*ν^2-(m : ℤ)^2) (-unaryPhase m ν)) *
      complexLaurent (etaProduct (24*m^2)*siegelProduct (24*m^2) (unaryA m ν)) := by
    rw [map_mul]
    ring
  rw [hrearr, HahnSeries.single_mul_single, HahnSeries.single_mul_single,
    zero_add, mul_one, unary_phase_cancel, eta_mul_siegel _ _ hAD]
  have hexp : (m : ℤ)^2+(12*ν^2-(m : ℤ)^2)=12*ν^2 := by ring
  rw [hexp]

theorem unary_square_support (m n : ℕ) (ν k : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ))
    (hk : 12*((m : ℤ)*k+ν)^2=(n : ℤ)) :
    -(n : ℤ)≤k ∧ k≤(n : ℤ)+1 := by
  obtain ⟨hA,hAD⟩ := unary_parameters m ν hm hν
  obtain ⟨d,ht⟩ := triangular_exists k
  have hw : 2*(unaryB ν : ℤ)+((24*m^2 : ℕ) : ℤ)*k*(k-1)+2*(unaryA m ν : ℤ)*k=2*(n : ℤ) := by
    rw [unaryB_cast, hA]
    push_cast
    rw [unary_exponent_identity, hk]
  have hp := weighted_nonnegative (24*m^2) (unaryA m ν) hAD k
  have hBn : unaryB ν≤n := by omega
  have hsub : ((n-unaryB ν : ℕ) : ℤ)=(n : ℤ)-(unaryB ν : ℤ) := Int.natCast_sub hBn
  have he : ((24*m^2 : ℕ) : ℤ)*k*(k-1)+2*(unaryA m ν : ℤ)*k=2*((n-unaryB ν : ℕ) : ℤ) := by
    rw [hsub]
    linarith
  have hb := (weighted_triangular_bound (24*m^2) (unaryA m ν) (n-unaryB ν) d k hAD ht he).2
  omega

theorem clearedUnaryTheta_coefficient_card (m n : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    PowerSeries.coeff n (clearedUnaryTheta m ν) =
      (Nat.card {k : ℤ // 12*((m : ℤ)*k+ν)^2=(n : ℤ)} : ℤ) := by
  classical
  let s := (Finset.Icc (-(n : ℤ)) ((n : ℤ)+1)).filter
    (fun k => 12*((m : ℤ)*k+ν)^2=(n : ℤ))
  let e : {k : ℤ // 12*((m : ℤ)*k+ν)^2=(n : ℤ)} ≃ {k // k ∈ s} :=
    { toFun := fun k => ⟨k.1, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr (unary_square_support m n ν k.1 hm hν k.2), k.2⟩⟩
      invFun := fun k => ⟨k.1, (Finset.mem_filter.mp k.2).2⟩
      left_inv := fun k => rfl
      right_inv := fun k => rfl }
  have hc := Nat.card_congr e
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_coe]
  simp only [clearedUnaryTheta, PowerSeries.coeff_mk]
  change _ = (s.card : ℤ)
  rw [← Finset.sum_filter]
  simp [s]

theorem unary_residue_card (m n : ℕ) (ν : ℤ) (hm : 0 < m) :
    Nat.card {k : ℤ // 12*((m : ℤ)*k+ν)^2=(n : ℤ)} =
      Nat.card {r : ℤ // (m : ℤ) ∣ r-ν ∧ 12*r^2=(n : ℤ)} := by
  let f : {k : ℤ // 12*((m : ℤ)*k+ν)^2=(n : ℤ)} →
      {r : ℤ // (m : ℤ) ∣ r-ν ∧ 12*r^2=(n : ℤ)} :=
    fun k => ⟨(m : ℤ)*k.1+ν, ⟨⟨k.1, by ring⟩, k.2⟩⟩
  have hinj : Function.Injective f := by
    intro k l h
    have he := congrArg Subtype.val h
    change (m : ℤ)*k.1+ν=(m : ℤ)*l.1+ν at he
    have hmZ : (m : ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
    apply Subtype.ext
    exact mul_left_cancel₀ hmZ (add_right_cancel he)
  have hsurj : Function.Surjective f := by
    intro r
    obtain ⟨k,hk⟩ := r.2.1
    have he : (m : ℤ)*k+ν=r.1 := by omega
    refine ⟨⟨k, ?_⟩, ?_⟩
    · rw [he]
      exact r.2.2
    · apply Subtype.ext
      exact he
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)

theorem clearedUnaryTheta_residue_coefficient (m n : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    PowerSeries.coeff n (clearedUnaryTheta m ν) =
      (Nat.card {r : ℤ // (m : ℤ) ∣ r-ν ∧ 12*r^2=(n : ℤ)} : ℤ) := by
  rw [clearedUnaryTheta_coefficient_card m n ν hm hν, unary_residue_card m n ν hm]

theorem cleared_unary_exponent (m : ℕ) (r : ℤ) (hm : 0 < m) :
    (24*(m : ℚ))*((r : ℚ)^2/(2*m))=12*(r : ℚ)^2 := by
  have hmQ : (m : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hmQ]
  ring

theorem unaryPhase_inverse (m : ℕ) (ν : ℤ) :
    (unaryPhase m ν)⁻¹ =
      Complex.exp (-Real.pi * Complex.I * (((ν : ℂ)/(m : ℂ)+1/2)-1)/2) := by
  rw [unaryPhase, ← Complex.exp_neg]
  congr 1
  ring

theorem cleared_unary_eta_siegel_exact_phase (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    complexLaurent (clearedUnaryTheta m ν) =
      HahnSeries.single 0 (-Complex.exp (-Real.pi * Complex.I * (((ν : ℂ)/(m : ℂ)+1/2)-1)/2)) *
        clearedEta m * clearedSiegel m ν := by
  rw [← unaryPhase_inverse]
  exact cleared_unary_eta_siegel m ν hm hν

theorem unaryPhase_root (m : ℕ) (ν : ℤ) (hm : 0 < m) :
    unaryPhase m ν ^ (8*m) = 1 := by
  have hmC : (m : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold unaryPhase
  rw [← Complex.exp_nat_mul]
  have he : ((8*m : ℕ) : ℂ)*(Real.pi * Complex.I * (((ν : ℂ)/(m : ℂ)+1/2)-1)/2) =
      ((2*ν-(m : ℤ) : ℤ) : ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    field_simp [hmC]
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem unary_characteristic_exponent (m : ℕ) (ν : ℤ) (hm : 0 < m)
    (hν : -(m : ℤ)≤2*ν ∧ 2*ν<(m : ℤ)) :
    (24*(m : ℚ)^2)*((ν : ℚ)/m+1/2)=(unaryA m ν : ℚ) := by
  have hmQ : (m : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hA := (unary_parameters m ν hm hν).1
  have hAQ : (unaryA m ν : ℚ)=12*(m : ℚ)^2+24*(m : ℚ)*(ν : ℚ) := by exact_mod_cast hA
  rw [hAQ]
  field_simp [hmQ]
  ring

end ArithmeticThetaUnaryProduct

#print axioms ArithmeticThetaUnaryProduct.coneEmbedding_product
#print axioms ArithmeticThetaUnaryProduct.specialization_partial
#print axioms ArithmeticThetaUnaryProduct.specialization_product
#print axioms ArithmeticThetaUnaryProduct.specialized_product_double_sum

#print axioms ArithmeticThetaUnaryProduct.formal_specialized_jacobi
#print axioms ArithmeticThetaUnaryProduct.cleared_unary_product
#print axioms ArithmeticThetaUnaryProduct.cleared_unary_eta_siegel

#print axioms ArithmeticThetaUnaryProduct.clearedUnaryTheta_residue_coefficient

#print axioms ArithmeticThetaUnaryProduct.unaryPhase_root
