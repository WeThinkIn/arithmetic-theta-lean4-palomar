import UnaryKatoPowerDefinitionsR0160

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnaryKatoPowerR0160
namespace LiteralSiegelGamma
open ArithmeticThetaUnaryProduct

private def finiteProduct (D A N : ℕ) : PowerSeries ℤ :=
  (∏ l ∈ Finset.range N, (1 + PowerSeries.X ^ (D*l+A))) *
  (∏ l ∈ Finset.range N, (1 + PowerSeries.X ^ (D*(l+1)-A)))

private theorem partial_endpoint (D A N : ℕ) :
    finiteProduct D A N * (1 + PowerSeries.X^(D*N+A)) = siegelPartial D A N := by
  induction N with
  | zero => simp [finiteProduct, siegelPartial]
  | succ N ih =>
    have hs : siegelPartial D A (N+1) = siegelPartial D A N *
        (1+PowerSeries.X^(D*(N+1)+A)) * (1+PowerSeries.X^(D*(N+1)-A)) := by
      simp [siegelPartial, Finset.prod_range_succ, mul_assoc]
    rw [hs, ← ih]
    simp only [finiteProduct, Finset.prod_range_succ]
    ring

private theorem partial_coeff (D A N b : ℕ) (hAD : A < D) (hb : b < N) :
    PowerSeries.coeff b (finiteProduct D A N) = PowerSeries.coeff b (siegelProduct D A) := by
  have he : b < D*N+A := by nlinarith
  have hc := congrArg (PowerSeries.coeff b) (partial_endpoint D A N)
  simp only [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow',
    if_neg (show ¬D*N+A ≤ b by omega), add_zero] at hc
  rw [hc]
  simpa only [siegelProduct, PowerSeries.coeff_mk] using
    siegelPartial_stable D A hAD b N (by omega)

private def reparam (k : Type) [Field k] (d : ℕ) (hd : 0 < d) :
    PowerSeries ℤ →+* LaurentSeries k :=
  (integerSeries k).comp
    (PowerSeries.substAlgHom (R := ℤ) (PowerSeries.HasSubst.X_pow (Nat.ne_of_gt hd))).toRingHom

private theorem reparam_apply (k : Type) [Field k] (d : ℕ) (hd : 0 < d)
    (f : PowerSeries ℤ) :
    reparam k d hd f = integerSeries k (PowerSeries.subst (PowerSeries.X^d) f) := by
  simp only [reparam, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, PowerSeries.coe_substAlgHom]

private theorem reparam_X_pow (k : Type) [Field k] (d : ℕ) (hd : 0 < d) (b : ℕ) :
    reparam k d hd (PowerSeries.X^b) = HahnSeries.single ((d*b : ℕ) : ℤ) (1 : k) := by
  simp [reparam, PowerSeries.substAlgHom_X, integerSeries, ← pow_mul,
    HahnSeries.ofPowerSeries_X_pow]

private theorem reparam_partial (k : Type) [Field k] (d D A N : ℕ)
    (hd : 0 < d) (hAD : A < D) :
    reparam k d hd (finiteProduct D A N) =
      ArithmeticThetaLaurentNormR0064.Partial k (d*D) (d*A) (-1) N := by
  have hb (l : ℕ) : A ≤ D*(l+1) := by nlinarith
  simp only [finiteProduct, map_mul, map_prod, map_add, map_one, reparam_X_pow,
    ArithmeticThetaLaurentNormR0064.Partial, inv_neg, inv_one, map_neg,
    neg_mul, one_mul, sub_neg_eq_add]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro l hl <;>
    congr 2 <;> push_cast [Int.natCast_sub (hb l)] <;> congr 1 <;> ring

private theorem reparam_coeff_congr (k : Type) [Field k] (d : ℕ) (hd : 0 < d)
    (f g : PowerSeries ℤ) (n e : ℤ) (he : e ≤ n)
    (h : ∀ b : ℕ, b ≤ n.toNat → PowerSeries.coeff b f = PowerSeries.coeff b g) :
    (reparam k d hd f).coeff e = (reparam k d hd g).coeff e := by
  rw [reparam_apply, reparam_apply]
  change ((PowerSeries.map (Int.castRingHom k)
    (PowerSeries.subst (PowerSeries.X^d) f) : PowerSeries k) : LaurentSeries k).coeff e =
    ((PowerSeries.map (Int.castRingHom k)
    (PowerSeries.subst (PowerSeries.X^d) g) : PowerSeries k) : LaurentSeries k).coeff e
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · rfl
  · simp only [PowerSeries.coeff_map, PowerSeries.coeff_subst_X_pow (Nat.ne_of_gt hd)]
    have habs : (e.natAbs : ℤ) = e := by
      rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ e)]
    have hb : e.natAbs / d ≤ n.toNat := by
      have := Nat.div_le_self e.natAbs d
      omega
    rw [h _ hb]

end LiteralSiegelGamma

/-- The literal gamma limit of the complete Siegel product, including the endpoint A=0. -/
theorem literal_siegel_gamma : ∀ (k : Type) [Field k] [CharZero k] (d D A : ℕ),
    0 < d → 0 < D → A < D →
    ArithmeticThetaLaurentNormR0064.IsGamma k (d*D) (d*A) (-1)
      (integerSeries k (PowerSeries.subst (PowerSeries.X^d)
        (ArithmeticThetaUnaryProduct.siegelProduct D A))) := by
  intro k _ _ d D A hd _hD hAD n
  refine ⟨n.toNat+1, ?_⟩
  intro N hN e he
  rw [← LiteralSiegelGamma.reparam_partial k d D A N hd hAD]
  rw [← LiteralSiegelGamma.reparam_apply k d hd]
  apply LiteralSiegelGamma.reparam_coeff_congr k d hd _ _ n e he
  intro b hb
  exact LiteralSiegelGamma.partial_coeff D A N b hAD (by omega)

end ArithmeticThetaUnaryKatoPowerR0160

#print axioms ArithmeticThetaUnaryKatoPowerR0160.literal_siegel_gamma
