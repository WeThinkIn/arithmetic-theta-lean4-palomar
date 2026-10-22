module

public import FaithfulAnnularEvaluationR0156
public import LocalGammaProviderBridgeR0065
public import LaurentGammaNonzeroR0064
public import LaurentGammaExistenceR0064

@[expose] public section

/-! Evaluation of the complete gamma products, at every boundary and interior chart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace FullGammaEvaluation
open ArithmeticThetaGenericOverlapR0065

private lemma filtered_mul_coeff_zero (F : Type) [Field F]
    (H f : LaurentSeries F) (d : ℕ) (e : ℤ)
    (hf : ∀ i : ℤ, i < (d : ℤ) → f.coeff i = 0)
    (he : e < H.order + (d : ℤ)) : (H * f).coeff e = 0 := by
  by_cases hH : H = 0
  · simp [hH]
  by_cases hzero : f = 0
  · simp [hzero]
  have horder : (d : ℤ) ≤ f.order := by
    by_contra h
    exact hzero (HahnSeries.coeff_order_eq_zero.mp (hf _ (by omega)))
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [HahnSeries.order_mul hH hzero]
  omega

private lemma t_pow_single (F : Type) [Field F] (n : ℕ) :
    ArithmeticThetaLaurentNormR0064.t F ^ n = HahnSeries.single (n : ℤ) (1 : F) := by
  simp [ArithmeticThetaLaurentNormR0064.t, HahnSeries.single_pow]

private lemma genericSection_leftFactor (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (r j l : ℕ) :
    σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.leftFactor k r j l)) =
      1 - HahnSeries.C α *
        HahnSeries.single ((r : ℤ) * l + j) (1 : F) := by
  simp only [ArithmeticThetaCorrectedGammaR0061.leftFactor,
    map_sub, map_one, map_mul, map_pow]
  change 1 - σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) ^ _ *
      σ
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = _
  rw [ht, hx]
  rw [t_pow_single]
  rw [mul_comm (HahnSeries.single
    (ArithmeticThetaCorrectedGammaR0061.leftExponent r j l : ℤ) (1 : F))
    (HahnSeries.C α)]
  simp [ArithmeticThetaCorrectedGammaR0061.leftExponent]

private lemma genericSection_rightFactor (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (r j l : ℕ) (hj : j < r) :
    σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.rightFactor k r j (l + 1))) =
      1 - HahnSeries.C α⁻¹ *
        HahnSeries.single ((r : ℤ) * (l + 1) - j) (1 : F) := by
  simp only [ArithmeticThetaCorrectedGammaR0061.rightFactor,
    map_sub, map_one, map_mul, map_pow]
  change 1 - σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) ^ _ *
      σ
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = _
  rw [ht, hy]
  have heq : ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) + 1 =
      r * (l + 1) - j := by
    simp [ArithmeticThetaCorrectedGammaR0061.rightExponent]
    have hrl : r ≤ r * (l + 1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  rw [show ArithmeticThetaLaurentNormR0064.t F ^
        ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) *
      (HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) =
      HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F ^
        (ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) + 1) by
      rw [pow_succ]; ring, heq, t_pow_single]
  congr 1
  have hbound : j ≤ r * (l + 1) := by
    have hrl : r ≤ r * (l + 1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  simp only [Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private lemma genericSection_fullPartial (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (r j N : ℕ) (hj : j < r) :
    σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N)) =
      ArithmeticThetaLaurentNormR0064.Partial F r j α N := by
  simp only [ArithmeticThetaCorrectedGammaR0061.fullPartial,
    ArithmeticThetaCorrectedGammaR0061.leftPartial,
    ArithmeticThetaCorrectedGammaR0061.rightPartial,
    ArithmeticThetaLaurentNormR0064.Partial, map_mul, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro l hl
    exact genericSection_leftFactor k F α σ ht hx hy r j l
  · apply Finset.prod_congr rfl
    intro l hl
    exact genericSection_rightFactor k F α σ ht hx hy r j l hj

private lemma genericSection_gamma_isGamma (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F)
    (hcont : ∀ (N : ℕ) (b : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k),
      b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N →
      ∀ e : ℤ, e < (N : ℤ) →
        (σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k b)).coeff e = 0)
    (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ArithmeticThetaLaurentNormR0064.IsGamma F r j α
      (σ (ArithmeticThetaLocalNormR0054.gammaLocal k r j hr hj)) := by
  rw [local_gamma_provider_bridge k r j hr hj]
  intro n
  have hlim := (Classical.choose_spec (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))).2.2.1
  obtain ⟨N₀, hN₀⟩ := hlim (n + 1).toNat
  refine ⟨N₀, ?_⟩
  intro N hN e he
  have hmem := hN₀ N hN
  have he' : e < ((n + 1).toNat : ℤ) := by omega
  have hz := hcont (n + 1).toNat
    (correctedGamma k r j hr hj - ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N)
    hmem e he'
  have hcoeff :
      (σ
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (correctedGamma k r j hr hj)) -
       σ
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N))).coeff e = 0 := by
    rw [← map_sub, ← map_sub]
    exact hz
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hcoeff
  rw [genericSection_fullPartial k F α σ ht hx hy r j N hj] at hcoeff
  exact hcoeff.symm

private lemma genericSection_tpower (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (e : ℤ) :
    σ (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e) =
      HahnSeries.single e (1 : F) := by
  have hparam :
      ((ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k :
        (GenericChart k)ˣ) : GenericChart k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) :=
    (IsLocalization.Away.algebraMap_isUnit
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)).unit_spec
  calc
    σ (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e) =
        ((Units.map (σ).toMonoidHom
          (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) :
          LaurentSeries F) := rfl
    _ = ((Units.map (σ).toMonoidHom
          (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k)) :
          LaurentSeries F) ^ e := by rw [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = (ArithmeticThetaLaurentNormR0064.t F) ^ e := by
      rw [Units.coe_map, hparam]
      exact congrArg (fun z : LaurentSeries F => z ^ e) ht
    _ = HahnSeries.single e (1 : F) := (RatFunc.single_zpow e).symm

private lemma genericSection_literalPartial (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (r c j N : ℕ) :
    σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k r c j N) =
      ArithmeticThetaLaurentNormR0064.Partial F r (c*j) (α^c) N := by
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial,
    ArithmeticThetaLaurentNormR0064.Partial, map_prod, map_mul, map_sub,
    map_one, map_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  rw [genericSection_tpower k F α σ ht hx hy, genericSection_tpower k F α σ ht hx hy,
    hx, hy]
  have hC : (HahnSeries.C α : LaurentSeries F) ^ c = HahnSeries.C (α ^ c) := by
    exact (map_pow (HahnSeries.C : F →+* LaurentSeries F) α c).symm
  have hCi : (HahnSeries.C α⁻¹ : LaurentSeries F) ^ c =
      HahnSeries.C (α ^ c)⁻¹ := by
    rw [← map_pow (HahnSeries.C : F →+* LaurentSeries F), inv_pow]
  have hl :
      HahnSeries.single
        (ArithmeticThetaAnnularTorsionPrereqR0053.leftExponent r c j l : ℤ)
        (1 : F) * (HahnSeries.C α : LaurentSeries F) ^ c =
      HahnSeries.C (α^c) *
        HahnSeries.single ((r : ℤ) * l + c*j) (1 : F) := by
    rw [hC, mul_comm]
    congr 1
  have he : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent r c j l + c =
      (r : ℤ) * (l + 1) - (c*j : ℕ) := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent]
    ring
  have hr :
      HahnSeries.single
        (ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent r c j l)
        (1 : F) * (HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) ^ c =
      HahnSeries.C (α^c)⁻¹ *
        HahnSeries.single ((r : ℤ) * (l+1) - (c*j : ℕ)) (1 : F) := by
    calc
      _ = HahnSeries.C (α^c)⁻¹ *
          (HahnSeries.single
            (ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent r c j l)
            (1 : F) * ArithmeticThetaLaurentNormR0064.t F ^ c) := by
        rw [mul_pow, hCi]
        ring
      _ = _ := by
        rw [t_pow_single, HahnSeries.single_mul_single]
        simp only [one_mul, he]
  rw [hl, hr, ← hC]
  simp only [Nat.cast_mul]

private lemma genericSection_powered_isGamma (k F : Type) [Field k] [CharZero k] [Field F]
    (α : F) (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries F)
    (ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = ArithmeticThetaLaurentNormR0064.t F)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α)
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t F) (r c j : ℕ) (ζ : k) (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r)

    (hcont : ∀ (N : ℕ) (b : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k),
      b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N →
      ∀ e : ℤ, e < (N : ℤ) →
        (σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k b)).coeff e = 0)
    (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
    (hj : j < r) :
    ArithmeticThetaLaurentNormR0064.IsGamma F r (c*j) (α^c)
      (σ (ArithmeticThetaLocalNormR0054.poweredLocal k r c j ζ hr hc hdiv hcop hζ hj)) := by
  let C := ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k r c j
    (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0)
  let H : LaurentSeries F := σ C
  intro n
  let d : ℕ := (n - H.order).toNat + 1
  refine ⟨ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j d, ?_⟩
  intro N hN e he
  have happrox := (Classical.choose_spec
    (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_local_divisor
      k r c j ζ hr hc hdiv hcop hζ hj)).1.1
  obtain ⟨f, hf, hdiff⟩ := happrox d N hN
  have hclear := ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_clearing
    k r c j hr hc hdiv hcop hj
  have hNzero : ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0 ≤ N := by
    dsimp [ArithmeticThetaAnnularTorsionPrereqR0053.cutoff] at hN ⊢
    omega
  have hstable : ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial
      k r c j N = C :=
    hclear.2.2 N _ hNzero (le_refl _)
  have hz : (H * σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f)).coeff e = 0 := by
    apply filtered_mul_coeff_zero F H _ d e
    · intro i hi
      exact hcont d f hf i hi
    · dsimp [d]
      omega
  have hseries :
      (σ (ArithmeticThetaLocalNormR0054.poweredLocal k r c j ζ hr hc hdiv hcop hζ hj) -
       ArithmeticThetaLaurentNormR0064.Partial F r (c*j) (α^c) N).coeff e = 0 := by
    rw [← genericSection_literalPartial k F α σ ht hx hy r c j N, ← map_sub]
    change (σ
      (ArithmeticThetaLocalNormR0054.poweredLocal k r c j ζ
        hr hc hdiv hcop hζ hj -
        ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k r c j N)).coeff e = 0
    change ArithmeticThetaLocalNormR0054.poweredLocal k r c j ζ
      hr hc hdiv hcop hζ hj -
        ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k r c j N =
      ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k r c j N *
        ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f at hdiff
    rw [hdiff, map_mul, hstable]
    change (H * σ
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f)).coeff e = 0
    exact hz
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hseries
  exact hseries.symm


end FullGammaEvaluation


/-- The full unpowered and powered gamma limits under faithful annular evaluation. -/
theorem full_gamma_evaluation :
    ∀ (k : Type) [Field k] [CharZero k] (r c : ℕ) (hr : 0 < r) (hc : 1 < c)
      (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
      (a : kˣ) (n : ℕ) (hn : 0 < n) (ev : ChartField k →+* Series k)
      (hev : IsEvaluation k a n ev) (j : Fin r),
      ArithmeticThetaLaurentNormR0064.IsGamma (Coeff k) r j.val (coordinate k a n)
        (ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt))) ∧
      ArithmeticThetaLaurentNormR0064.IsGamma (Coeff k) r (c*j.val) (coordinate k a n ^ c)
        (ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ
            hr hc hdiv hcop hζ j.isLt))) ∧
      ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
        (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt)) ≠ 0 ∧
      ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
        (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ
          hr hc hdiv hcop hζ j.isLt)) ≠ 0 := by
  intro k _ _ r c hr hc hdiv hcop ζ hζ a n hn ev hev j
  let α := coordinate k a n
  let σ := ev.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k)
  have ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) =
      ArithmeticThetaLaurentNormR0064.t (Coeff k) := by
    have h := hev.1 PowerSeries.X
    change ev (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = _ at h
    simpa [σ, ArithmeticThetaKatoAnnularR0152.chartToField,
      baseSeries, ArithmeticThetaLaurentNormR0064.t,
      LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using h
  have hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α := hev.2.1
  have hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) =
      HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t (Coeff k) := by
    simpa only [σ, α, ArithmeticThetaKatoAnnularR0152.chartToField,
      RingHom.comp_apply, map_inv₀] using hev.2.2.1
  have hcont : ∀ (N : ℕ) (b : Chart k),
      b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N →
      ∀ e : ℤ, e < (N : ℤ) →
        (σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k b)).coeff e = 0 :=
    hev.2.2.2
  have hg := FullGammaEvaluation.genericSection_gamma_isGamma
    k (Coeff k) α σ ht hx hy hcont r j.val hr j.isLt
  have hp := FullGammaEvaluation.genericSection_powered_isGamma
    k (Coeff k) α σ ht hx hy r c j.val ζ hr hc hdiv hcont hcop hζ j.isLt
  have htrans : Transcendental k α :=
    FaithfulAnnularEvaluation.coordinate_transcendental k a n hn
  have htransc : Transcendental k (α ^ c) := htrans.pow (by omega)
  have ha0 : α ≠ 0 := fun h => htrans (h.symm ▸ isAlgebraic_zero)
  have ha1 : α ≠ 1 := fun h => htrans (h.symm ▸ isAlgebraic_one)
  have hac0 : α ^ c ≠ 0 := pow_ne_zero _ ha0
  have hac1 : α ^ c ≠ 1 := fun h => htransc (h.symm ▸ isAlgebraic_one)
  obtain ⟨G, hG, uniqueG⟩ :=
    ArithmeticThetaLaurentNormR0064.gamma_exists_unique (Coeff k) r j.val α hr ha0
  obtain ⟨P, hP, uniqueP⟩ :=
    ArithmeticThetaLaurentNormR0064.gamma_exists_unique (Coeff k) r (c*j.val) (α^c) hr hac0
  have eqG : ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt)) = G := uniqueG _ hg
  have eqP : ev (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ
        hr hc hdiv hcop hζ j.isLt)) = P := uniqueP _ hp
  rw [eqG, eqP]
  exact ⟨hG, hP,
    ArithmeticThetaLaurentNormR0064.gamma_nonzero (Coeff k) r j.val α hr ha0 ha1 G hG,
    ArithmeticThetaLaurentNormR0064.gamma_nonzero (Coeff k) r (c*j.val) (α^c)
      hr hac0 hac1 P hP⟩

end ArithmeticThetaAnnularNormBridgeR0156

#print axioms ArithmeticThetaAnnularNormBridgeR0156.full_gamma_evaluation
