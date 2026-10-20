module

public import LocalGammaProviderBridgeR0065

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaGenericOverlapR0065

private def sectionToLaurent (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) : Chart k →+* LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k).comp
    (ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα)

private lemma sectionToLaurent_parameter (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) :
    IsUnit (sectionToLaurent k α hα (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) := by
  have hs := Classical.choose_spec
    ((ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k true α hα).1)
  have ht : ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X := by
    change ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) = _
    exact DFunLike.congr_fun hs.1.1 PowerSeries.X
  rw [sectionToLaurent, RingHom.comp_apply, ht]
  simpa only [LaurentSeries.coe_algebraMap] using
    (IsLocalization.Away.algebraMap_isUnit (S := LaurentSeries k)
      (PowerSeries.X : PowerSeries k))

private def genericSection (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) : GenericChart k →+* LaurentSeries k :=
  IsLocalization.Away.lift (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)
    (sectionToLaurent_parameter k α hα)

private lemma genericSection_comp (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) :
    (genericSection k α hα).comp
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) =
        sectionToLaurent k α hα := by
  exact IsLocalization.Away.lift_comp _ (sectionToLaurent_parameter k α hα)

private lemma genericSection_parameter (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) =
      ArithmeticThetaLaurentNormR0064.t k := by
  rw [← RingHom.comp_apply, genericSection_comp]
  change sectionToLaurent k α hα
    (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = _
  have hs := Classical.choose_spec
    ((ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k true α hα).1)
  have ht : ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X := by
    change ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) = _
    exact DFunLike.congr_fun hs.1.1 PowerSeries.X
  simp [sectionToLaurent, ht, ArithmeticThetaLaurentNormR0064.t,
    HahnSeries.ofPowerSeries_X]

private lemma genericSection_x (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C α := by
  rw [← RingHom.comp_apply, genericSection_comp]
  have hs := Classical.choose_spec
    ((ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k true α hα).1)
  simpa [sectionToLaurent, ArithmeticThetaIndexedOverlapsR0058.selectedSection,
    ArithmeticThetaAnnularTorsionPrereqR0053.coord] using
    congrArg (HahnSeries.ofPowerSeries ℤ k) hs.1.2.1

private lemma genericSection_y (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) =
      HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t k := by
  rw [← RingHom.comp_apply, genericSection_comp]
  have hs := Classical.choose_spec
    ((ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k true α hα).1)
  simpa [sectionToLaurent, ArithmeticThetaIndexedOverlapsR0058.selectedSection,
    ArithmeticThetaAnnularTorsionPrereqR0053.coord,
    ArithmeticThetaLaurentNormR0064.t, map_mul, HahnSeries.ofPowerSeries_X] using
    congrArg (HahnSeries.ofPowerSeries ℤ k) hs.1.2.2.1

private lemma section_coeff_zero (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (f : Chart k) (n m : ℕ)
    (hf : f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n)
    (hm : m < n) :
    PowerSeries.coeff m
      (ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα f) = 0 := by
  have hs := Classical.choose_spec
    ((ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k true α hα).1)
  have hmem := hs.1.2.2.2 n f hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff] at hmem
  exact hmem m hm

private lemma sectionToLaurent_coeff_zero (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (f : Chart k) (n : ℕ) (e : ℤ)
    (hf : f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n)
    (he : e < n) : (sectionToLaurent k α hα f).coeff e = 0 := by
  by_cases hneg : e < 0
  · simp [sectionToLaurent, PowerSeries.coeff_coe, hneg]
  · have hnonneg : 0 ≤ e := by omega
    have hm : e.natAbs < n := by omega
    simpa [sectionToLaurent, PowerSeries.coeff_coe, hneg] using
      section_coeff_zero k α hα f n e.natAbs hf hm

private lemma t_pow_single (k : Type) [Field k] (n : ℕ) :
    ArithmeticThetaLaurentNormR0064.t k ^ n =
      HahnSeries.single (n : ℤ) (1 : k) := by
  simp [ArithmeticThetaLaurentNormR0064.t, HahnSeries.single_pow]

private lemma genericSection_leftFactor (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (r j l : ℕ) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.leftFactor k r j l)) =
      1 - HahnSeries.C α *
        HahnSeries.single ((r : ℤ) * l + j) (1 : k) := by
  simp only [ArithmeticThetaCorrectedGammaR0061.leftFactor,
    map_sub, map_one, map_mul, map_pow]
  change 1 - genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) ^ _ *
      genericSection k α hα
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = _
  rw [genericSection_parameter, genericSection_x]
  rw [t_pow_single]
  rw [mul_comm (HahnSeries.single
    (ArithmeticThetaCorrectedGammaR0061.leftExponent r j l : ℤ) (1 : k))
    (HahnSeries.C α)]
  simp [ArithmeticThetaCorrectedGammaR0061.leftExponent]

private lemma genericSection_rightFactor (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (r j l : ℕ) (hj : j < r) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.rightFactor k r j (l + 1))) =
      1 - HahnSeries.C α⁻¹ *
        HahnSeries.single ((r : ℤ) * (l + 1) - j) (1 : k) := by
  simp only [ArithmeticThetaCorrectedGammaR0061.rightFactor,
    map_sub, map_one, map_mul, map_pow]
  change 1 - genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) ^ _ *
      genericSection k α hα
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = _
  rw [genericSection_parameter, genericSection_y]
  have heq : ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) + 1 =
      r * (l + 1) - j := by
    simp [ArithmeticThetaCorrectedGammaR0061.rightExponent]
    have hrl : r ≤ r * (l + 1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  rw [show ArithmeticThetaLaurentNormR0064.t k ^
        ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) *
      (HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t k) =
      HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t k ^
        (ArithmeticThetaCorrectedGammaR0061.rightExponent r j (l + 1) + 1) by
      rw [pow_succ]; ring, heq, t_pow_single]
  congr 1
  have hbound : j ≤ r * (l + 1) := by
    have hrl : r ≤ r * (l + 1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  simp only [Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private lemma genericSection_fullPartial (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (r j N : ℕ) (hj : j < r) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N)) =
      ArithmeticThetaLaurentNormR0064.Partial k r j α N := by
  simp only [ArithmeticThetaCorrectedGammaR0061.fullPartial,
    ArithmeticThetaCorrectedGammaR0061.leftPartial,
    ArithmeticThetaCorrectedGammaR0061.rightPartial,
    ArithmeticThetaLaurentNormR0064.Partial, map_mul, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro l hl
    exact genericSection_leftFactor k α hα r j l
  · apply Finset.prod_congr rfl
    intro l hl
    exact genericSection_rightFactor k α hα r j l hj

private lemma genericSection_gamma_isGamma (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ArithmeticThetaLaurentNormR0064.IsGamma k r j α
      (genericSection k α hα (ArithmeticThetaLocalNormR0054.gammaLocal k r j hr hj)) := by
  rw [local_gamma_provider_bridge k r j hr hj]
  intro n
  have hlim := (Classical.choose_spec (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))).2.2.1
  obtain ⟨N₀, hN₀⟩ := hlim (n + 1).toNat
  refine ⟨N₀, ?_⟩
  intro N hN e he
  have hmem := hN₀ N hN
  have he' : e < ((n + 1).toNat : ℤ) := by omega
  have hz := sectionToLaurent_coeff_zero k α hα
    (correctedGamma k r j hr hj - ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N)
    (n + 1).toNat e hmem he'
  have hcoeff :
      (genericSection k α hα
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (correctedGamma k r j hr hj)) -
       genericSection k α hα
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N))).coeff e = 0 := by
    rw [← map_sub, ← map_sub, ← RingHom.comp_apply, genericSection_comp]
    exact hz
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hcoeff
  rw [genericSection_fullPartial k α hα r j N hj] at hcoeff
  exact hcoeff.symm

private lemma genericSection_tpower (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (e : ℤ) :
    genericSection k α hα (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e) =
      HahnSeries.single e (1 : k) := by
  have hparam :
      ((ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k :
        (GenericChart k)ˣ) : GenericChart k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) :=
    (IsLocalization.Away.algebraMap_isUnit
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)).unit_spec
  calc
    genericSection k α hα (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e) =
        ((Units.map (genericSection k α hα).toMonoidHom
          (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) :
          LaurentSeries k) := rfl
    _ = ((Units.map (genericSection k α hα).toMonoidHom
          (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k)) :
          LaurentSeries k) ^ e := by rw [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = (ArithmeticThetaLaurentNormR0064.t k) ^ e := by
      rw [Units.coe_map, hparam]
      congr 1
      exact genericSection_parameter k α hα
    _ = HahnSeries.single e (1 : k) := (RatFunc.single_zpow e).symm

private lemma genericSection_literalPartial (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (c j N : ℕ) :
    genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k (2*c) c j N) =
      ArithmeticThetaLaurentNormR0064.Partial k (2*c) (c*j) (α^c) N := by
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial,
    ArithmeticThetaLaurentNormR0064.Partial, map_prod, map_mul, map_sub,
    map_one, map_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  rw [genericSection_tpower, genericSection_tpower,
    genericSection_x, genericSection_y]
  have hC : (HahnSeries.C α : LaurentSeries k) ^ c = HahnSeries.C (α ^ c) := by
    exact (map_pow (HahnSeries.C : k →+* LaurentSeries k) α c).symm
  have hCi : (HahnSeries.C α⁻¹ : LaurentSeries k) ^ c =
      HahnSeries.C (α ^ c)⁻¹ := by
    rw [← map_pow (HahnSeries.C : k →+* LaurentSeries k), inv_pow]
  have hl :
      HahnSeries.single
        (ArithmeticThetaAnnularTorsionPrereqR0053.leftExponent (2*c) c j l : ℤ)
        (1 : k) * (HahnSeries.C α : LaurentSeries k) ^ c =
      HahnSeries.C (α^c) *
        HahnSeries.single ((2*c : ℤ) * l + c*j) (1 : k) := by
    rw [hC, mul_comm]
    congr 1
  have he : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l + c =
      (2*c : ℤ) * (l + 1) - (c*j : ℕ) := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent]
    ring
  have hr :
      HahnSeries.single
        (ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l)
        (1 : k) * (HahnSeries.C α⁻¹ * ArithmeticThetaLaurentNormR0064.t k) ^ c =
      HahnSeries.C (α^c)⁻¹ *
        HahnSeries.single ((2*c : ℤ) * (l+1) - (c*j : ℕ)) (1 : k) := by
    calc
      _ = HahnSeries.C (α^c)⁻¹ *
          (HahnSeries.single
            (ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l)
            (1 : k) * ArithmeticThetaLaurentNormR0064.t k ^ c) := by
        rw [mul_pow, hCi]
        ring
      _ = _ := by
        rw [t_pow_single, HahnSeries.single_mul_single]
        simpa only [one_mul, he]
  rw [hl, hr, ← hC]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

private lemma genericSection_powered_isGamma (k : Type) [Field k] [CharZero k]
    (α : k) (hα : α ≠ 0) (c j : ℕ) (ζ : k) (hc : 1 < c)
    (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
    (hj : j < 2*c) :
    ArithmeticThetaLaurentNormR0064.IsGamma k (2*c) (c*j) (α^c)
      (genericSection k α hα (powered k c j ζ hc hcop hζ hj)) := by
  let C := ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j
    (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0)
  let H : LaurentSeries k := genericSection k α hα C
  intro n
  let d : ℕ := (n - H.order).toNat + 1
  refine ⟨ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j d, ?_⟩
  intro N hN e he
  have happrox := (Classical.choose_spec
    (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_local_divisor
      k (2*c) c j ζ (by omega) hc (by simp) hcop hζ hj)).1.1
  obtain ⟨f, hf, hdiff⟩ := happrox d N hN
  have hclear := ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_clearing
    k (2*c) c j (by omega) hc (by simp) hcop hj
  have hNzero : ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0 ≤ N := by
    dsimp [ArithmeticThetaAnnularTorsionPrereqR0053.cutoff] at hN ⊢
    omega
  have hstable : ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial
      k (2*c) c j N = C :=
    hclear.2.2 N _ hNzero (le_refl _)
  have hz : (H * sectionToLaurent k α hα f).coeff e = 0 := by
    have h := ArithmeticThetaLaurentNormR0064.existence_head_coeff k H
      (ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα f)
      0 n e he (by
        intro m hm
        simpa using section_coeff_zero k α hα f d m hf (by dsimp [d]; omega))
    simpa [H, sectionToLaurent] using h
  have hseries :
      (genericSection k α hα (powered k c j ζ hc hcop hζ hj) -
       ArithmeticThetaLaurentNormR0064.Partial k (2*c) (c*j) (α^c) N).coeff e = 0 := by
    rw [← genericSection_literalPartial k α hα c j N, ← map_sub]
    change (genericSection k α hα
      (ArithmeticThetaLocalNormR0054.poweredLocal k (2*c) c j ζ
        (by omega) hc (by simp) hcop hζ hj -
        ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k (2*c) c j N)).coeff e = 0
    change ArithmeticThetaLocalNormR0054.poweredLocal k (2*c) c j ζ
      (by omega) hc (by simp) hcop hζ hj -
        ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k (2*c) c j N =
      ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N *
        ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f at hdiff
    rw [hdiff, map_mul, hstable]
    change (H * genericSection k α hα
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f)).coeff e = 0
    rw [← RingHom.comp_apply, genericSection_comp]
    exact hz
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hseries
  exact hseries.symm

theorem chart_laurent_specialization :
    ∀ (k : Type) [Field k] [CharZero k] (c j : ℕ) (ζ α : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c) (hα : α ≠ 0),
      ∃ σ : GenericChart k →+* LaurentSeries k,
        σ.comp (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) =
          (HahnSeries.ofPowerSeries ℤ k).comp
            (ArithmeticThetaIndexedOverlapsR0058.selectedSection k true α hα) ∧
        ArithmeticThetaLaurentNormR0064.IsGamma k (2*c) j α
          (σ (ArithmeticThetaLocalNormR0054.gammaLocal k (2*c) j (by omega) hj)) ∧
        ArithmeticThetaLaurentNormR0064.IsGamma k (2*c) (c*j) (α^c)
          (σ (powered k c j ζ hc hcop hζ hj)) := by
  intro k _ _ c j ζ α hc hcop hζ hj hα
  exact ⟨genericSection k α hα, genericSection_comp k α hα,
    genericSection_gamma_isGamma k α hα (2*c) j (by omega) hj,
    genericSection_powered_isGamma k α hα c j ζ hc hcop hζ hj⟩

end ArithmeticThetaGenericOverlapR0065
