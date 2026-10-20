module

public import CoefficientEvaluationNaturalityR0158
public import RamifiedEvaluationNaturalityR0158
public import GammaBaseChangeNaturalityR0158
public import SplitPeriodKatoFormulaR0158

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158
namespace UnsplitKatoFullExpansionR0158
open ArithmeticThetaLaurentNormR0064
local instance coeffCharZero (k : Type) [Field k] [CharZero k] : CharZero (Coeff k) :=
  charZero_of_injective_ringHom (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151

open ArithmeticThetaAnnularNormBridgeR0156 (IsEvaluation coordinate baseSeries literalTheta)

private lemma normalization (c r : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) :
    ((r*(c^2-1)/12 : ℕ) : ℤ) = (r : ℤ)*(ArithmeticThetaNormFiniteR0063.K c / 12) ∧
    ArithmeticThetaNormFiniteR0063.p c = -((c*(c-1)/2 : ℕ) : ℤ) := by
  have hcast := (ArithmeticThetaNormFiniteR0063.integer_casts c 1 hcop).2.2.2.1
  have hs : 1 ≤ c^2 := by nlinarith
  have hK : ((c^2-1 : ℕ) : ℤ) = 12*(ArithmeticThetaNormFiniteR0063.K c /12) := by
    apply Int.cast_injective (α := ℚ)
    push_cast [Nat.cast_sub hs]
    rw [hcast]
    ring
  have hpos : 0 ≤ ArithmeticThetaNormFiniteR0063.K c /12 := by omega
  have hKn : c^2-1 = 12*(ArithmeticThetaNormFiniteR0063.K c /12).toNat := by
    rw [← Int.toNat_of_nonneg hpos] at hK
    exact_mod_cast hK
  constructor
  · rw [hKn]
    rw [← Nat.mul_assoc, Nat.mul_right_comm r 12, Nat.mul_div_cancel]
    simp only [Nat.cast_mul, Int.toNat_of_nonneg hpos]
    omega
  · simp only [ArithmeticThetaNormFiniteR0063.p, ArithmeticThetaNormFiniteR0063.triangle]
    rw [Int.natCast_ediv, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ c)]
    norm_num

private lemma eval_tpower (k : Type) [Field k] [CharZero k]
    (a : kˣ) (n : ℕ) (v : ChartField k →+* Series k) (hv : IsEvaluation k a n v)
    (e : ℤ) :
    v (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e)) = t (Coeff k)^e := by
  let σ := v.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k)
  have ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = t (Coeff k) := by
    have h := hv.1 PowerSeries.X
    change v (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = _ at h
    simpa [σ, ArithmeticThetaKatoAnnularR0152.chartToField, baseSeries, t,
      LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using h
  have hparam : ((ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k :
      (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)ˣ) :
      ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) :=
    (IsLocalization.Away.algebraMap_isUnit _).unit_spec
  change σ (↑(ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) = _
  calc
    _ = ((Units.map σ.toMonoidHom
      (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) : Series k) := rfl
    _ = (σ (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k)) ^ e := by
      rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
      rfl
    _ = _ := by rw [hparam, ht]

private lemma eval_localZ (k : Type) [Field k] [CharZero k]
    (a : kˣ) (n : ℕ) (v : ChartField k →+* Series k) (hv : IsEvaluation k a n v)
    (j : ℕ) :
    v (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.localZ k j)) =
      HahnSeries.C (coordinate k a n) * t (Coeff k)^j := by
  have ht := eval_tpower k a n v hv 1
  have ht' : v (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = t (Coeff k) := by
    have h := hv.1 PowerSeries.X
    change v (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = _ at h
    simpa [baseSeries, t,
      LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using h
  simp only [ArithmeticThetaLocalNormR0054.localZ,
    ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate, map_mul, map_pow]
  change v (ArithmeticThetaKatoAnnularR0152.chartToField k
    (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) ^ j *
    v (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = _
  rw [ht', hv.2.1, mul_comm]

private lemma eval_literal (k : Type) [Field k] [CharZero k]
    (r c : ℕ) (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r)
    (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (a : kˣ) (n : ℕ) (v : ChartField k →+* Series k) (hv : IsEvaluation k a n v)
    (j : Fin r) :
    v (literalTheta k r c hr hc hdiv hcop ζ hζ j) =
      fValue k c r (HahnSeries.C (coordinate k a n) * t (Coeff k)^j.val)
        (v (ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt)))
        (v (ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ hr hc hdiv hcop hζ j.isLt))) := by
  rw [literalTheta]
  simp only [map_div₀, map_mul, map_pow, map_neg]
  rw [eval_tpower k a n v hv, eval_localZ k a n v hv,
    (normalization c r hc hcop).1]
  simp only [fValue, Q, (normalization c r hc hcop).2, zpow_neg, zpow_natCast]
  rw [← zpow_natCast (t (Coeff k)) r, ← zpow_mul]
  ring

private lemma exists_model (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    ∃ (T : Tower k r hr) (M : Model k T), IsModel k T M := by
  obtain ⟨T, _⟩ := ArithmeticThetaInfinitesimalPolygonR0129.proper_flat_polygon_tower k r hr h3
  obtain ⟨b, hb, hbr, _⟩ :=
    ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis k r hr h3 T (fun _ => 1) 3 (by omega)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩

private lemma w_nonzero (k : Type) [Field k] [CharZero k] : w k ≠ 0 := by
  have ht := ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.coordinate_transcendental k 1 1 (by omega)
  have he : coordinate k 1 1 = w k := by simp [coordinate]
  rw [he] at ht
  exact fun h => ht (h.symm ▸ isAlgebraic_zero)

private lemma literal_expansion (k : Type) [Field k] [CharZero k]
    (r c : ℕ) (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r)
    (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (ev : ChartField k →+* Series k) (hev : IsEvaluation k 1 1 ev) (j : Fin r) :
    HasExpansion k r c j.val (ev (literalTheta k r c hr hc hdiv hcop ζ hζ j)) := by
  intro g h hg hh
  have H := ArithmeticThetaAnnularNormBridgeR0156.full_gamma_evaluation
    k r c hr hc hdiv hcop ζ hζ 1 1 (by omega) ev hev j
  have he : coordinate k 1 1 = w k := by simp [coordinate]
  rw [he] at H
  have eg := (gamma_exists_unique (Coeff k) r j.val (w k) hr (w_nonzero k)).unique H.1 hg
  have eh := (gamma_exists_unique (Coeff k) r (c*j.val) (w k ^ c) hr
    (pow_ne_zero _ (w_nonzero k))).unique H.2.1 hh
  rw [eval_literal k r c hr hc hdiv hcop ζ hζ 1 1 ev hev j, he, eg, eh]

private lemma coefficient_fValue (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (κ : Coeff k →+* Coeff l) (hw : κ (w k) = w l)
    (ell : Series k →+* Series l)
    (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap (Coeff k) (Coeff l) κ ell)
    (r c j : ℕ) (g h : Series k) :
    ell (fValue k c r (HahnSeries.C (w k) * t (Coeff k)^j) g h) =
      fValue l c r (HahnSeries.C (w l) * t (Coeff l)^j) (ell g) (ell h) := by
  have hs (e : ℤ) (a : Coeff k) : ell (HahnSeries.single e a) = HahnSeries.single e (κ a) := by
    rw [GammaBaseChangeNaturalityR0158.coefficientHom_eq _ _ κ ell hell]
    exact GammaBaseChangeNaturalityR0158.coefficientHom_single _ _ κ e a
  simp only [fValue, Q, map_mul, map_div₀, map_zpow₀, map_pow, map_neg,
    HahnSeries.C_apply, t, hs, map_one, hw]

private lemma ramified_fValue (k : Type) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
    (ell : Series k →+* Series k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) d hd ell)
    (r c j : ℕ) (g h : Series k) :
    ell (fValue k c r (HahnSeries.C (w k) * t (Coeff k)^j) g h) =
      fValue k c (r*d) (HahnSeries.C (w k) * t (Coeff k)^(j*d)) (ell g) (ell h) := by
  have hs (e : ℤ) (a : Coeff k) : ell (HahnSeries.single e a) = HahnSeries.single ((d : ℤ)*e) a := by
    rw [GammaBaseChangeNaturalityR0158.ramificationHom_eq _ d hd ell hell]
    exact GammaBaseChangeNaturalityR0158.ramificationHom_single _ d hd e a
  have hC (a : Coeff k) : ell (HahnSeries.C a) = HahnSeries.C a := by
    simpa only [HahnSeries.C_apply, mul_zero] using hs 0 a
  have ht : ell (t (Coeff k)) = t (Coeff k)^d := by
    simpa [t, HahnSeries.single_pow] using hs 1 1
  simp only [fValue, Q, map_mul, map_div₀, map_zpow₀, map_pow, map_neg, hC, ht,
    ← pow_mul, Nat.mul_comm d]

private theorem split_field_expansion :
∀ (k : Type) [Field k] [CharZero k] (r c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∀ (j : Fin r) (ev : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaLaurentNormR0064.Series k), ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 ev → ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c j.val (ev (φ j g))) := by
  intro k _ _ r c hc hcop hr h3 he T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ
  classical
  let d := 2*c
  have hd : 0 < d := by dsimp [d]; omega
  have hrd : 0 < r*d := Nat.mul_pos hr hd
  have h3d : 3 ≤ r*d := h3.trans (Nat.le_mul_of_pos_right r hd)
  have hed : Even (r*d) := he.mul_right d
  have hcr : c ∣ r*d := by dsimp [d]; exact dvd_mul_of_dvd_right (dvd_mul_left c 2) r
  obtain ⟨Tb, Mb, hMb⟩ := exists_model k (r*d) hrd h3d
  letI : AlgebraicGeometry.IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3d Mb hMb
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k Mb hMb
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme k Mb) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Mb)
  obtain ⟨sb, hsb, _⟩ := marked_section_algebraization k (r*d) hrd h3d Tb Mb hMb
    (zeroIndex (r*d) hrd) 1
  obtain ⟨Gb, hGb, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb
  have Hχ : ∀ j : Fin (r*d), ∃ χj, IsChartMap k Mb j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k (r*d) hrd h3d Tb Mb hMb j
    exact ⟨χj, hj⟩
  choose χb hχb using Hχ
  have Hφ : ∀ j : Fin (r*d), ∃ φj, IsChartFieldMap k Mb (χb j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k (r*d) hrd h3d Tb Mb hMb j (χb j) (hχb j)
    exact ⟨φj, hj.1⟩
  choose φb hφb using Hφ
  obtain ⟨gb, hgb, hub⟩ := split_period_kato_formula k (r*d) c hc hcop hrd h3d hed
    Tb Mb hMb sb hsb Gb hGb ζ hζ χb hχb φb hφb hcr
  have Hρ : ∀ q : Fin d, ∃ (ρq : Chart k →+* Chart k) (Eq : ChartField k →+* ChartField k),
      ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρq ∧
      ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρq Eq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := ArithmeticThetaRamifiedPeriodR0154.completed_chart_ramification k d hd q
    obtain ⟨Eq, hEq, _⟩ := hρq.2.2
    exact ⟨ρq, Eq, hρq.1, hEq⟩
  choose ρ E hρ hE using Hρ
  obtain ⟨F, hF, _⟩ := ArithmeticThetaRamifiedPeriodR0154.ramified_model_morphism k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k d hd
  obtain ⟨b, hb, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_generic_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1
  obtain ⟨α, hα, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_function_field_expansion k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    φ hφ φb hφb E hE
  have hbase := ArithmeticThetaRamifiedPeriodR0155.ramified_kato_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    he hed s hs sb hsb G hG Gb hGb
  obtain ⟨g, hg, hu⟩ := actual_kato_function_existence k r hr h3 T he M hM s hs G hG c hc hcop
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb Gb hGb ell b hbase α hα.1 c hc hcop).2 g hg
  obtain ⟨g₀, hg₀, hu₀⟩ := actual_kato_function_existence k (r*d) hrd h3d Tb hed Mb hMb
    sb hsb Gb hGb c hc hcop
  have heq : α g = gb := (hu₀ _ hK).trans (hu₀ _ hgb.1).symm
  refine ⟨g, ⟨hg, ?_⟩, fun f hf => hu f hf.1⟩
  intro j ev hev g₁ g₂ hg₁ hg₂
  let jb := ArithmeticThetaRamifiedPeriodR0154.markedIndex r d hd j
  have hjc : ArithmeticThetaRamifiedPeriodR0154.coarseIndex r d hd jb = j := by
    apply Fin.ext
    simp [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex, ArithmeticThetaRamifiedPeriodR0154.coarseIndex,
      Nat.ne_of_gt hd]
  have hjq : (ArithmeticThetaRamifiedPeriodR0154.residueIndex r d hd jb).val = 0 := by
    simp [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex, ArithmeticThetaRamifiedPeriodR0154.residueIndex]
  obtain ⟨L, hL, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension (Coeff k) d hd
  have hsquare := ramified_evaluation_naturality k d hd
    (ArithmeticThetaRamifiedPeriodR0154.residueIndex r d hd jb) hjq (ρ _) (hρ _) (E _) (hE _) L hL.1 ev hev
  have hx : ev (φb jb gb) = L (ev (φ j g)) := by
    rw [← heq, hα.2.2.2.1, hjc]
    exact RingHom.congr_fun hsquare (φ j g)
  have H := literal_expansion k (r*d) c hrd hc hcr hcop (ζ : k) hζ ev hev jb
  rw [← hgb.2 jb, hx] at H
  apply L.injective
  rw [ramified_fValue k d hd L hL.1]
  apply H
  · exact gamma_base_change_naturality.2 (Coeff k) d hd L hL.1 r j.val (w k) g₁ hr (w_nonzero k) hg₁
  · simpa only [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex, Nat.mul_assoc] using
      gamma_base_change_naturality.2 (Coeff k) d hd L hL.1 r (c*j.val) (w k ^ c) g₂ hr
        (pow_ne_zero _ (w_nonzero k)) hg₂

end UnsplitKatoFullExpansionR0158

open UnsplitKatoFullExpansionR0158
open ArithmeticThetaLaurentNormR0064
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaAnnularNormBridgeR0156 (IsEvaluation)

/-- The exact full Kato expansion over the original coefficient field and every specified even polygon. -/
theorem unsplit_kato_full_expansion :
∀ (k : Type) [Field k] [CharZero k] (r c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∀ (j : Fin r) (ev : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaLaurentNormR0064.Series k), ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 ev → ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c j.val (ev (φ j g))) := by
  intro k _ _ r c hc hcop hr h3 he T M hM s hs G hG _ _ χ hχ φ hφ
  classical
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  letI : CharZero (Coeff k) := coeffCharZero k
  letI : CharZero (Coeff l) := coeffCharZero l
  letI : NeZero c := ⟨by omega⟩
  letI : NeZero (c : k) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot l c
  let ζ : lˣ := Units.mk0 z (hz.ne_zero (by omega))
  have hζ : IsPrimitiveRoot (ζ : l) c := hz
  obtain ⟨Tl, Ml, hMl⟩ := exists_model l r hr h3
  letI : AlgebraicGeometry.IsIntegral (genericScheme l Ml) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral l h3 Ml hMl
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation l Ml hMl
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme l Ml) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure l Ml)
  obtain ⟨sl, hsl, _⟩ := marked_section_algebraization l r hr h3 Tl Ml hMl (zeroIndex r hr) 1
  obtain ⟨Gl, hGl, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    l r hr h3 Tl he Ml hMl sl hsl
  have Hχ : ∀ j : Fin r, ∃ χj, IsChartMap l Ml j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps l r hr h3 Tl Ml hMl j
    exact ⟨χj, hj⟩
  choose χl hχl using Hχ
  have Hφ : ∀ j : Fin r, ∃ φj, IsChartFieldMap l Ml (χl j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps l r hr h3 Tl Ml hMl j (χl j) (hχl j)
    exact ⟨φj, hj.1⟩
  choose φl hφl using Hφ
  obtain ⟨gl, hgl, _⟩ := split_field_expansion l r c hc hcop hr h3 he Tl Ml hMl
    sl hsl Gl hGl ζ hζ χl hχl φl hφl
  obtain ⟨Hell, Hρ, HE⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι
  obtain ⟨ell, hell, _⟩ := Hell
  obtain ⟨ρ, hρ, _⟩ := Hρ
  obtain ⟨E, hE, _⟩ := HE ρ hρ.1
  obtain ⟨F, hF, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_model_base_change
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl
  obtain ⟨b, hb, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_generic_kato_square
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl F hF ell hell
    he s hs sl hsl G hG Gl hGl
  obtain ⟨α, hα, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_function_field_expansion
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 E hE χ hχ χl hχl F hF ell hell b hb.1 φ hφ φl hφl
  obtain ⟨g, hg, hu⟩ := actual_kato_function_existence k r hr h3 T he M hM s hs G hG c hc hcop
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    l r hr h3 Tl he Ml hMl sl hsl Gl hGl ell b hb.2 α hα.1 c hc hcop).2 g hg
  obtain ⟨g₀, hg₀, hu₀⟩ := actual_kato_function_existence l r hr h3 Tl he Ml hMl
    sl hsl Gl hGl c hc hcop
  have heq : α g = gl := (hu₀ _ hK).trans (hu₀ _ hgl.1).symm
  obtain ⟨evl, hevl, _⟩ := ArithmeticThetaAnnularNormBridgeR0156.faithful_annular_evaluation l 1 1 (by omega)
  obtain ⟨κ, hκ, _⟩ := (coefficient_evaluation_naturality k l ι).1
  obtain ⟨L, hL, _⟩ := (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps (Coeff k) (Coeff l) κ).1
  refine ⟨g, ⟨hg, ?_⟩, fun f hf => hu f hf.1⟩
  intro j ev hev g₁ g₂ hg₁ hg₂
  have hsquare := (coefficient_evaluation_naturality k l ι).2 κ hκ L hL ρ hρ.1 E hE ev evl hev hevl.1
  have hx : evl (φl j gl) = L (ev (φ j g)) := by
    rw [← heq, hα.2.2]
    exact RingHom.congr_fun hsquare (φ j g)
  have H := hgl.2 j evl hevl.1
  rw [hx] at H
  apply L.injective
  rw [coefficient_fValue k l κ hκ.2 L hL]
  apply H
  · simpa only [hκ.2] using gamma_base_change_naturality.1 (Coeff k) (Coeff l) κ L hL
      r j.val (w k) g₁ hr (w_nonzero k) hg₁
  · simpa only [map_pow, hκ.2] using gamma_base_change_naturality.1 (Coeff k) (Coeff l) κ L hL
      r (c*j.val) (w k ^ c) g₂ hr (pow_ne_zero _ (w_nonzero k)) hg₂

#print axioms unsplit_kato_full_expansion
end ArithmeticThetaUnsplitExpansionR0158
