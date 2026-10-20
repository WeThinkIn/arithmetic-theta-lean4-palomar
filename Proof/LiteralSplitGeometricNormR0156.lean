module

public import FullGammaEvaluationR0156
public import EvaluationScalingR0156
public import MultiplicationEvaluationR0156
public import CompletedNormProductR0153

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace LiteralSplitGeometricNorm
open ArithmeticThetaLaurentNormR0064

private def stretch (F : Type) [Field F] (q : ℕ) (hq : 0 < q) :
    LaurentSeries F →+* LaurentSeries F :=
  HahnSeries.embDomainRingHom
    { toFun := fun i : ℤ => (q : ℤ) * i
      map_zero' := mul_zero _
      map_add' := mul_add _ }
    (fun a b h => by dsimp at h; nlinarith)
    (fun a b => by dsimp; constructor <;> intro h <;> nlinarith)

private lemma stretch_single (F : Type) [Field F] (q : ℕ) (hq : 0 < q)
    (i : ℤ) (a : F) :
    stretch F q hq (HahnSeries.single i a) = HahnSeries.single ((q : ℤ)*i) a :=
  HahnSeries.embDomain_single

private lemma stretch_C (F : Type) [Field F] (q : ℕ) (hq : 0 < q) (a : F) :
    stretch F q hq (HahnSeries.C a) = HahnSeries.C a :=
  HahnSeries.embDomainRingHom_C

private lemma stretch_coeff (F : Type) [Field F] (q : ℕ) (hq : 0 < q)
    (g : LaurentSeries F) (i : ℤ) :
    (stretch F q hq g).coeff ((q : ℤ)*i) = g.coeff i :=
  HahnSeries.embDomain_coeff (a := i)

private lemma stretch_partial (F : Type) [Field F] (q : ℕ) (hq : 0 < q)
    (d m : ℕ) (a : F) (N : ℕ) :
    stretch F q hq (Partial F d m a N) = Partial F (q*d) (q*m) a N := by
  simp only [Partial, map_mul, map_prod, map_sub, map_one, stretch_C, stretch_single]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro l hl <;>
    congr 3 <;> push_cast <;> ring

private lemma stretch_gamma (F : Type) [Field F] (q : ℕ) (hq : 0 < q)
    (d m : ℕ) (a : F) (g : LaurentSeries F) (hg : IsGamma F d m a g) :
    IsGamma F (q*d) (q*m) a (stretch F q hq g) := by
  intro n
  obtain ⟨N₀, hN₀⟩ := hg (n / q)
  refine ⟨N₀, ?_⟩
  intro N hN e he
  rw [← stretch_partial F q hq]
  by_cases hex : ∃ i : ℤ, (q : ℤ)*i = e
  · obtain ⟨i, rfl⟩ := hex
    rw [stretch_coeff, stretch_coeff]
    apply hN₀ N hN i
    exact (Int.le_ediv_iff_mul_le (by omega)).mpr (by nlinarith)
  · have hnmem : e ∉ Set.range (fun i : ℤ => (q : ℤ)*i) := hex
    change (HahnSeries.embDomain _ _).coeff _ = (HahnSeries.embDomain _ _).coeff _
    rw [HahnSeries.embDomain_of_notMem_range hnmem,
      HahnSeries.embDomain_of_notMem_range hnmem]

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

private lemma stretch_t (F : Type) [Field F] (q : ℕ) (hq : 0 < q) :
    stretch F q hq (t F) = t F ^ q := by
  rw [t, stretch_single, HahnSeries.single_pow]
  simp

private lemma stretch_fValue (k : Type) [Field k] (q : ℕ) (hq : 0 < q)
    (c d : ℕ) (v g h : Series k) :
    stretch (Coeff k) q hq (fValue k c d v g h) =
    fValue k c (q*d) (stretch (Coeff k) q hq v)
      (stretch (Coeff k) q hq g) (stretch (Coeff k) q hq h) := by
  simp only [fValue, Q, map_mul, map_div₀, map_zpow₀, map_pow, map_neg,
    stretch_t, ← pow_mul]

private lemma norm_product_at_period (k : Type) [Field k] [CharZero k]
    (c d r : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hd : 0 < d) (hcd : Nat.Coprime c d) (hζ : IsPrimitiveRoot ζ d)
    (hr : 0 < r) (hdr : d ∣ r) :
    ∃ (G H : Fin d → Fin d → Series k) (b e : Series k),
      (∀ i j : Fin d, IsGamma (Coeff k) r ((r/d)*i.val) (a k ζ j.val 1) (G i j)) ∧
      (∀ i j : Fin d, IsGamma (Coeff k) r (c*((r/d)*i.val)) (a k ζ j.val c) (H i j)) ∧
      IsGamma (Coeff k) r 0 (w k ^ d) b ∧
      IsGamma (Coeff k) r 0 (w k ^ (c*d)) e ∧
      (∏ i : Fin d, ∏ j : Fin d,
        fValue k c r (HahnSeries.C (a k ζ j.val 1) * t (Coeff k)^((r/d)*i.val))
          (G i j) (H i j)) = fValue k c r (z k d) b e := by
  obtain ⟨G, H, b, e, hG, hH, hb, he, _, _, _, hnorm⟩ :=
    formal_f_norm k c d ζ hc hcop hd hcd hζ
  have hq : 0 < r/d := Nat.div_pos (Nat.le_of_dvd hr hdr) hd
  have hqd : r/d*d = r := Nat.div_mul_cancel hdr
  let R := stretch (Coeff k) (r/d) hq
  refine ⟨fun i j => R (G i j), fun i j => R (H i j), R b, R e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [hqd] using stretch_gamma (Coeff k) (r/d) hq d i.val _ _ (hG i j)
  · intro i j
    simpa only [hqd, Nat.mul_left_comm (r/d) c] using
      stretch_gamma (Coeff k) (r/d) hq d (c*i.val) _ _ (hH i j)
  · simpa only [hqd, Nat.mul_zero] using stretch_gamma (Coeff k) (r/d) hq d 0 _ _ hb
  · simpa only [hqd, Nat.mul_zero] using stretch_gamma (Coeff k) (r/d) hq d 0 _ _ he
  · have hn := congrArg R hnorm
    simp only [map_prod] at hn
    simpa only [R, stretch_fValue, hqd, point, z, map_mul, map_pow,
      stretch_C, stretch_t, ← pow_mul] using hn

private lemma coordinate_root (k : Type) [Field k] [CharZero k] (ζ : kˣ) (j : ℕ) :
    coordinate k (ζ^j) 1 = a k (ζ : k) j 1 := by
  simp [coordinate, a, scalar, coefficientMap]

private lemma coordinate_root_power (k : Type) [Field k] [CharZero k]
    (ζ : kˣ) (j c : ℕ) :
    coordinate k (ζ^j) 1 ^ c = a k (ζ : k) j c := by
  rw [coordinate_root]
  simp [a, mul_pow, ← pow_mul, Nat.mul_comm j c]

private lemma evaluated_literal_product (k : Type) [Field k] [CharZero k]
    (r c : ℕ) (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r)
    (hcop : Nat.Coprime c 6) (ζc : k) (hζc : IsPrimitiveRoot ζc c)
    (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d) (hdr : d ∣ r)
    (ζd : kˣ) (hζd : IsPrimitiveRoot (ζd : k) d)
    (v : Fin d → (ChartField k →+* Series k))
    (hv : ∀ j, IsEvaluation k (ζd^j.val) 1 (v j))
    (w : ChartField k →+* Series k) (hw : IsEvaluation k 1 d w) :
    (∏ i : Fin d, ∏ j : Fin d,
      v j (literalTheta k r c hr hc hdiv hcop ζc hζc
        (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d i))) =
      w (literalTheta k r c hr hc hdiv hcop ζc hζc
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr)) := by
  obtain ⟨G,H,b,e,hG,hH,hb,he,hnorm⟩ :=
    norm_product_at_period k c d r (ζd : k) hc hcop hd hcd hζd hr hdr
  have hi (i : Fin d) :
      (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d i).val = (r/d)*i.val := by
    apply Nat.mod_eq_of_lt
    calc
      r/d*i.val < r/d*d := Nat.mul_lt_mul_of_pos_left i.isLt
        (Nat.div_pos (Nat.le_of_dvd hr hdr) hd)
      _ = r := Nat.div_mul_cancel hdr
  have hrow (i j : Fin d) :
      v j (literalTheta k r c hr hc hdiv hcop ζc hζc
        (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d i)) =
      fValue k c r (HahnSeries.C (a k (ζd : k) j.val 1) * t (Coeff k)^((r/d)*i.val))
        (G i j) (H i j) := by
    have hh := full_gamma_evaluation k r c hr hc hdiv hcop ζc hζc
      (ζd^j.val) 1 (by omega) (v j) (hv j)
      (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d i)
    have hα : coordinate k (ζd^j.val) 1 ≠ 0 := by
      intro h
      exact (FaithfulAnnularEvaluation.coordinate_transcendental k (ζd^j.val) 1 (by omega))
        (h.symm ▸ isAlgebraic_zero)
    have hg := (gamma_exists_unique (Coeff k) r ((r/d)*i.val)
      (a k (ζd : k) j.val 1) hr (by rwa [← coordinate_root])).unique
      (by simpa only [hi, coordinate_root] using hh.1) (hG i j)
    have hp := (gamma_exists_unique (Coeff k) r (c*((r/d)*i.val))
      (a k (ζd : k) j.val c) hr (by rw [← coordinate_root_power]; exact pow_ne_zero _ hα)).unique
      (by simpa only [hi, coordinate_root_power] using hh.2.1) (hH i j)
    rw [eval_literal k r c hr hc hdiv hcop ζc hζc _ _ _ (hv j)]
    simpa only [hi, coordinate_root] using congrArg₂
      (fun g h => fValue k c r
        (HahnSeries.C (a k (ζd : k) j.val 1) * t (Coeff k)^((r/d)*i.val)) g h) hg hp
  have htarget :
      w (literalTheta k r c hr hc hdiv hcop ζc hζc
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr)) = fValue k c r (z k d) b e := by
    have hh := full_gamma_evaluation k r c hr hc hdiv hcop ζc hζc
      1 d hd w hw (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr)
    have hwc : coordinate k 1 d = ArithmeticThetaLaurentNormR0064.w k ^ d := by
      simp [coordinate]
    have hα : ArithmeticThetaLaurentNormR0064.w k ^ d ≠ 0 := by
      rw [← hwc]
      intro h
      exact (FaithfulAnnularEvaluation.coordinate_transcendental k 1 d hd)
        (h.symm ▸ isAlgebraic_zero)
    have hg := (gamma_exists_unique (Coeff k) r 0 _ hr hα).unique
      (by simpa only [ArithmeticThetaIdentitySectionsR0138.zeroIndex, hwc] using hh.1) hb
    have hp := (gamma_exists_unique (Coeff k) r 0 _ hr (pow_ne_zero c hα)).unique
      (by simpa only [ArithmeticThetaIdentitySectionsR0138.zeroIndex, hwc, Nat.mul_zero] using hh.2.1)
      (by simpa only [← pow_mul, Nat.mul_comm d c] using he)
    rw [eval_literal k r c hr hc hdiv hcop ζc hζc _ _ _ hw]
    simpa only [ArithmeticThetaIdentitySectionsR0138.zeroIndex, hwc, pow_zero, mul_one, z] using
      congrArg₂ (fun g h => fValue k c r (z k d) g h) hg hp
  simp_rw [hrow]
  exact hnorm.trans htarget.symm

end LiteralSplitGeometricNorm


/-- The actual geometric norm fixes any rational function with the specified literal expansions. -/
theorem literal_split_geometric_norm :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hcr : c ∣ r) (ζc : k) (hζc : IsPrimitiveRoot ζc c) (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d) (hdr : d ∣ r) (ζd : kˣ) (hζd : IsPrimitiveRoot (ζd : k) d) (μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (hμ : ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ), ∀ f : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), (∀ j : Fin r, φ j f = ArithmeticThetaAnnularNormBridgeR0156.literalTheta k r c hr hc hcr hcop ζc hζc j) → ArithmeticThetaGeometricNormR0150.fieldNorm μ f = f := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ rot scal inv ha χ hχ φ hφ
    c hc hcop hcr ζc hζc d hd hcd hdr ζd hζd μ hμ f hf
  classical
  obtain ⟨ν, e, E, hν, hE, hprod⟩ :=
    ArithmeticThetaSplitNormR0153.completed_norm_product k r hr h3 T he M hM s hs
      G hG rot scal inv ha χ hχ φ hφ d hd hdr ζd hζd
  have hνμ : ν = μ := ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm.fieldMap_unique _ _ _ hμ hν
  subst ν
  obtain ⟨v, hv, _⟩ := faithful_annular_evaluation k 1 1 (by omega)
  obtain ⟨w, hw, _⟩ := faithful_annular_evaluation k 1 d hd
  have hV : ∀ j : Fin d, ∃ vj : ChartField k →+* Series k,
      IsEvaluation k (ζd^j.val) 1 vj := by
    intro j
    obtain ⟨vj, hvj, _⟩ := faithful_annular_evaluation k (ζd^j.val) 1 (by omega)
    exact ⟨vj, hvj.1⟩
  choose V hV using hV
  let j0 := ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr
  apply (φ j0).injective
  apply hw.2
  rw [← multiplication_evaluation k r hr h3 T he M hM s hs G hG (χ j0) (hχ j0)
    (φ j0) (hφ j0) d hd μ hμ v w hv.1 hw.1, hprod, map_prod]
  have hterm (ab : Fin d × Fin d) :
      v (E (ζd^ab.2.val)
        (φ (ArithmeticThetaSplitNormR0153.shift (hr := hr) j0
          (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1)) f)) =
      V ab.2 (literalTheta k r c hr hc hcr hcop ζc hζc
        (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1)) := by
    rw [evaluation_scaling k (ζd^ab.2.val) 1 1 (by omega)
      (e (ζd^ab.2.val)) (E (ζd^ab.2.val)) (hE _).1 (hE _).2 v (V ab.2) hv.1
      (by simpa only [mul_one] using hV ab.2), hf]
    congr 2
    apply Fin.ext
    simp [ArithmeticThetaSplitNormR0153.shift, j0,
      ArithmeticThetaIdentitySectionsR0138.zeroIndex]
    exact Nat.mod_eq_of_lt (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1).isLt
  simp_rw [hterm]
  rw [Fintype.prod_prod_type, hf]
  exact LiteralSplitGeometricNorm.evaluated_literal_product k r c hr hc hcr hcop ζc hζc
    d hd hcd hdr ζd hζd V hV w hw.1

end ArithmeticThetaAnnularNormBridgeR0156
#print axioms ArithmeticThetaAnnularNormBridgeR0156.literal_split_geometric_norm
