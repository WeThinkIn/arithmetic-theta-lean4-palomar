import CompletedMarkedSpecializationR0159
import MarkedKatoRegularityR0159
import GammaZeroLocusR0159
import Lean

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaMarkedKatoValuesR0159
namespace SplitMarkedKatoValueR0159
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private lemma affine_value_relation (R : CommRingCat.{u}) (F : Type u) [IsDomain R] [Field F]
    (σ : R →+* F) (g : (Spec R).functionField) (v : F)
    (hv : HasValue F (Spec R) (Spec.map (CommRingCat.ofHom σ)) g v)
    (n d : R) (he : g * algebraMap R _ d = algebraMap R _ n) :
    v * σ d = σ n := by
  let X := Spec R
  let p : Spec (CommRingCat.of F) ⟶ X := Spec.map (CommRingCat.ofHom σ)
  let x := p (IsLocalRing.closedPoint F)
  let t : R →+* X.presheaf.stalk x := (StructureSheaf.toStalk R x).hom
  have hi (a : R) : algebraMap (X.presheaf.stalk x) X.functionField
      (t a) = algebraMap R X.functionField a := by
    exact congrArg (fun f : CommRingCat.of R ⟶ X.functionField => f a)
      (StructureSheaf.toStalk_stalkSpecializes ((genericPoint_spec X).specializes trivial))
  have hs (a : R) : Scheme.stalkClosedPointTo p (t a) = σ a := by
    change ((StructureSheaf.toStalk R x) ≫ Scheme.stalkClosedPointTo p) a = σ a
    change (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) ≫
      Scheme.stalkClosedPointTo p) a = σ a
    have hh := Scheme.germ_stalkClosedPointTo_Spec
      (show R ⟶ CommRingCat.of F from CommRingCat.ofHom σ)
    rw [Category.assoc, hh, Iso.inv_hom_id_assoc]
    rfl
  change ∃ b : X.presheaf.stalk x,
    algebraMap (X.presheaf.stalk x) X.functionField b = g ∧
    Scheme.stalkClosedPointTo p b = v at hv
  obtain ⟨b, hb, hbv⟩ := hv
  have h : b * t d =
      t n := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, hi, hi, hb]
    exact he
  have hh := congrArg (Scheme.stalkClosedPointTo p) h
  rw [map_mul, hs, hs, hbv] at hh
  exact hh

private lemma affine_generic (R : CommRingCat.{u}) [IsDomain R] :
    (Spec R).fromSpecStalk (_root_.genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) := by
  apply (cancel_mono (Spec R).toSpecΓ).mp
  rw [Scheme.fromSpecStalk_toSpecΓ, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  change _ = (Scheme.ΓSpecIso R).hom ≫ ((Scheme.ΓSpecIso R).inv ≫ _)
  simp
  rfl

private lemma value_relation (R : CommRingCat.{u}) [IsDomain R]
    (K F : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [Field F]
    (X : Scheme.{u}) [IsIntegral X] (f : Spec R ⟶ X)
    (φ : X.functionField →+* K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (_root_.genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f)
    (σ : R →+* F) (p : Spec (CommRingCat.of F) ⟶ X)
    (hp : Spec.map (CommRingCat.ofHom σ) ≫ f = p)
    (g : X.functionField) (v : F) (hv : HasValue F X p g v)
    (n d : R) (he : φ g * algebraMap R K d = algebraMap R K n) :
    v * σ d = σ n := by
  let Y := Spec R
  let e : K ≃ₐ[R] Y.functionField := IsLocalization.algEquiv (nonZeroDivisors R) K _
  let ψ := e.toRingHom.comp φ
  have hecomp : e.toRingHom.comp (algebraMap R K) = algebraMap R Y.functionField := by
    ext a
    exact e.commutes a
  have hψ : ArithmeticThetaGeometricNormR0150.IsFieldMap f ψ := by
    unfold ArithmeticThetaGeometricNormR0150.IsFieldMap
    change Y.fromSpecStalk (_root_.genericPoint Y) ≫ f =
      Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom e.toRingHom) ≫ _
    rw [Spec.map_comp, Category.assoc, hφ, ← Category.assoc, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom (e.toRingHom.comp (algebraMap R K))) ≫ _
    rw [hecomp, affine_generic]
  have hval := rational_value_transport.2 F F (RingHom.id F) X Y f ψ hψ p
    (Spec.map (CommRingCat.ofHom σ)) (by simpa using hp) g v hv
  apply affine_value_relation R F σ (ψ g) v hval n d
  have hh := congrArg e he
  change e (φ g) * algebraMap R Y.functionField d = algebraMap R Y.functionField n
  simpa only [map_mul, e.commutes] using hh

open ArithmeticThetaAnnularTorsionPrereqR0053 (GenericChart toGeneric tau cx cy)
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaInfinitesimalPolygonR0129 (Tower)
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaAlgebraizedMarkedLineR0136

variable (k : Type) [Field k] [CharZero k]

private def genericScalars : LaurentSeries k →+* GenericChart k :=
  IsLocalization.Away.lift PowerSeries.X
    (show IsUnit (((toGeneric k).comp (ArithmeticThetaAnnularTorsionPrereqR0053.base k))
      PowerSeries.X) from IsLocalization.Away.algebraMap_isUnit (tau k))

private lemma genericScalars_base (a : PowerSeries k) :
    genericScalars k (algebraMap (PowerSeries k) (LaurentSeries k) a) =
      toGeneric k (ArithmeticThetaAnnularTorsionPrereqR0053.base k a) :=
  IsLocalization.Away.lift_eq _ _ a

private def ringChart {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k) :
    Spec (CommRingCat.of (GenericChart k)) ⟶ genericScheme k M :=
  pullback.lift (Spec.map (CommRingCat.ofHom (toGeneric k)) ≫ χ)
    (Spec.map (CommRingCat.ofHom (genericScalars k))) (by
      rw [Category.assoc, hχ, chartBase, genericBase, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext a
      exact (genericScalars_base k a).symm)

private lemma chart_value_relation {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ)
    (a : kˣ) (σ : GenericChart k →+* LaurentSeries k) (hσ : IsSpecialization k a σ)
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (hpoint : Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularThetaR0128.specialize k a)) ≫ χ = p)
    (g : (genericScheme k M).functionField) (v : LaurentSeries k)
    (hv : HasValue _ _ (genericPoint k M p hp) g v)
    (n d : GenericChart k)
    (he : φ g * ArithmeticThetaLocalOrdersR0066.toFunctionField k d =
      ArithmeticThetaLocalOrdersR0066.toFunctionField k n) : v * σ d = σ n := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply value_relation (CommRingCat.of (GenericChart k)) (ChartField k) (LaurentSeries k)
    (genericScheme k M) (ringChart k M χ hχ) φ ?_ σ (genericPoint k M p hp) ?_ g v hv n d he
  · apply (cancel_mono (genericInclusion k M)).mp
    simp only [Category.assoc, ringChart, genericInclusion, pullback.lift_fst]
    rw [← Spec.map_comp_assoc]
    exact hφ
  · apply (cancel_mono (genericInclusion k M)).mp
    simp only [Category.assoc, ringChart, genericInclusion, ArithmeticThetaGenericEvaluationR0140.genericPoint, pullback.lift_fst]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (σ.comp (toGeneric k))) ≫ χ = _
    rw [hσ]
    change Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularThetaR0128.specialize k a) ≫
      CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫ χ = _
    rw [Spec.map_comp, Category.assoc, hpoint]
    rfl

private lemma specialization_coordinates (a : kˣ)
    (σ : GenericChart k →+* LaurentSeries k) (hσ : IsSpecialization k a σ) :
    σ (toGeneric k (tau k)) = ArithmeticThetaLaurentNormR0064.t k ∧
    σ (toGeneric k (cx k)) = HahnSeries.C (a : k) ∧
    σ (toGeneric k (cy k)) = HahnSeries.C (a : k)⁻¹ * ArithmeticThetaLaurentNormR0064.t k := by
  have ht := (ArithmeticThetaScaledAnnularR0050.specialization_coordinates
    k 1 0 (by decide) (by decide) (a : k) a.ne_zero)
  have he (b) : σ (toGeneric k b) = algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaAnnularThetaR0128.specialize k a b) := RingHom.congr_fun hσ b
  constructor
  · rw [he]
    change algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaScaledAnnularR0050.specialization k 1 0 _ _ (a : k) a.ne_zero
        (ArithmeticThetaScaledAnnularR0050.tau k 1)) = _
    rw [ht.1]
    simp [ArithmeticThetaLaurentNormR0064.t, LaurentSeries.coe_algebraMap,
      HahnSeries.ofPowerSeries_X]
  constructor
  · rw [he]
    change algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaScaledAnnularR0050.specialization k 1 0 _ _ (a : k) a.ne_zero
        (ArithmeticThetaScaledAnnularR0050.cx k 1)) = _
    rw [ht.2.1]
    simp [LaurentSeries.coe_algebraMap]
  · rw [he]
    change algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaScaledAnnularR0050.specialization k 1 0 _ _ (a : k) a.ne_zero
        (ArithmeticThetaScaledAnnularR0050.cy k 1)) = _
    rw [ht.2.2]
    simp [ArithmeticThetaLaurentNormR0064.t, LaurentSeries.coe_algebraMap,
      HahnSeries.ofPowerSeries_X]

private lemma specialization_filtered (a : kˣ)
    (σ : GenericChart k →+* LaurentSeries k) (hσ : IsSpecialization k a σ)
    (N : ℕ) (b : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k)
    (hb : b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N)
    (e : ℤ) (he : e < (N : ℤ)) : (σ (toGeneric k b)).coeff e = 0 := by
  have h := (Classical.choose_spec
    (ArithmeticThetaScaledTateCompletionExtensionR0048.completion_specialization_exists_and_filtered
      k 1 0 (by decide) (by decide) (a : k) a.ne_zero)).2 N b hb
  change ArithmeticThetaAnnularThetaR0128.specialize k a b ∈
    (Ideal.span {PowerSeries.X}) ^ (1 * N) at h
  rw [one_mul, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff] at h
  have hsb : σ (toGeneric k b) = algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaAnnularThetaR0128.specialize k a b) := RingHom.congr_fun hσ b
  rw [hsb]
  change (algebraMap (PowerSeries k) (LaurentSeries k)
    (ArithmeticThetaAnnularThetaR0128.specialize k a b)).coeff e = 0
  by_cases hneg : e < 0
  · simp [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe, hneg]
  · simpa [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe, hneg] using h e.natAbs (by omega)

-- Exact accepted private constants; the numeric Name component is preserved.
local macro "acceptedMarkedGammaR0159" : term => pure (Lean.mkIdent
  (.str (.str (.str (.num `_private.FullGammaEvaluationR0156 0)
    "ArithmeticThetaAnnularNormBridgeR0156") "FullGammaEvaluation") "genericSection_gamma_isGamma"))
local macro "acceptedMarkedPoweredR0159" : term => pure (Lean.mkIdent
  (.str (.str (.str (.num `_private.FullGammaEvaluationR0156 0)
    "ArithmeticThetaAnnularNormBridgeR0156") "FullGammaEvaluation") "genericSection_powered_isGamma"))

private lemma specialized_gamma (a : kˣ) (σ : GenericChart k →+* LaurentSeries k)
    (hσ : IsSpecialization k a σ) (r c : ℕ) (hr : 0 < r) (hc : 1 < c)
    (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (j : Fin r) (γ δ : LaurentSeries k)
    (hγ : ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ)
    (hδ : ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ) :
    σ (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt) = γ ∧
    σ (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ hr hc hdiv hcop hζ j.isLt) = δ := by
  obtain ⟨ht, hx, hy⟩ := specialization_coordinates k a σ hσ
  have hG := acceptedMarkedGammaR0159 k k (a : k) σ ht hx hy
    (specialization_filtered k a σ hσ) r j.val hr j.isLt
  have hD := acceptedMarkedPoweredR0159 k k (a : k) σ ht hx hy r c j.val ζ hr hc hdiv
    (specialization_filtered k a σ hσ) hcop hζ j.isLt
  constructor
  · exact (ArithmeticThetaLaurentNormR0064.gamma_exists_unique k r j.val (a : k) hr a.ne_zero).unique hG hγ
  · exact (ArithmeticThetaLaurentNormR0064.gamma_exists_unique k r (c*j.val) ((a : k)^c)
      hr (pow_ne_zero _ a.ne_zero)).unique hD hδ

private lemma specialization_tpower (a : kˣ) (σ : GenericChart k →+* LaurentSeries k)
    (hσ : IsSpecialization k a σ) (e : ℤ) :
    σ (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e) =
      ArithmeticThetaLaurentNormR0064.t k ^ e := by
  have hparam : ((ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k :
      (GenericChart k)ˣ) : GenericChart k) = toGeneric k (tau k) :=
    (IsLocalization.Away.algebraMap_isUnit _).unit_spec
  change σ (↑(ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) = _
  calc
    _ = ((Units.map σ.toMonoidHom
      (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e)) : LaurentSeries k) := rfl
    _ = (σ (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k)) ^ e := by
      rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
      rfl
    _ = _ := by rw [hparam, (specialization_coordinates k a σ hσ).1]

local macro "acceptedMarkedNormalizationR0159" : term => pure (Lean.mkIdent
  (.str (.str (.str (.num `_private.LiteralSplitGeometricNormR0156 0)
    "ArithmeticThetaAnnularNormBridgeR0156") "LiteralSplitGeometricNorm") "normalization"))

private lemma specialization_literal (a : kˣ) (σ : GenericChart k →+* LaurentSeries k)
    (hσ : IsSpecialization k a σ) (r c : ℕ) (hr : 0 < r) (hc : 1 < c)
    (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (j : Fin r) (γ δ : LaurentSeries k)
    (hγ : ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ)
    (hδ : ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ)
    (hδ0 : δ ≠ 0) :
    let n := ArithmeticThetaAnnularTorsionPrereqR0053.tpower k ((r*(c^2-1)/12 : ℕ) : ℤ) *
      ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt ^ (c^2)
    let d := (-ArithmeticThetaLocalNormR0054.localZ k j.val) ^ (c*(c-1)/2) *
      ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ hr hc hdiv hcop hζ j.isLt
    σ d ≠ 0 ∧ σ n / σ d = literalValue k r c j.val (a : k) γ δ := by
  dsimp only
  obtain ⟨hG, hD⟩ := specialized_gamma k a σ hσ r c hr hc hdiv hcop ζ hζ j γ δ hγ hδ
  have hz : σ (ArithmeticThetaLocalNormR0054.localZ k j.val) =
      HahnSeries.C (a : k) * ArithmeticThetaLaurentNormR0064.t k ^ j.val := by
    simp only [ArithmeticThetaLocalNormR0054.localZ,
      ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate, map_mul, map_pow]
    rw [(specialization_coordinates k a σ hσ).1,
      (specialization_coordinates k a σ hσ).2.1, mul_comm]
  simp only [map_mul, map_pow, map_neg, hG, hD, hz, specialization_tpower k a σ hσ]
  constructor
  · apply mul_ne_zero _ hδ0
    apply pow_ne_zero
    apply neg_ne_zero.mpr
    apply mul_ne_zero
    · exact (map_ne_zero (HahnSeries.C : k →+* LaurentSeries k)).mpr a.ne_zero
    · apply pow_ne_zero
      simp [ArithmeticThetaLaurentNormR0064.t]
  · obtain ⟨hK, hp⟩ := acceptedMarkedNormalizationR0159 c r hc hcop
    rw [hK]
    simp only [literalValue, hp, zpow_neg, zpow_natCast]
    rw [← zpow_natCast (ArithmeticThetaLaurentNormR0064.t k) r, ← zpow_mul]
    ring

private lemma powered_gamma_ne_zero (r c : ℕ) (hr : 0 < r) (j : Fin r) (a : kˣ)
    (N : ℕ) (hcopN : Nat.Coprime c N) (hidx : r ∣ N*j.val)
    (haN : (a : k)^N = 1) (hne : j.val ≠ 0 ∨ (a : k) ≠ 1)
    (δ : LaurentSeries k)
    (hδ : ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ) : δ ≠ 0 := by
  intro hz
  obtain ⟨hjc, hac⟩ := (gamma_zero_locus k r (c*j.val) ((a : k)^c) δ hr
    (pow_ne_zero _ a.ne_zero) hδ).mp hz
  have hj : r ∣ j.val := by
    have hh := Nat.dvd_gcd hjc hidx
    simpa [Nat.gcd_mul_right, hcopN.gcd_eq_one] using hh
  have hj0 := Nat.eq_zero_of_dvd_of_lt hj j.isLt
  have haNu : a^N = 1 := by apply Units.ext; simpa using haN
  have hacu : a^c = 1 := by apply Units.ext; simpa using hac
  have hd : orderOf a ∣ Nat.gcd c N :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hacu) (orderOf_dvd_of_pow_eq_one haNu)
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcopN.gcd_eq_one ▸ hd))
  exact hne.elim (fun h => h hj0) (fun h => h (congrArg Units.val ha1))

end SplitMarkedKatoValueR0159


open SplitMarkedKatoValueR0159

/-- The actual normalized Kato function has its full literal gamma quotient as
its stalk value at every specified nonidentity marked torsion point. -/
theorem split_marked_kato_value :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hcr : c ∣ r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (j : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j a p) (N : ℕ) (hN : 0 < N) (hcopN : Nat.Coprime c N) (hidx : r ∣ N*j.val) (haN : (a : k)^N = 1) (hne : j.val ≠ 0 ∨ (a : k) ≠ 1) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g → ∀ (γ δ : LaurentSeries k), ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ → ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ → ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g (ArithmeticThetaMarkedKatoValuesR0159.literalValue k r c j.val (a : k) γ δ) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ c hc hcop hcr ζ hζ χ hχ φ hφ
    j a p hp N hN hcopN hidx haN hne g hg γ δ hγ hδ
  obtain ⟨v, ⟨hv0, hv⟩, _⟩ := marked_kato_regularity k r hr h3 he T M hM s hs G hG
    c hc hcop j a p hp N hN hcopN hidx haN hne g hg.1
  obtain ⟨hpoint, σ, hσ, _⟩ := completed_marked_specialization k r hr h3 he T M hM j a p hp
    (χ j) (hχ j)
  obtain ⟨g₀, hg₀, _⟩ := ArithmeticThetaUnsplitExpansionR0158.split_period_kato_formula
    k r c hc hcop hr h3 he T M hM s hs G hG ζ hζ χ hχ φ hφ hcr
  obtain ⟨g₁, hg₁, hu⟩ := ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG c hc hcop
  have hgg : g = g₀ := (hu g hg).trans (hu g₀ hg₀.1).symm
  have hδ0 := powered_gamma_ne_zero k r c hr j a N hcopN hidx haN hne δ hδ
  let n := ArithmeticThetaAnnularTorsionPrereqR0053.tpower k ((r*(c^2-1)/12 : ℕ) : ℤ) *
    ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt ^ (c^2)
  let d := (-ArithmeticThetaLocalNormR0054.localZ k j.val) ^ (c*(c-1)/2) *
    ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val (ζ : k) hr hc hcr hcop hζ j.isLt
  obtain ⟨hd, heval⟩ := specialization_literal k a σ hσ r c hr hc hcr hcop (ζ : k) hζ
    j γ δ hγ hδ hδ0
  have hd0 : d ≠ 0 := fun h => hd (by change σ d = 0; rw [h, map_zero])
  have hdf : ArithmeticThetaLocalOrdersR0066.toFunctionField k d ≠ 0 := by
    change algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
      (ArithmeticThetaKatoAnnularR0152.ChartField k) d ≠ 0
    simpa only [map_zero] using
      (IsFractionRing.injective (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
        (ArithmeticThetaKatoAnnularR0152.ChartField k)).ne hd0
  have hrel : φ j g * ArithmeticThetaLocalOrdersR0066.toFunctionField k d =
      ArithmeticThetaLocalOrdersR0066.toFunctionField k n := by
    rw [hgg, hg₀.2 j]
    dsimp [ArithmeticThetaAnnularNormBridgeR0156.literalTheta, n, d] at hdf ⊢
    simp only [map_mul, map_pow, map_neg] at hdf ⊢
    exact div_mul_cancel₀ _ hdf
  have hval := chart_value_relation k M (χ j) (hχ j).1 (φ j) (hφ j) a σ hσ p hp.1
    hpoint g v hv n d hrel
  have hvEq : v = literalValue k r c j.val (a : k) γ δ :=
    ((eq_div_iff hd).mpr hval).trans heval
  exact hvEq ▸ hv

#print axioms split_marked_kato_value
end ArithmeticThetaMarkedKatoValuesR0159
