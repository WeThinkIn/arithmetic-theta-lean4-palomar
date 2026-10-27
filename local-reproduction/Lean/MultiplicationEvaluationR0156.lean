import FaithfulAnnularEvaluationR0156

/-! Multiplication on the actual marked generic curve and its faithful annular evaluation. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace MultiplicationEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaScaledTateBridgeR0046
section Completion
variable {R S : Type*} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)

private def stage (m : ℕ) : AdicCompletion I R →+* S ⧸ J ^ m :=
  (Ideal.quotientMap (J ^ m) f
    ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow _ m))).comp
    (AdicCompletion.evalₐ I m).toRingHom

private lemma stage_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (stage I J f h n) = stage I J f h m := by
  apply RingHom.ext
  intro z
  have hc : (Ideal.Quotient.factorPow J hmn).comp
      (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow _ n))) =
      (Ideal.quotientMap (J ^ m) f
        ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow _ m))).comp
        (Ideal.Quotient.factorPow I hmn) := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  have hh := RingHom.congr_fun hc (AdicCompletion.evalₐ I n z)
  simp only [RingHom.comp_apply] at hh
  rw [show Ideal.Quotient.factorPow I hmn
      (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z by
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    have ha := SModEq.sub_mem.mp (a.property hmn)
    simpa only [smul_eq_mul, Ideal.mul_top, neg_sub] using neg_mem ha] at hh
  exact hh

private def extend [IsAdicComplete J S] : AdicCompletion I R →+* S :=
  IsAdicComplete.liftRingHom J (stage I J f h) (stage_compat I J f h)

private lemma extend_of [IsAdicComplete J S] (r : R) :
    extend I J f h (algebraMap R _ r) = f r := by
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  rw [extend, IsAdicComplete.mk_liftRingHom]
  simp [stage, AdicCompletion.evalₐ_of]
end Completion

variable (k : Type) [Field k] [CharZero k]

section Families
variable {B : Type} [CommRing B] (σ : k →+* B) (u : Bˣ)

private def nodeEval : Node k 1 →+* PowerSeries B :=
  Ideal.Quotient.lift (relationIdeal k 1)
    (MvPolynomial.eval₂Hom (PowerSeries.map σ)
      (fun i => if i = (0 : Fin 2) then PowerSeries.C (u : B)
        else PowerSeries.C (↑u⁻¹ : B) * PowerSeries.X)) (by
    change relationIdeal k 1 ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    simp [relation, parameter, ← mul_assoc, ← map_mul])

private lemma nodeEval_base (b : PowerSeries k) :
    nodeEval k σ u (algebraMap (PowerSeries k) (Node k 1) b) = PowerSeries.map σ b := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C b) = _
  simp
private lemma nodeEval_x : nodeEval k σ u (x k 1) = PowerSeries.C (u : B) := by
  simp [nodeEval, x, quotientMap]
private lemma nodeEval_y : nodeEval k σ u (y k 1) =
    PowerSeries.C (↑u⁻¹ : B) * PowerSeries.X := by simp [nodeEval, y, quotientMap]
private lemma nodeEval_t : nodeEval k σ u (t k 1) = PowerSeries.X := by
  rw [t, nodeEval_base]; simp [parameter]

private def chartEval : Chart k →+* PowerSeries B :=
  extend (nodeIdeal k 1) (Ideal.span {PowerSeries.X}) (nodeEval k σ u) (by
    rw [nodeIdeal, Ideal.span_singleton_le_iff_mem]
    change nodeEval k σ u (t k 1) ∈ Ideal.span {PowerSeries.X}
    rw [nodeEval_t]; exact Ideal.mem_span_singleton_self _)

private lemma chartEval_of (b : Node k 1) :
    chartEval k σ u (toCompleted k 1 b) = nodeEval k σ u b := extend_of _ _ _ _ _
private lemma chartEval_base (b : PowerSeries k) :
    chartEval k σ u (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = PowerSeries.map σ b :=
  (chartEval_of k σ u _).trans (nodeEval_base k σ u b)
private lemma chartEval_x :
    chartEval k σ u (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = PowerSeries.C (u : B) :=
  (chartEval_of k σ u _).trans (nodeEval_x k σ u)
private lemma chartEval_y :
    chartEval k σ u (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      PowerSeries.C (↑u⁻¹ : B) * PowerSeries.X :=
  (chartEval_of k σ u _).trans (nodeEval_y k σ u)
private lemma chartEval_t : chartEval k σ u (completedParameter k 1) = PowerSeries.X :=
  (chartEval_of k σ u _).trans (nodeEval_t k σ u)

private lemma chartHom_ext (f g : Chart k →+* PowerSeries B)
    (htf : f (completedParameter k 1) = PowerSeries.X)
    (htg : g (completedParameter k 1) = PowerSeries.X)
    (hb : ∀ b : PowerSeries k, f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b))
    (hx : f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cx k))
    (hy : f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) : f = g := by
  have hn : f.comp (toCompleted k 1) = g.comp (toCompleted k 1) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hb
    · intro i; fin_cases i
      · exact hx
      · exact hy
  have hfilt (f : Chart k →+* PowerSeries B)
      (ht : f (completedParameter k 1) = PowerSeries.X) (N : ℕ) (b : Chart k)
      (hm : b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N) :
      f b ∈ (Ideal.span {PowerSeries.X}) ^ N := by
    have hle : Ideal.span {completedParameter k 1} ≤
        (Ideal.span {PowerSeries.X}).comap f := by
      rw [Ideal.span_singleton_le_iff_mem]
      change f (completedParameter k 1) ∈ Ideal.span {PowerSeries.X}
      rw [ht]; exact Ideal.mem_span_singleton_self _
    exact ((Ideal.pow_right_mono hle N).trans (Ideal.le_comap_pow _ N)) hm
  apply RingHom.ext
  intro b
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(PowerSeries.X : PowerSeries B)})).mpr
  intro N
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 N b
  have he := RingHom.congr_fun hn (quotientMap k 1 p)
  simp only [RingHom.comp_apply] at he
  have hm := Ideal.sub_mem _ (hfilt f htf N _ hp) (hfilt g htg N _ hp)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  simpa only [map_sub, RingHom.comp_apply, he, sub_sub_sub_cancel_right] using hm

private lemma chartEval_natural {C : Type} [CommRing C] (τ : B →+* C) :
    (PowerSeries.map τ).comp (chartEval k σ u) =
      chartEval k (τ.comp σ) (Units.map τ u) := by
  apply chartHom_ext
  · simp only [RingHom.comp_apply, chartEval_t, PowerSeries.map_X]
  · exact chartEval_t k _ _
  · intro b
    simp only [RingHom.comp_apply, chartEval_base]
    exact (RingHom.congr_fun (PowerSeries.map_comp σ τ) b).symm
  · simp [chartEval_x]
  · simp [chartEval_y]
end Families


open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaPolygonCartierR0133.MarkedIdealTowerBaseChangeR0133
open ArithmeticThetaPolygonCartierR0133.GlobalMarkedIdealChartsR0133

private lemma specIdeal_le {R : Type} [CommRing R]
    (I J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : specIdeal I ≤ specIdeal J) : I ≤ J := by
  apply Scheme.IdealSheafData.le_of_isAffine
  have he := Ideal.map_mono (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) h
  have hi : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
    ext x
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id x
  simpa only [specIdeal, Ideal.map_map, hi, Ideal.map_id] using he

private lemma chartEval_section {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (zeroIndex r hr) a p) :
    Spec.map (CommRingCat.ofHom (chartEval k (RingHom.id k) a)) ≫ χ = p := by
  let η := Spec.map (CommRingCat.ofHom (chartEval k (RingHom.id k) a))
  have hbase : η ≫ χ ≫ M.p = 𝟙 (baseScheme k) := by
    rw [hχ.1, chartBase, ← Spec.map_comp]
    have h : (chartEval k (RingHom.id k) a).comp
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k) = RingHom.id _ := by
      ext b
      simp [chartEval_base, PowerSeries.map_id]
    change Spec.map (CommRingCat.ofHom ((chartEval k (RingHom.id k) a).comp
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k))) = _
    rw [h]; exact Spec.map_id _
  letI : IsClosedImmersion p :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM p hp.1
  have hker : p.ker ≤ (η ≫ χ).ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le]
    apply specIdeal_le
    change markedChartIdeal k M p χ ≤ specIdeal η.ker
    rw [(completed_marked_chart_ideal k r hr h3 T M hM _ _ a p hp χ hχ).1]
    rw [show specIdeal η.ker = RingHom.ker (chartEval k (RingHom.id k) a) from spec_kernel _]
    rw [Ideal.span_singleton_le_iff_mem]
    change chartEval k (RingHom.id k) a (markedEquation k (zeroIndex r hr) (zeroIndex r hr) a) = 0
    have hn : next r hr (zeroIndex r hr) ≠ zeroIndex r hr := by
      intro hh
      have := congrArg Fin.val hh
      simp [next, zeroIndex, Nat.mod_eq_of_lt (show 1 < r by omega)] at this
    simp [markedEquation, hn, map_sub, chartEval_x, chartEval_base, PowerSeries.map_id]
  let q := IsClosedImmersion.lift p (η ≫ χ) hker
  have hq : q ≫ p = η ≫ χ := IsClosedImmersion.lift_fac p _ hker
  have hqid : q = 𝟙 (baseScheme k) := by
    have hh := congrArg (fun f => f ≫ M.p) hq
    simpa only [Category.assoc, hp.1, Category.comp_id, hbase] using hh
  exact hq.symm.trans (hqid ▸ Category.id_comp p)

private def laurentUnit (n : ℕ) : (LaurentPolynomial k)ˣ :=
  ⟨LaurentPolynomial.T (n : ℤ), LaurentPolynomial.T (-(n : ℤ)),
    by rw [← LaurentPolynomial.T_add]; simp only [add_neg_cancel, LaurentPolynomial.T_zero],
    by rw [← LaurentPolynomial.T_add]; simp only [neg_add_cancel, LaurentPolynomial.T_zero]⟩
private def family (n : ℕ) : Chart k →+* PowerSeries (LaurentPolynomial k) :=
  chartEval k LaurentPolynomial.C (laurentUnit k n)
private def special (a : kˣ) : LaurentPolynomial k →+* k :=
  LaurentPolynomial.eval₂ (RingHom.id k) a

private lemma special_joint (b : LaurentPolynomial k)
    (h : ∀ a : kˣ, special k a b = 0) : b = 0 := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow b
  have hz (a : kˣ) : p.eval (a : k) = 0 := by
    have hh := congrArg (special k a) hp
    rw [map_mul, h a, zero_mul] at hh
    simpa [special, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_at_apply] using hh
  have hpz : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono
    intro x hx
    exact hz (Units.mk0 x hx.2)
  rw [hpz, map_zero] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_right (LaurentPolynomial.isUnit_T _).ne_zero

private lemma special_family (a : kˣ) (n : ℕ) :
    (PowerSeries.map (special k a)).comp (family k n) =
      chartEval k (RingHom.id k) (a^n) := by
  rw [family, chartEval_natural]
  have hc : (special k a).comp LaurentPolynomial.C = RingHom.id k := by
    ext b; exact LaurentPolynomial.eval₂_C _ _ _
  have hu : Units.map (special k a) (laurentUnit k n) = a^n := by
    apply Units.ext
    exact LaurentPolynomial.eval₂_T_n _ _ _
  rw [hc, hu]

private abbrev FamilyRing := Localization.Away (PowerSeries.X : PowerSeries (LaurentPolynomial k))
private def specialGeneric (a : kˣ) : FamilyRing k →+* LaurentSeries k :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries (LaurentPolynomial k))
    (show IsUnit (((HahnSeries.ofPowerSeries ℤ k).comp (PowerSeries.map (special k a)))
      PowerSeries.X) from by
        simp only [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
        exact isUnit_iff_ne_zero.mpr (by simp))

private lemma specialGeneric_of (a : kˣ) (b : PowerSeries (LaurentPolynomial k)) :
    specialGeneric k a (algebraMap _ (FamilyRing k) b) =
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (special k a) b) :=
  IsLocalization.Away.lift_eq _ _ b

private lemma specialGeneric_joint (b : FamilyRing k)
    (h : ∀ a : kˣ, specialGeneric k a b = 0) : b = 0 := by
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (PowerSeries.X : PowerSeries (LaurentPolynomial k))) b
  have hp (a : kˣ) : specialGeneric k a (algebraMap _ (FamilyRing k) p) = 0 := by
    rw [← IsLocalization.mk'_spec (FamilyRing k) p s, map_mul, h, zero_mul]
  have hp0 : p = 0 := by
    apply PowerSeries.ext
    intro m
    apply special_joint k
    intro a
    have hh : PowerSeries.map (special k a) p = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
        simpa only [map_zero] using (specialGeneric_of k a p).symm.trans (hp a))
    have hc := congrArg (PowerSeries.coeff m) hh
    simpa [PowerSeries.coeff_map] using hc
  simp [hp0]

private lemma specialGeneric_dense : Dense (Set.range (fun a : kˣ =>
    PrimeSpectrum.comap (specialGeneric k a) (⊥ : PrimeSpectrum (LaurentSeries k)))) := by
  rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hv : PrimeSpectrum.vanishingIdeal (Set.range (fun a : kˣ =>
      PrimeSpectrum.comap (specialGeneric k a) (⊥ : PrimeSpectrum (LaurentSeries k)))) = ⊥ := by
    apply le_antisymm _ bot_le
    intro b hb
    apply specialGeneric_joint k b
    intro a
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hb _ ⟨a, rfl⟩
  rw [hv]
  exact PrimeSpectrum.zeroLocus_bot


private def baseToFamily : LaurentSeries k →+* FamilyRing k :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries k)
    (show IsUnit (((algebraMap (PowerSeries (LaurentPolynomial k)) (FamilyRing k)).comp
      (PowerSeries.map LaurentPolynomial.C)) PowerSeries.X) from by
      simp only [RingHom.comp_apply, PowerSeries.map_X]
      exact IsLocalization.Away.algebraMap_isUnit _)

private lemma baseToFamily_of (b : PowerSeries k) :
    baseToFamily k (algebraMap (PowerSeries k) (LaurentSeries k) b) =
      algebraMap (PowerSeries (LaurentPolynomial k)) (FamilyRing k)
        (PowerSeries.map LaurentPolynomial.C b) := IsLocalization.Away.lift_eq _ _ b

private lemma specialGeneric_base (a : kˣ) :
    (specialGeneric k a).comp (baseToFamily k) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries k))
  apply RingHom.ext
  intro b
  simp only [RingHom.comp_apply, baseToFamily_of, specialGeneric_of, RingHom.id_apply]
  change HahnSeries.ofPowerSeries ℤ k ((PowerSeries.map (special k a))
    ((PowerSeries.map LaurentPolynomial.C) b)) = HahnSeries.ofPowerSeries ℤ k b
  congr 1
  have hc : (special k a).comp LaurentPolynomial.C = RingHom.id k := by
    ext b; exact LaurentPolynomial.eval₂_C _ _ _
  rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hc, PowerSeries.map_id]
  rfl

private def familyMap (n : ℕ) : Chart k →+* FamilyRing k :=
  (algebraMap (PowerSeries (LaurentPolynomial k)) (FamilyRing k)).comp (family k n)

private lemma familyMap_base (n : ℕ) :
    Spec.map (CommRingCat.ofHom (familyMap k n)) ≫ chartBase k =
      Spec.map (CommRingCat.ofHom (baseToFamily k)) ≫ genericBase k := by
  rw [chartBase, genericBase, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact (congrArg (algebraMap _ (FamilyRing k)) (chartEval_base k _ _ b)).trans
    (baseToFamily_of k b).symm

private def familyPoint {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (n : ℕ) : Spec (CommRingCat.of (FamilyRing k)) ⟶ genericScheme k M :=
  pullback.lift (Spec.map (CommRingCat.ofHom (familyMap k n)) ≫ χ)
    (Spec.map (CommRingCat.ofHom (baseToFamily k))) (by
      rw [Category.assoc, hχ, familyMap_base])

private lemma familyPoint_inclusion {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k) (n : ℕ) :
    familyPoint k M χ hχ n ≫ genericInclusion k M =
      Spec.map (CommRingCat.ofHom (familyMap k n)) ≫ χ := pullback.lift_fst _ _ _
private lemma familyPoint_structure {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k) (n : ℕ) :
    familyPoint k M χ hχ n ≫ genericStructure k M =
      Spec.map (CommRingCat.ofHom (baseToFamily k)) := pullback.lift_snd _ _ _

private lemma familyPoint_special {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (a : kˣ) (n : ℕ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (zeroIndex r hr) (a^n) p) :
    Spec.map (CommRingCat.ofHom (specialGeneric k a)) ≫ familyPoint k M χ hχ.1 n =
      ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1 := by
  apply pullback.hom_ext
  · change _ ≫ genericInclusion k M = _ ≫ genericInclusion k M
    rw [Category.assoc, familyPoint_inclusion, ← Category.assoc, ← Spec.map_comp]
    have he : (specialGeneric k a).comp (familyMap k n) =
        (HahnSeries.ofPowerSeries ℤ k).comp (chartEval k (RingHom.id k) (a^n)) := by
      apply RingHom.ext
      intro b
      exact (specialGeneric_of k a (family k n b)).trans
        (congrArg (HahnSeries.ofPowerSeries ℤ k) (RingHom.congr_fun (special_family k a n) b))
    change Spec.map (CommRingCat.ofHom ((specialGeneric k a).comp (familyMap k n))) ≫ χ = _
    rw [he]
    change Spec.map (CommRingCat.ofHom (chartEval k (RingHom.id k) (a^n)) ≫
      CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ k)) ≫ χ = _
    rw [Spec.map_comp, Category.assoc, chartEval_section k h3 M hM χ hχ (a^n) p hp]
    exact (pullback.lift_fst _ _ _).symm
  · change _ ≫ genericStructure k M = _ ≫ genericStructure k M
    rw [Category.assoc, familyPoint_structure, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((specialGeneric k a).comp (baseToFamily k))) = _
    rw [specialGeneric_base]
    exact (Spec.map_id _).trans (pullback.lift_snd _ _ _).symm


open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaHodgeFourTorsionR0147

private lemma familyPoint_multiplication {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ) (d : ℕ) :
    familyPoint k M χ hχ.1 1 ≫ multiplication k M G d = familyPoint k M χ hχ.1 d := by
  letI : IsDomain (FamilyRing k) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers (PowerSeries.X : PowerSeries (LaurentPolynomial k))) (FamilyRing k) (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero)
  letI : IsProper (genericStructure k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  apply Scheme.Hom.eq_of_forall_comp_eq_of_dense_of_isReduced
    _ _ (genericStructure k M)
    (by rw [Category.assoc, MultiplicationDifferential.multiplication_over,
      familyPoint_structure, familyPoint_structure])
    _ (specialGeneric_dense k)
  rintro x ⟨a, rfl⟩
  refine ⟨LaurentSeries k, inferInstance, Spec.map (CommRingCat.ofHom (specialGeneric k a)),
    ⟨(⊥ : PrimeSpectrum (LaurentSeries k)), rfl⟩, ?_⟩
  rw [← Category.assoc]
  let p := MarkedPointAddition.sectionAt k h3 M hM (zeroIndex r hr) a
  have hp := MarkedPointAddition.sectionAt_spec k h3 M hM (zeroIndex r hr) a
  have hpa : MarkedLift k M (zeroIndex r hr) (a^1) p := by simpa using hp
  rw [familyPoint_special k h3 M hM χ hχ a 1 p hpa,
    familyPoint_special k h3 M hM χ hχ a d
      (MarkedPointAddition.sectionAt k h3 M hM (zeroIndex r hr) (a^d))
      (MarkedPointAddition.sectionAt_spec k h3 M hM (zeroIndex r hr) (a^d))]
  have hm := MarkedExactTorsion.point_nsmul k M hM h3 he s hs G hG (zeroIndex r hr) a d
  have hi : (⟨(d*(zeroIndex r hr).val)%r, Nat.mod_lt _ hr⟩ : Fin r) = zeroIndex r hr := by
    apply Fin.ext; simp [zeroIndex]
  rw [hi] at hm
  have hn := G.nsmul_natural (genericStructure k M) (𝟙 _)
    (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) a).val
    (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) a).property d
    (ArithmeticThetaHodgeFourTorsionR0147.universalPoint k M)
  have hpt : WeierstrassProjModel.schemeHomOverComp
      (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) a).val
      (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) a).property
      (ArithmeticThetaHodgeFourTorsionR0147.universalPoint k M) =
      MarkedPointAddition.point k h3 M hM (zeroIndex r hr) a :=
    Subtype.ext (Category.comp_id _)
  rw [hpt, hm] at hn
  simpa only [MarkedPointAddition.point, pointOver, Category.id_comp,
    WeierstrassProjModel.schemeHomOverComp, multiplication, p] using
    congrArg Subtype.val hn

private def familyToSeries : FamilyRing k →+* Series k :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries (LaurentPolynomial k))
    (show IsUnit (((HahnSeries.ofPowerSeries ℤ (Coeff k)).comp
      (PowerSeries.map (algebraMap (LaurentPolynomial k) (Coeff k)))) PowerSeries.X) from by
      simp only [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
      exact isUnit_iff_ne_zero.mpr (HahnSeries.single_ne_zero one_ne_zero))

private lemma familyToSeries_of (b : PowerSeries (LaurentPolynomial k)) :
    familyToSeries k (algebraMap _ (FamilyRing k) b) =
      HahnSeries.ofPowerSeries ℤ (Coeff k)
        (PowerSeries.map (algebraMap (LaurentPolynomial k) (Coeff k)) b) :=
  IsLocalization.Away.lift_eq _ _ b

private lemma family_coeff (n : ℕ) :
    (PowerSeries.map (algebraMap (LaurentPolynomial k) (Coeff k))).comp (family k n) =
      FaithfulAnnularEvaluation.chartEvaluation k 1 n := by
  apply chartHom_ext
  · simp only [family, RingHom.comp_apply, chartEval_t, PowerSeries.map_X]
  · exact FaithfulAnnularEvaluation.chartEvaluation_parameter k 1 n
  · intro b
    simp only [family, RingHom.comp_apply, chartEval_base,
      FaithfulAnnularEvaluation.chartEvaluation_base]
    exact (RingHom.congr_fun (PowerSeries.map_comp LaurentPolynomial.C
      (algebraMap (LaurentPolynomial k) (Coeff k))) b).symm
  · simp only [family, RingHom.comp_apply, chartEval_x, PowerSeries.map_C,
      FaithfulAnnularEvaluation.chartEvaluation_x]
    congr 1
    simp [laurentUnit, coordinate, ArithmeticThetaLaurentNormR0064.w, ← map_pow,
      LaurentPolynomial.T_pow]
  · simp only [family, RingHom.comp_apply, chartEval_y, map_mul, PowerSeries.map_C,
      PowerSeries.map_X, FaithfulAnnularEvaluation.chartEvaluation_y]
    congr 2
    have hu : algebraMap (LaurentPolynomial k) (Coeff k) (↑((laurentUnit k n)⁻¹)) =
        (coordinate k 1 n)⁻¹ := by
      have hh := map_mul (algebraMap (LaurentPolynomial k) (Coeff k)) (laurentUnit k n : LaurentPolynomial k)
        (↑((laurentUnit k n)⁻¹))
      have ht : algebraMap (LaurentPolynomial k) (Coeff k) (laurentUnit k n : LaurentPolynomial k) =
          coordinate k 1 n := by
        simp [laurentUnit, coordinate, ArithmeticThetaLaurentNormR0064.w, ← map_pow,
          LaurentPolynomial.T_pow]
      rw [Units.mul_inv, map_one, ht] at hh
      exact eq_inv_of_mul_eq_one_right hh.symm
    exact hu

private lemma evaluation_chart (n : ℕ) (v : ChartField k →+* Series k)
    (hv : IsEvaluation k 1 n v) (b : Chart k) :
    v (chartToField k b) = HahnSeries.ofPowerSeries ℤ (Coeff k)
      (FaithfulAnnularEvaluation.chartEvaluation k 1 n b) := by
  let f := (HahnSeries.ofPowerSeries ℤ (Coeff k)).comp
    (FaithfulAnnularEvaluation.chartEvaluation k 1 n)
  have hbase (b : PowerSeries k) : v (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) =
      f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) := by
    rw [hv.1]
    simp only [f, RingHom.comp_apply, FaithfulAnnularEvaluation.chartEvaluation_base]
    rfl
  have hx : v (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) =
      f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) := by
    rw [hv.2.1]; simp [f, FaithfulAnnularEvaluation.chartEvaluation_x]
  have hy : v (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) =
      f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) := by
    rw [hv.2.2.1]
    simp [f, FaithfulAnnularEvaluation.chartEvaluation_y, ArithmeticThetaLaurentNormR0064.t,
      HahnSeries.ofPowerSeries_X]
  have hnode : (v.comp (chartToField k)).comp (toCompleted k 1) = f.comp (toCompleted k 1) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hbase
    · intro i; fin_cases i
      · exact hx
      · exact hy
  apply HahnSeries.ext
  funext e
  let N := (e+1).toNat
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 N b
  have he : e < (N : ℤ) := by dsimp [N]; omega
  have h1 := hv.2.2.2 N _ hp e he
  have hf := FaithfulAnnularEvaluation.chartEvaluation_filtered k 1 n N _ hp
  change FaithfulAnnularEvaluation.chartEvaluation k 1 n _ ∈
    (Ideal.span {PowerSeries.X}) ^ N at hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hf
  have h2 : (f (b - toCompleted k 1 (quotientMap k 1 p))).coeff e = 0 := by
    change (HahnSeries.ofPowerSeries ℤ (Coeff k) _).coeff e = 0
    by_cases hneg : e < 0
    · simp [PowerSeries.coeff_coe, hneg]
    · simpa [PowerSeries.coeff_coe, hneg] using hf e.natAbs (by omega)
  simp only [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1 h2
  change _ = (f b).coeff e
  rw [h1, h2]
  exact congrArg (fun z : Series k => z.coeff e) (RingHom.congr_fun hnode (quotientMap k 1 p))

private lemma evaluation_family (n : ℕ) (v : ChartField k →+* Series k)
    (hv : IsEvaluation k 1 n v) :
    v.comp (chartToField k) = (familyToSeries k).comp (familyMap k n) := by
  apply RingHom.ext
  intro b
  exact (evaluation_chart k n v hv b).trans
    ((congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k)) (RingHom.congr_fun (family_coeff k n) b)).symm.trans
      (familyToSeries_of k (family k n b)).symm)


private lemma evaluation_point {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (n : ℕ) (v : ChartField k →+* Series k) (hv : IsEvaluation k 1 n v) :
    Spec.map (CommRingCat.ofHom (v.comp φ)) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) =
    Spec.map (CommRingCat.ofHom (familyToSeries k)) ≫ familyPoint k M χ hχ n := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, Category.assoc, familyPoint_inclusion]
  change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom v) ≫ _ ≫ _ = _
  rw [Spec.map_comp]
  simp only [Category.assoc]
  rw [hφ]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (v.comp (chartToField k))) ≫ χ =
    Spec.map (CommRingCat.ofHom ((familyToSeries k).comp (familyMap k n))) ≫ χ
  rw [evaluation_family k n v hv]

end MultiplicationEvaluation

open CategoryTheory AlgebraicGeometry MultiplicationEvaluation
/-- Pullback by actual multiplication is power substitution in the full faithful evaluation. -/
theorem multiplication_evaluation :
    ∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (χ : Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ArithmeticThetaKatoAnnularR0152.IsChartMap k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) χ) (φ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k) (hφ : ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M χ φ) (d : ℕ) (hd : 0 < d) (μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (hμ : ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ) (v w : ArithmeticThetaAnnularNormBridgeR0156.ChartField k →+* ArithmeticThetaAnnularNormBridgeR0156.Series k) (hv : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 v) (hw : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 d w), ∀ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), v (φ (μ g)) = w (φ g) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ χ hχ φ hφ d hd μ hμ v w hv hw g
  have hh : (v.comp φ).comp μ = w.comp φ := by
    suffices h : CommRingCat.ofHom ((v.comp φ).comp μ) = CommRingCat.ofHom (w.comp φ) from
      congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    apply (cancel_mono ((ArithmeticThetaGenericEvaluationR0140.genericScheme k M).fromSpecStalk
      (_root_.genericPoint (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)))).mp
    change Spec.map (CommRingCat.ofHom μ ≫ CommRingCat.ofHom (v.comp φ)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, ← hμ, ← Category.assoc]
    rw [evaluation_point k M χ hχ.1 φ hφ 1 v hv, Category.assoc,
      familyPoint_multiplication k h3 he M hM s hs G hG χ hχ d]
    exact (evaluation_point k M χ hχ.1 φ hφ d w hw).symm
  exact RingHom.congr_fun hh g

end ArithmeticThetaAnnularNormBridgeR0156
#print axioms ArithmeticThetaAnnularNormBridgeR0156.multiplication_evaluation
