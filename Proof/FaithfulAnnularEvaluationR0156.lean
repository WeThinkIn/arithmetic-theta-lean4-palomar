module

public import AnnularNormBridgeDefinitionsR0156

@[expose] public section

/-! Faithful evaluation of the completed annulus at a transcendental coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace FaithfulAnnularEvaluation
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

variable (k : Type) [Field k] [CharZero k] (a : kˣ) (n : ℕ)

private lemma coordinate_ne_zero : coordinate k a n ≠ 0 := by
  apply mul_ne_zero
  · exact (map_ne_zero (coefficientMap k)).mpr a.ne_zero
  · apply pow_ne_zero
    simpa [ArithmeticThetaLaurentNormR0064.w] using
      (IsFractionRing.injective (LaurentPolynomial k) (Coeff k)).ne
        (LaurentPolynomial.isUnit_T (1 : ℤ) (R := k)).ne_zero

private def nodeEvaluation : Node k 1 →+* PowerSeries (Coeff k) :=
  Ideal.Quotient.lift (relationIdeal k 1)
    (MvPolynomial.eval₂Hom (PowerSeries.map (coefficientMap k))
      (fun i => if i = (0 : Fin 2) then PowerSeries.C (coordinate k a n)
        else PowerSeries.C (coordinate k a n)⁻¹ * PowerSeries.X)) (by
    change relationIdeal k 1 ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    simp [relation, parameter, ← mul_assoc, ← map_mul, coordinate_ne_zero k a n])

private lemma nodeEvaluation_base (b : PowerSeries k) :
    nodeEvaluation k a n (algebraMap (PowerSeries k) (Node k 1) b) =
      PowerSeries.map (coefficientMap k) b := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C b) = _
  simp

private lemma nodeEvaluation_x : nodeEvaluation k a n (x k 1) =
    PowerSeries.C (coordinate k a n) := by simp [nodeEvaluation, x, quotientMap]
private lemma nodeEvaluation_y : nodeEvaluation k a n (y k 1) =
    PowerSeries.C (coordinate k a n)⁻¹ * PowerSeries.X := by
  simp [nodeEvaluation, y, quotientMap]
private lemma nodeEvaluation_t : nodeEvaluation k a n (t k 1) = PowerSeries.X := by
  rw [t, nodeEvaluation_base]
  simp [parameter]

private def targetIdeal : Ideal (PowerSeries (Coeff k)) := Ideal.span {PowerSeries.X}
private instance targetComplete : IsAdicComplete (targetIdeal k) (PowerSeries (Coeff k)) := by
  unfold targetIdeal
  infer_instance

private lemma nodeEvaluation_cont : nodeIdeal k 1 ≤ (targetIdeal k).comap (nodeEvaluation k a n) := by
  rw [nodeIdeal, Ideal.span_singleton_le_iff_mem]
  change nodeEvaluation k a n (t k 1) ∈ targetIdeal k
  rw [nodeEvaluation_t]
  exact Ideal.mem_span_singleton_self _

/-- The full map on completed charts, obtained from compatible finite quotients. -/
def chartEvaluation : Chart k →+* PowerSeries (Coeff k) :=
  extend (nodeIdeal k 1) (targetIdeal k) (nodeEvaluation k a n) (nodeEvaluation_cont k a n)

lemma chartEvaluation_of (b : Node k 1) :
    chartEvaluation k a n (toCompleted k 1 b) = nodeEvaluation k a n b :=
  extend_of _ _ _ _ _

lemma chartEvaluation_base (b : PowerSeries k) :
    chartEvaluation k a n (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      PowerSeries.map (coefficientMap k) b := by
  exact (chartEvaluation_of k a n _).trans (nodeEvaluation_base k a n b)
lemma chartEvaluation_x :
    chartEvaluation k a n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      PowerSeries.C (coordinate k a n) := by
  exact (chartEvaluation_of k a n _).trans (nodeEvaluation_x k a n)
lemma chartEvaluation_y :
    chartEvaluation k a n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      PowerSeries.C (coordinate k a n)⁻¹ * PowerSeries.X := by
  exact (chartEvaluation_of k a n _).trans (nodeEvaluation_y k a n)
lemma chartEvaluation_parameter :
    chartEvaluation k a n (completedParameter k 1) = PowerSeries.X := by
  exact (chartEvaluation_of k a n _).trans (nodeEvaluation_t k a n)

lemma chartEvaluation_filtered (N : ℕ) (b : Chart k)
    (hb : b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N) :
    chartEvaluation k a n b ∈ targetIdeal k ^ N := by
  have hgen : Ideal.span {completedParameter k 1} ≤
      (targetIdeal k).comap (chartEvaluation k a n) := by
    rw [Ideal.span_singleton_le_iff_mem]
    change chartEvaluation k a n (completedParameter k 1) ∈ targetIdeal k
    rw [chartEvaluation_parameter]
    exact Ideal.mem_span_singleton_self _
  exact ((Ideal.pow_right_mono hgen N).trans (Ideal.le_comap_pow _ N)) hb

lemma coefficientMap_eq : coefficientMap k = algebraMap k (Coeff k) := rfl

lemma coordinate_transcendental (hn : 0 < n) : Transcendental k (coordinate k a n) := by
  have hT : Transcendental k (LaurentPolynomial.T 1 : LaurentPolynomial k) := by
    have h := (transcendental_ringHom_iff_of_comp_eq (RingEquiv.refl k)
      (Polynomial.toLaurent (R := k)) Polynomial.toLaurent_injective
      (a := Polynomial.X) (by apply RingHom.ext; intro b; simp))
    simpa using h.mpr (Polynomial.transcendental_X k)
  have hw : Transcendental k (ArithmeticThetaLaurentNormR0064.w k) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective (LaurentPolynomial k) (Coeff k))).mpr hT
  have hp : Transcendental k (Polynomial.C (a : k) * Polynomial.X ^ n) := by
    apply Polynomial.transcendental
    · simpa [Polynomial.natDegree_C_mul, a.ne_zero] using hn.ne'
    · simp [mem_nonZeroDivisors_iff_ne_zero, a.ne_zero]
  simpa [coordinate, coefficientMap_eq] using hw.aeval_of_transcendental hp

open ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1
open ArithmeticThetaAnnularGeometry.CompletedNodeSupport

private def residueScalar : Resid (parameter k 1) →+* k :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
    change Ideal.span {parameter k 1} ≤ RingHom.ker _
    rw [Ideal.span_singleton_le_iff_mem]
    simp [parameter])

private lemma residueScalar_injective : Function.Injective (residueScalar k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  change PowerSeries.constantCoeff p = 0 at hb
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa [parameter, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] using hb

private def branchEvaluation : Polynomial (Resid (parameter k 1)) →+* Coeff k :=
  (Polynomial.eval₂RingHom (coefficientMap k) (coordinate k a n)).comp
    (Polynomial.mapRingHom (residueScalar k))

private lemma branchEvaluation_injective (hn : 0 < n) :
    Function.Injective (branchEvaluation k a n) := by
  have h : Function.Injective
      (Polynomial.eval₂RingHom (coefficientMap k) (coordinate k a n)) := by
    intro p q hpq
    apply (transcendental_iff_injective.mp (coordinate_transcendental k a n hn))
    simpa only [Polynomial.aeval_def, ← coefficientMap_eq, Polynomial.coe_eval₂RingHom] using hpq
  exact h.comp (Polynomial.map_injective (residueScalar k) (residueScalar_injective k))

private def nodeBranch : Node k 1 →+* Polynomial (Resid (parameter k 1)) :=
  (branchX (parameter k 1)).toRingHom

private lemma nodeBranch_kernel : RingHom.ker (nodeBranch k) = Ideal.span {y k 1} :=
  ker_branchX _

private lemma nodeBranch_cont : nodeIdeal k 1 ≤ RingHom.ker (nodeBranch k) := by
  rw [nodeBranch_kernel, nodeIdeal, Ideal.span_singleton_le_iff_mem]
  have hxy : x k 1 * y k 1 = t k 1 := xy_eq (parameter k 1)
  rw [← hxy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private def completedBranch : Chart k →+* Polynomial (Resid (parameter k 1)) :=
  residueExtension (nodeIdeal k 1) (nodeBranch k) (nodeBranch_cont k)

private lemma completedBranch_kernel :
    RingHom.ker (completedBranch k) =
      Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.cy k} := by
  rw [completedBranch, residueExtension_ker _ _ _
    (show (nodeIdeal k 1).FG from Submodule.fg_span_singleton _),
    nodeBranch_kernel, Ideal.map_span, Set.image_singleton]
  rfl

private lemma nodeEvaluation_residue (b : Node k 1) :
    PowerSeries.constantCoeff (nodeEvaluation k a n b) =
      branchEvaluation k a n (nodeBranch k b) := by
  suffices h : PowerSeries.constantCoeff.comp (nodeEvaluation k a n) =
      (branchEvaluation k a n).comp (nodeBranch k) from RingHom.congr_fun h b
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    change PowerSeries.constantCoeff ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C c)) =
      branchEvaluation k a n ((MvPolynomial.aeval ![Polynomial.X, 0]) (MvPolynomial.C c))
    simp [branchEvaluation, residueScalar, Polynomial.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      (PowerSeries.coeff_map (coefficientMap k) 0 c)
  · intro i
    simp only [RingHom.comp_apply]
    change PowerSeries.constantCoeff ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X i)) =
      branchEvaluation k a n ((MvPolynomial.aeval ![Polynomial.X, 0]) (MvPolynomial.X i))
    fin_cases i <;> simp [branchEvaluation]

private lemma completedBranch_filtered (b : Chart k)
    (hb : b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k 1) :
    completedBranch k b = 0 := by
  have hle : ArithmeticThetaAnnularTorsionPrereqR0053.filtration k 1 ≤
      RingHom.ker (completedBranch k) := by
    change (Ideal.span {completedParameter k 1}) ^ 1 ≤ _
    rw [pow_one, Ideal.span_singleton_le_iff_mem]
    change completedBranch k (toCompleted k 1 (t k 1)) = 0
    change residueExtension _ _ _ (algebraMap _ _ (t k 1)) = 0
    rw [residueExtension_of]
    exact nodeBranch_cont k (Ideal.mem_span_singleton_self _)
  exact hle hb

lemma chartEvaluation_residue (b : Chart k) :
    PowerSeries.constantCoeff (chartEvaluation k a n b) =
      branchEvaluation k a n (completedBranch k b) := by
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 1 b
  have he := chartEvaluation_filtered k a n 1 _ hp
  rw [targetIdeal, pow_one, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    map_sub, map_sub, sub_eq_zero] at he
  have hr := completedBranch_filtered k _ hp
  rw [map_sub, sub_eq_zero] at hr
  rw [he, chartEvaluation_of, nodeEvaluation_residue, hr]
  rfl

lemma chartEvaluation_injective (hn : 0 < n) : Function.Injective (chartEvaluation k a n) := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  letI : IsNoetherianRing (Chart k) := (completion_reductions k 1 (by omega)).2.1
  let y := ArithmeticThetaAnnularTorsionPrereqR0053.cy k
  let I : Ideal (Chart k) := Ideal.span {y}
  letI : Nontrivial (Resid (parameter k 1)) := (residueScalar k).domain_nontrivial
  have hproper : I ≠ ⊤ := by
    change Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.cy k} ≠ ⊤
    rw [← completedBranch_kernel]
    exact RingHom.ker_ne_top _
  letI : IsHausdorff I (Chart k) := IsHausdorff.of_isDomain I hproper
  have hy : chartEvaluation k a n y ≠ 0 := by
    rw [show y = ArithmeticThetaAnnularTorsionPrereqR0053.cy k from rfl, chartEvaluation_y]
    exact mul_ne_zero (by simpa using inv_ne_zero (coordinate_ne_zero k a n)) PowerSeries.X_ne_zero
  have hdvd (b : Chart k) (hb : chartEvaluation k a n b = 0) : y ∣ b := by
    have h := chartEvaluation_residue k a n b
    rw [hb, map_zero] at h
    have hz : completedBranch k b = 0 :=
      (branchEvaluation_injective k a n hn) (h.symm.trans (map_zero _).symm)
    have hm : b ∈ RingHom.ker (completedBranch k) := hz
    rwa [completedBranch_kernel, Ideal.mem_span_singleton] at hm
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  have hpow : ∀ N : ℕ, ∀ b : Chart k, chartEvaluation k a n b = 0 → y ^ N ∣ b := by
    intro N
    induction N with
    | zero => intro b hb; simp
    | succ N ih =>
      intro b hb
      obtain ⟨c, rfl⟩ := hdvd b hb
      have hc : chartEvaluation k a n c = 0 := by
        rw [map_mul] at hb
        exact (mul_eq_zero.mp hb).resolve_left hy
      obtain ⟨d, hd⟩ := ih c hc
      refine ⟨d, ?_⟩
      rw [hd, pow_succ]
      ring
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro N
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  change b ∈ (Ideal.span {y}) ^ N
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact hpow N b hb

/-- Extend a faithful chart map across both parameter inversion and fractions. -/
lemma field_extension (f : Chart k →+* Series k) (hf : Function.Injective f) :
    ∃ E : ChartField k →+* Series k,
      ∀ b : Chart k, E (ArithmeticThetaKatoAnnularR0152.chartToField k b) = f b := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  have ht : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
    have h := (completion_reductions k 1 (by omega)).2.2.2.2.1
    simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaScaledAnnularR0050.tau, completedBaseMap, completedParameter,
      t, parameter] using h
  have hloc : Function.Injective
      (algebraMap (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hunit : IsUnit (f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) :=
    isUnit_iff_ne_zero.mpr (fun h => ht (hf (h.trans (map_zero f).symm)))
  let g : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* Series k :=
    IsLocalization.Away.lift (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) hunit
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) g).mpr
    intro b c
    simp only [g, IsLocalization.Away.lift_eq]
    exact hloc.eq_iff.trans hf.eq_iff.symm
  refine ⟨IsFractionRing.lift hg, ?_⟩
  intro b
  change IsFractionRing.lift hg
    (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _
      (algebraMap (Chart k) _ b)) = _
  rw [IsFractionRing.lift_algebraMap]
  exact IsLocalization.Away.lift_eq _ hunit b

lemma evaluation_exists (hn : 0 < n) :
    ∃ ev : ChartField k →+* Series k, IsEvaluation k a n ev := by
  let f : Chart k →+* Series k :=
    (HahnSeries.ofPowerSeries ℤ (Coeff k)).comp (chartEvaluation k a n)
  have hf : Function.Injective f :=
    HahnSeries.ofPowerSeries_injective.comp (chartEvaluation_injective k a n hn)
  obtain ⟨E, hE⟩ := field_extension k f hf
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [hE]
    change HahnSeries.ofPowerSeries ℤ (Coeff k) (chartEvaluation k a n _) = _
    rw [chartEvaluation_base]
    rfl
  · rw [hE]
    simp [f, chartEvaluation_x]
  · rw [hE]
    simp [f, chartEvaluation_y, ArithmeticThetaLaurentNormR0064.t,
      HahnSeries.ofPowerSeries_X]
  · intro N b hb e he
    rw [hE]
    change (HahnSeries.ofPowerSeries ℤ (Coeff k) (chartEvaluation k a n b)).coeff e = 0
    have h := chartEvaluation_filtered k a n N b hb
    rw [targetIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff] at h
    by_cases hneg : e < 0
    · simp [PowerSeries.coeff_coe, hneg]
    · simpa [PowerSeries.coeff_coe, hneg] using h e.natAbs (by omega)

lemma evaluation_unique (E F : ChartField k →+* Series k)
    (hE : IsEvaluation k a n E) (hF : IsEvaluation k a n F) : E = F := by
  have hnode (b : Node k 1) :
      E (ArithmeticThetaKatoAnnularR0152.chartToField k (toCompleted k 1 b)) =
      F (ArithmeticThetaKatoAnnularR0152.chartToField k (toCompleted k 1 b)) := by
    suffices h : (E.comp (ArithmeticThetaKatoAnnularR0152.chartToField k)).comp
        (toCompleted k 1) = (F.comp (ArithmeticThetaKatoAnnularR0152.chartToField k)).comp
        (toCompleted k 1) from RingHom.congr_fun h b
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (hE.1 c).trans (hF.1 c).symm
    · intro i
      fin_cases i
      · exact hE.2.1.trans hF.2.1.symm
      · exact hE.2.2.1.trans hF.2.2.1.symm
  have hchart (b : Chart k) :
      E (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      F (ArithmeticThetaKatoAnnularR0152.chartToField k b) := by
    apply HahnSeries.ext
    funext e
    let N := (e + 1).toNat
    obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 N b
    have he : e < (N : ℤ) := by dsimp [N]; omega
    have h1 := hE.2.2.2 N _ hp e he
    have h2 := hF.2.2.2 N _ hp e he
    simp only [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1 h2
    rw [h1, h2, hnode]
  apply IsFractionRing.ringHom_ext (A := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
  suffices h : E.comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) =
      F.comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) from
    fun b => RingHom.congr_fun h b
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  apply RingHom.ext
  exact hchart

end FaithfulAnnularEvaluation

/-- The unique faithful evaluation on the full completed-annular fraction field. -/
theorem faithful_annular_evaluation :
    ∀ (k : Type) [Field k] [CharZero k] (a : kˣ) (n : ℕ) (hn : 0 < n),
      ∃! ev : ChartField k →+* Series k, IsEvaluation k a n ev ∧ Function.Injective ev := by
  intro k _ _ a n hn
  obtain ⟨E, hE⟩ := FaithfulAnnularEvaluation.evaluation_exists k a n hn
  refine ⟨E, ⟨hE, E.injective⟩, ?_⟩
  intro F hF
  exact FaithfulAnnularEvaluation.evaluation_unique k a n F E hF.1 hE

end ArithmeticThetaAnnularNormBridgeR0156

#print axioms ArithmeticThetaAnnularNormBridgeR0156.faithful_annular_evaluation
