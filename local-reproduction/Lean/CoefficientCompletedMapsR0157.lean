import CoefficientNormDescentDefinitionsR0157

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace CoefficientCompletedMapsR0157
open ArithmeticThetaAnnularTorsionPrereqR0053

section CompletionMap
variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
variable (hf : I.map f ≤ J)
include hf
private lemma power_map (n : ℕ) : (I ^ n).map f ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' hf _
private def quotMap (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Ideal.map_le_iff_le_comap.mp (power_map I J f hf n))
private def stage (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
  (quotMap I J f hf n).comp (AdicCompletion.evalₐ I n).toRingHom
private lemma stage_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (stage I J f hf n) = stage I J f hf m := by
  have hq : (Ideal.Quotient.factorPow J h).comp (quotMap I J f hf n) =
      (quotMap I J f hf m).comp (Ideal.Quotient.factorPow I h) := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  rw [stage, ← RingHom.comp_assoc, hq, RingHom.comp_assoc]
  congr 1
  ext z
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  apply Ideal.Quotient.eq.mpr
  have hh := SModEq.sub_mem.mp (a.property h)
  simpa only [smul_eq_mul, Ideal.mul_top, neg_sub] using neg_mem hh
private def completedMap : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (stage I J f hf) (fun h => stage_compat I J f hf h)
private lemma completedMap_of (a : R) :
    completedMap I J f hf (algebraMap R _ a) = algebraMap S _ (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completedMap, AdicCompletion.evalₐ_liftRingHom]
  rfl
end CompletionMap


variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable (ι : k →+* l)

private def polynomialMap : ArithmeticThetaScaledTateBridgeR0046.PolynomialChart k →+* Node l :=
  MvPolynomial.eval₂Hom ((algebraMap (PowerSeries l) (Node l)).comp (baseMap k l ι))
    (fun i => if i = 0 then ArithmeticThetaScaledTateBridgeR0046.x l 1
      else ArithmeticThetaScaledTateBridgeR0046.y l 1)

private lemma polynomialMap_relation : polynomialMap k l ι (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 := by
  have h : ArithmeticThetaScaledTateBridgeR0046.quotientMap l 1 (ArithmeticThetaScaledTateBridgeR0046.relation l 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa [polynomialMap, ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter, baseMap,
    ArithmeticThetaScaledTateBridgeR0046.x, ArithmeticThetaScaledTateBridgeR0046.y] using h

private def nodeMap : Node k →+* Node l :=
  Ideal.Quotient.lift (ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1) (polynomialMap k l ι)
    (by
      change ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 ≤ RingHom.ker (polynomialMap k l ι)
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact polynomialMap_relation k l ι)

private lemma nodeMap_base (b : PowerSeries k) :
    nodeMap k l ι (algebraMap (PowerSeries k) (Node k) b) =
      algebraMap (PowerSeries l) (Node l) (baseMap k l ι b) := by
  change polynomialMap k l ι (MvPolynomial.C b) = _
  simp [polynomialMap]

private lemma nodeMap_t : nodeMap k l ι (ArithmeticThetaScaledTateBridgeR0046.t k 1) = ArithmeticThetaScaledTateBridgeR0046.t l 1 := by
  simp [ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter, nodeMap_base, baseMap]

private lemma nodeMap_x : nodeMap k l ι (ArithmeticThetaScaledTateBridgeR0046.x k 1) = ArithmeticThetaScaledTateBridgeR0046.x l 1 := by
  change polynomialMap k l ι (MvPolynomial.X 0) = _
  simp [polynomialMap]

private lemma nodeMap_y : nodeMap k l ι (ArithmeticThetaScaledTateBridgeR0046.y k 1) = ArithmeticThetaScaledTateBridgeR0046.y l 1 := by
  change polynomialMap k l ι (MvPolynomial.X 1) = _
  simp [polynomialMap]

private lemma nodeMap_ideal : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map (nodeMap k l ι) ≤ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal l 1 := by
  rw [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton, nodeMap_t]
  rfl

private def coefficientMap : Chart k →+* Chart l :=
  completedMap (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal l 1) (nodeMap k l ι) (nodeMap_ideal k l ι)

private lemma coefficientMap_complete (a : Node k) :
    coefficientMap k l ι (complete k a) = complete l (nodeMap k l ι a) :=
  completedMap_of _ _ _ _ a

omit [CharZero k] in
private lemma parameter_eq : complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1) = tau k := by
  simp [complete, ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter, tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private lemma coefficientMap_base (b : PowerSeries k) :
    coefficientMap k l ι (base k b) = base l (baseMap k l ι b) := by
  change coefficientMap k l ι (complete k (algebraMap (PowerSeries k) (Node k) b)) = _
  rw [coefficientMap_complete, nodeMap_base]
  rfl

private lemma coefficientMap_x : coefficientMap k l ι (cx k) = cx l := by
  change coefficientMap k l ι (complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [coefficientMap_complete, nodeMap_x]
  rfl

private lemma coefficientMap_y : coefficientMap k l ι (cy k) = cy l := by
  change coefficientMap k l ι (complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [coefficientMap_complete, nodeMap_y]
  rfl

private abbrev chartIdeal : Ideal (Chart k) := Ideal.span {tau k}

private lemma approximation (n : ℕ) (z : Chart k) :
    ∃ a : Node k, z - complete k a ∈ chartIdeal k ^ n := by
  obtain ⟨p, hp⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by omega)).2.2.2.2.2.2 n z
  refine ⟨ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 p, ?_⟩
  change z - complete k _ ∈
    (Ideal.span {complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1)}) ^ n at hp
  rwa [parameter_eq] at hp

private lemma chartIdeal_eq : chartIdeal k =
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map (complete k) := by
  simp only [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span,
    Set.image_singleton, parameter_eq]

private lemma chart_eval_eq (n : ℕ) (z w : Chart k)
    (h : z - w ∈ chartIdeal k ^ n) :
    AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) n z =
      AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) n w := by
  rw [chartIdeal_eq] at h
  change z - w ∈ ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
    (algebraMap (Node k) (Chart k))) ^ n at h
  rw [← ArithmeticThetaNodeCharts.completion_eval_kernel
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Submodule.fg_span_singleton _) n] at h
  exact sub_eq_zero.mp ((map_sub _ z w).symm.trans h)

private lemma filtration_eq (n : ℕ) : filtration k n = chartIdeal k ^ n := by
  change (Ideal.span {complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1)}) ^ n = _
  rw [parameter_eq]

private lemma coefficientMap_ideal : (chartIdeal k).map (coefficientMap k l ι) = chartIdeal l := by
  change (Ideal.span {base k PowerSeries.X}).map _ = _
  rw [Ideal.map_span, Set.image_singleton, coefficientMap_base]
  simp only [baseMap, PowerSeries.map_X]
  rfl

private lemma coefficientMap_spec : IsChartMap k l ι (coefficientMap k l ι) := by
  refine ⟨coefficientMap_base k l ι, coefficientMap_x k l ι, coefficientMap_y k l ι, ?_⟩
  intro n b hb
  rw [filtration_eq] at hb ⊢
  have hh := Ideal.mem_map_of_mem (coefficientMap k l ι) hb
  rwa [Ideal.map_pow, coefficientMap_ideal] at hh

private lemma coefficientMap_unique (ρ ψ : Chart k →+* Chart l)
    (hρ : IsChartMap k l ι ρ) (hψ : IsChartMap k l ι ψ) : ρ = ψ := by
  have hnode : ρ.comp (complete k) = ψ.comp (complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      exact (hρ.1 b).trans (hψ.1 b).symm
    · intro i
      fin_cases i
      · exact hρ.2.1.trans hψ.2.1.symm
      · exact hρ.2.2.1.trans hψ.2.2.1.symm
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := approximation k n z
  have hmap (f : Chart k →+* Chart l) (hf : IsChartMap k l ι f) :
      f z - f (complete k a) ∈ chartIdeal l ^ n := by
    rw [← filtration_eq] at ha ⊢
    simpa only [map_sub] using hf.2.2.2 n _ ha
  exact (chart_eval_eq l n _ _ (hmap ρ hρ)).trans
    ((congrArg (AdicCompletion.evalₐ _ n) (RingHom.congr_fun hnode a)).trans
      (chart_eval_eq l n _ _ (hmap ψ hψ)).symm)

private def nodeAlgEquiv : Node k ≃ₐ[PowerSeries k] ArithmeticThetaNodeCharts.Node k :=
  { ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k with
    commutes' := by intro b; rfl }

private def nodeBasis : Module.Basis ℤ (PowerSeries k) (Node k) :=
  (Classical.choose (ArithmeticThetaNodeCharts.node_free_basis k)).map
    (nodeAlgEquiv k).symm.toLinearEquiv

private lemma nodeBasis_nat (n : ℕ) : nodeBasis k (n : ℤ) =
    ArithmeticThetaScaledTateBridgeR0046.x k 1 ^ n := by
  rw [nodeBasis, Module.Basis.map_apply,
    Classical.choose_spec (ArithmeticThetaNodeCharts.node_free_basis k),
    ArithmeticThetaNodeCharts.normalMonomial_nat]
  change (nodeAlgEquiv k).symm (ArithmeticThetaNodeCharts.x k ^ n) = _
  rw [map_pow]
  rfl

private lemma nodeBasis_neg (n : ℕ) : nodeBasis k (-(n : ℤ)) =
    ArithmeticThetaScaledTateBridgeR0046.y k 1 ^ n := by
  rw [nodeBasis, Module.Basis.map_apply,
    Classical.choose_spec (ArithmeticThetaNodeCharts.node_free_basis k),
    ArithmeticThetaNodeCharts.normalMonomial_neg]
  change (nodeAlgEquiv k).symm (ArithmeticThetaNodeCharts.y k ^ n) = _
  rw [map_pow]
  rfl

private lemma nodeMap_basis (i : ℤ) : nodeMap k l ι (nodeBasis k i) = nodeBasis l i := by
  cases i with
  | ofNat n =>
    change nodeMap k l ι (nodeBasis k (n : ℤ)) = nodeBasis l (n : ℤ)
    rw [nodeBasis_nat, map_pow, nodeMap_x, nodeBasis_nat]
  | negSucc n =>
    have hi : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
    rw [hi, nodeBasis_neg, map_pow, nodeMap_y, nodeBasis_neg]

private def nodeLinear : Node k →ₛₗ[baseMap k l ι] Node l where
  toFun := nodeMap k l ι
  map_add' := map_add _
  map_smul' a z := by simp [Algebra.smul_def, map_mul, nodeMap_base]

private def coefficientLinear (i : ℤ) : Node k →ₛₗ[baseMap k l ι] PowerSeries l where
  toFun a := baseMap k l ι ((nodeBasis k).coord i a)
  map_add' a b := by simp
  map_smul' a z := by simp [map_smul, map_mul]

private lemma coefficient_nodeMap (i : ℤ) (a : Node k) :
    (nodeBasis l).coord i (nodeMap k l ι a) = baseMap k l ι ((nodeBasis k).coord i a) := by
  have hh : ((nodeBasis l).coord i).comp (nodeLinear k l ι) = coefficientLinear k l ι i := by
    apply (nodeBasis k).ext
    intro j
    change (nodeBasis l).coord i (nodeMap k l ι (nodeBasis k j)) = _
    rw [nodeMap_basis]
    change (nodeBasis l).repr (nodeBasis l j) i = baseMap k l ι ((nodeBasis k).repr (nodeBasis k j) i)
    rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun hh a

private lemma node_coefficient_vanish (i : ℤ) (m n : ℕ) (hn : n < m) (a : Node k)
    (ha : a ∈ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 ^ m) :
    PowerSeries.coeff n ((nodeBasis k).coord i a) = 0 := by
  rw [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have he : ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ m * b =
      (PowerSeries.X ^ m : PowerSeries k) • b := by
    simp [Algebra.smul_def, ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter]
  rw [he, map_smul]
  exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) n hn

private lemma node_mem_of_coefficients (m : ℕ) (a : Node k)
    (ha : ∀ i n, n < m → PowerSeries.coeff n ((nodeBasis k).coord i a) = 0) :
    a ∈ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 ^ m := by
  rw [← (nodeBasis k).linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Ideal.sum_mem
  intro i hi
  have hc : PowerSeries.X ^ m ∣ (nodeBasis k).repr a i :=
    PowerSeries.X_pow_dvd_iff.mpr (ha i)
  obtain ⟨b, hb⟩ := hc
  rw [hb, ← smul_smul]
  have he : (PowerSeries.X ^ m : PowerSeries k) • (b • nodeBasis k i) =
      ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ m * (b • nodeBasis k i) := by
    simp [Algebra.smul_def, ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter]
  rw [he, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

private lemma complete_mem_reflect (m : ℕ) (a : Node k)
    (ha : complete k a ∈ chartIdeal k ^ m) :
    a ∈ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 ^ m := by
  have he := chart_eval_eq k m (complete k a) 0 (by simpa using ha)
  change Ideal.Quotient.mk _ a = 0 at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he

private def chartCoefficient (i : ℤ) (n : ℕ) (z : Chart k) : k :=
  PowerSeries.coeff n ((nodeBasis k).coord i (Classical.choose (approximation k (n+1) z)))

private lemma chartCoefficient_approx (i : ℤ) (n m : ℕ) (hn : n < m)
    (z : Chart k) (a : Node k) (ha : z - complete k a ∈ chartIdeal k ^ m) :
    chartCoefficient k i n z = PowerSeries.coeff n ((nodeBasis k).coord i a) := by
  let b := Classical.choose (approximation k (n+1) z)
  have hb : z - complete k b ∈ chartIdeal k ^ (n+1) :=
    Classical.choose_spec (approximation k (n+1) z)
  have hab : complete k (b-a) ∈ chartIdeal k ^ (n+1) := by
    rw [map_sub]
    have haa := (Ideal.pow_le_pow_right (by omega : n+1 ≤ m)) ha
    convert (chartIdeal k ^ (n+1)).sub_mem haa hb using 1; ring
  have hc := node_coefficient_vanish k i (n+1) n (by omega) (b-a)
    (complete_mem_reflect k (n+1) (b-a) hab)
  simp only [map_sub, sub_eq_zero] at hc
  exact hc

private lemma chartCoefficient_ext_zero (z : Chart k)
    (hz : ∀ i n, chartCoefficient k i n z = 0) : z = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro m
  obtain ⟨a, ha⟩ := approximation k m z
  have hamem : a ∈ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 ^ m := by
    apply node_mem_of_coefficients k m a
    intro i n hn
    rw [← chartCoefficient_approx k i n m hn z a ha, hz]
  have he := chart_eval_eq k m z (complete k a) ha
  have he0 : AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) m
      (complete k a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hamem
  exact he.trans (he0.trans (map_zero _).symm)

private lemma coefficientMap_injective : Function.Injective (coefficientMap k l ι) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply chartCoefficient_ext_zero k z
  intro i n
  obtain ⟨a, ha⟩ := approximation k (n+1) z
  have hmap : coefficientMap k l ι (z - complete k a) ∈ chartIdeal l ^ (n+1) := by
    have hh := Ideal.mem_map_of_mem (coefficientMap k l ι) ha
    rwa [Ideal.map_pow, coefficientMap_ideal] at hh
  have hamem : complete l (nodeMap k l ι a) ∈ chartIdeal l ^ (n+1) := by
    simpa only [map_sub, hz, coefficientMap_complete, zero_sub, neg_mem_iff] using hmap
  have hc := node_coefficient_vanish l i (n+1) n (by omega) (nodeMap k l ι a)
    (complete_mem_reflect l (n+1) _ hamem)
  rw [coefficient_nodeMap] at hc
  change PowerSeries.coeff n (PowerSeries.map ι ((nodeBasis k).coord i a)) = 0 at hc
  rw [PowerSeries.coeff_map] at hc
  exact (chartCoefficient_approx k i n (n+1) (by omega) z a ha).trans
    (ι.injective (hc.trans (map_zero ι).symm))

private lemma field_extension (ρ : Chart k →+* Chart l) (hρ : Function.Injective ρ) :
    ∃! E : ArithmeticThetaKatoAnnularR0152.ChartField k →+*
      ArithmeticThetaKatoAnnularR0152.ChartField l, ExtendsChart k l ρ E := by
  let : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  have ht : tau k ≠ 0 := by
    rw [← parameter_eq]
    exact (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
      (by omega)).2.2.2.2.1
  have hloc : Function.Injective (algebraMap (Chart k) (GenericChart k)) :=
    IsLocalization.injective (GenericChart k)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hcf : Function.Injective (ArithmeticThetaKatoAnnularR0152.chartToField k) :=
    (IsFractionRing.injective (GenericChart k)
      (ArithmeticThetaKatoAnnularR0152.ChartField k)).comp hloc
  let : IsDomain (Chart l) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain l 1 (by omega)).1
  have htl : tau l ≠ 0 := by
    rw [← parameter_eq]
    exact (ArithmeticThetaScaledTateBridgeR0046.completion_reductions l 1 (by omega)).2.2.2.2.1
  have hl : Function.Injective (algebraMap (Chart l) (GenericChart l)) :=
    IsLocalization.injective (GenericChart l) (powers_le_nonZeroDivisors_of_noZeroDivisors htl)
  let f := (ArithmeticThetaKatoAnnularR0152.chartToField l).comp ρ
  have hf : Function.Injective f :=
    ((IsFractionRing.injective (GenericChart l) (ArithmeticThetaKatoAnnularR0152.ChartField l)).comp hl).comp hρ
  have hunit : IsUnit (f (tau k)) := isUnit_iff_ne_zero.mpr (by
    exact fun h => ht (hf (h.trans (map_zero f).symm)))
  let g : GenericChart k →+* ArithmeticThetaKatoAnnularR0152.ChartField l :=
    IsLocalization.Away.lift (tau k) hunit
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (tau k)) g).mpr
    intro a b
    simp only [g, IsLocalization.Away.lift_eq]
    exact hloc.eq_iff.trans hf.eq_iff.symm
  let E : ArithmeticThetaKatoAnnularR0152.ChartField k →+*
      ArithmeticThetaKatoAnnularR0152.ChartField l := IsFractionRing.lift hg
  have hE : ExtendsChart k l ρ E := by
    intro a
    change E (algebraMap (GenericChart k) _ (algebraMap (Chart k) _ a)) = _
    rw [IsFractionRing.lift_algebraMap]
    exact IsLocalization.Away.lift_eq (tau k) hunit a
  refine ⟨E, hE, ?_⟩
  intro F hF
  apply IsFractionRing.ringHom_ext (A := GenericChart k)
  suffices h : F.comp (algebraMap (GenericChart k) _) = E.comp (algebraMap _ _) from
    fun a => RingHom.congr_fun h a
  apply IsLocalization.ringHom_ext (Submonoid.powers (tau k))
  apply RingHom.ext
  intro a
  exact (hF a).trans (hE a).symm

private lemma laurent_extension : ∃! ell : LaurentSeries k →+* LaurentSeries l, IsLaurentMap k l ι ell := by
  let g := (algebraMap (PowerSeries l) (LaurentSeries l)).comp (baseMap k l ι)
  have hg : Function.Injective g :=
    (IsFractionRing.injective (PowerSeries l) (LaurentSeries l)).comp
      (PowerSeries.map_injective ι ι.injective)
  let ell : LaurentSeries k →+* LaurentSeries l := IsFractionRing.lift hg
  have he : IsLaurentMap k l ι ell := fun b => IsFractionRing.lift_algebraMap hg b
  refine ⟨ell, he, ?_⟩
  intro other ho
  exact IsFractionRing.ringHom_ext (fun x => (ho x).trans (he x).symm)

end CoefficientCompletedMapsR0157

theorem coefficient_completed_maps :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) , (∃! ell : LaurentSeries k →+* LaurentSeries l, ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell) ∧ (∃! ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l, ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ ∧ Function.Injective ρ) ∧ (∀ (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l), ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ → ∃! E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField l, ArithmeticThetaCoefficientNormDescentR0157.ExtendsChart k l ρ E) := by
  intro k l _ _ _ _ ι
  refine ⟨CoefficientCompletedMapsR0157.laurent_extension k l ι, ?_, ?_⟩
  · refine ⟨CoefficientCompletedMapsR0157.coefficientMap k l ι,
      ⟨CoefficientCompletedMapsR0157.coefficientMap_spec k l ι,
        CoefficientCompletedMapsR0157.coefficientMap_injective k l ι⟩, ?_⟩
    intro ρ hρ
    exact CoefficientCompletedMapsR0157.coefficientMap_unique k l ι _ _ hρ.1
      (CoefficientCompletedMapsR0157.coefficientMap_spec k l ι)
  · intro ρ hρ
    have he := CoefficientCompletedMapsR0157.coefficientMap_unique k l ι ρ _ hρ
      (CoefficientCompletedMapsR0157.coefficientMap_spec k l ι)
    subst ρ
    exact CoefficientCompletedMapsR0157.field_extension k l _
      (CoefficientCompletedMapsR0157.coefficientMap_injective k l ι)

end ArithmeticThetaCoefficientNormDescentR0157

#print axioms ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps
