import RamifiedPeriodDefinitionsR0154

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0154
namespace CompletedChartRamificationR0154
open ArithmeticThetaAnnularTorsionPrereqR0053

section CompletionMap
variable {R : Type*} [CommRing R] (I : Ideal R) (f : R →+* R)
variable (hf : I.map f ≤ I)
include hf
private lemma power_map (n : ℕ) : (I ^ n).map f ≤ I ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' hf _
private def quotMap (n : ℕ) : R ⧸ I ^ n →+* R ⧸ I ^ n :=
  Ideal.quotientMap (I ^ n) f (Ideal.map_le_iff_le_comap.mp (power_map I f hf n))
private def stage (n : ℕ) : AdicCompletion I R →+* R ⧸ I ^ n :=
  (quotMap I f hf n).comp (AdicCompletion.evalₐ I n).toRingHom
private lemma stage_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (stage I f hf n) = stage I f hf m := by
  have hq : (Ideal.Quotient.factorPow I h).comp (quotMap I f hf n) =
      (quotMap I f hf m).comp (Ideal.Quotient.factorPow I h) := by
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
private def completedMap : AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (stage I f hf) (fun h => stage_compat I f hf h)
private lemma completedMap_of (a : R) :
    completedMap I f hf (algebraMap R _ a) = algebraMap R _ (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completedMap, AdicCompletion.evalₐ_liftRingHom]
  rfl
end CompletionMap

variable (k : Type u) [Field k] [CharZero k]
variable (d : ℕ) (hd : 0 < d) (q : Fin d)

omit [CharZero k] in
private lemma node_xy : ArithmeticThetaScaledTateBridgeR0046.x k 1 * ArithmeticThetaScaledTateBridgeR0046.y k 1 = ArithmeticThetaScaledTateBridgeR0046.t k 1 := by
  have h : ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  exact sub_eq_zero.mp h

private def polynomialMap : ArithmeticThetaScaledTateBridgeR0046.PolynomialChart k →+* Node k :=
  MvPolynomial.eval₂Hom ((algebraMap (PowerSeries k) (Node k)).comp (baseMap k d hd))
    (fun i => if i = 0 then ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ q.val * ArithmeticThetaScaledTateBridgeR0046.x k 1
      else ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ (d-q.val-1) * ArithmeticThetaScaledTateBridgeR0046.y k 1)

private lemma polynomialMap_relation : polynomialMap k d hd q (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 := by
  have he : q.val + (d-q.val-1) + 1 = d := by omega
  simp only [polynomialMap, ArithmeticThetaScaledTateBridgeR0046.relation, map_sub, map_mul, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one, baseMap,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_X]
  norm_num only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  rw [map_pow]
  have ht : algebraMap (PowerSeries k) (Node k) PowerSeries.X = ArithmeticThetaScaledTateBridgeR0046.t k 1 := by simp [ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter]
  rw [ht]
  change (ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ q.val * ArithmeticThetaScaledTateBridgeR0046.x k 1) *
    (ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ (d-q.val-1) * ArithmeticThetaScaledTateBridgeR0046.y k 1) - ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ d = 0
  rw [mul_mul_mul_comm, ← pow_add, node_xy, ← pow_succ, he, sub_self]

private def nodeMap : Node k →+* Node k :=
  Ideal.Quotient.lift (ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1) (polynomialMap k d hd q)
    (by
      change ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 ≤ RingHom.ker (polynomialMap k d hd q)
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact polynomialMap_relation k d hd q)

private lemma nodeMap_base (b : PowerSeries k) :
    nodeMap k d hd q (algebraMap (PowerSeries k) (Node k) b) =
      algebraMap (PowerSeries k) (Node k) (baseMap k d hd b) := by
  change polynomialMap k d hd q (MvPolynomial.C b) = _
  simp [polynomialMap]

private lemma nodeMap_t : nodeMap k d hd q (ArithmeticThetaScaledTateBridgeR0046.t k 1) = ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ d := by
  simp only [ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one, nodeMap_base, baseMap,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_X, map_pow]

private lemma nodeMap_x : nodeMap k d hd q (ArithmeticThetaScaledTateBridgeR0046.x k 1) = ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ q.val * ArithmeticThetaScaledTateBridgeR0046.x k 1 := by
  change polynomialMap k d hd q (MvPolynomial.X 0) = _
  simp [polynomialMap]

private lemma nodeMap_y : nodeMap k d hd q (ArithmeticThetaScaledTateBridgeR0046.y k 1) = ArithmeticThetaScaledTateBridgeR0046.t k 1 ^ (d-q.val-1) * ArithmeticThetaScaledTateBridgeR0046.y k 1 := by
  change polynomialMap k d hd q (MvPolynomial.X 1) = _
  simp [polynomialMap]

private lemma nodeMap_ideal : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map (nodeMap k d hd q) ≤ ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 := by
  rw [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton, nodeMap_t, Ideal.span_le]
  intro a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  apply Ideal.mem_span_singleton.mpr
  exact dvd_pow_self _ (Nat.ne_of_gt hd)

private def ramification : Chart k →+* Chart k :=
  completedMap (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (nodeMap k d hd q) (nodeMap_ideal k d hd q)

private lemma ramification_complete (a : Node k) :
    ramification k d hd q (complete k a) = complete k (nodeMap k d hd q a) :=
  completedMap_of _ _ _ a

omit [CharZero k] in
private lemma parameter_eq : complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1) = tau k := by
  simp [complete, ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter, tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private lemma ramification_spec : IsChartRamification k d hd q (ramification k d hd q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    change ramification k d hd q (complete k (algebraMap (PowerSeries k) (Node k) b)) = _
    rw [ramification_complete, nodeMap_base]
    rfl
  · change ramification k d hd q (complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
    rw [ramification_complete, nodeMap_x, map_mul, map_pow, parameter_eq]
    rfl
  · change ramification k d hd q (complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
    rw [ramification_complete, nodeMap_y, map_mul, map_pow, parameter_eq]
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

omit [CharZero k] in
private lemma chart_map_ideal (ρ : Chart k →+* Chart k)
    (hρ : IsChartRamification k d hd q ρ) : (chartIdeal k).map ρ ≤ chartIdeal k := by
  have ht : ρ (tau k) = tau k ^ d := by
    have h := hρ.1 PowerSeries.X
    simp only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      PowerSeries.expand_X, map_pow] at h
    exact h
  rw [Ideal.map_span, Set.image_singleton, ht]
  apply Ideal.span_le.mpr
  rintro a (rfl : a = tau k ^ d)
  exact Ideal.mem_span_singleton.mpr (dvd_pow_self _ (Nat.ne_of_gt hd))

private lemma ramification_unique (ρ ψ : Chart k →+* Chart k)
    (hρ : IsChartRamification k d hd q ρ) (hψ : IsChartRamification k d hd q ψ) :
    ρ = ψ := by
  have hnode : ρ.comp (complete k) = ψ.comp (complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      exact (hρ.1 b).trans (hψ.1 b).symm
    · intro i
      fin_cases i
      · exact hρ.2.1.trans hψ.2.1.symm
      · exact hρ.2.2.trans hψ.2.2.symm
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := approximation k n z
  have hmap (f : Chart k →+* Chart k) (hf : IsChartRamification k d hd q f) :
      f z - f (complete k a) ∈ chartIdeal k ^ n := by
    have hh := Ideal.mem_map_of_mem f ha
    rw [Ideal.map_pow, map_sub] at hh
    exact (pow_le_pow_left' (chart_map_ideal k d hd q f hf) n) hh
  exact (chart_eval_eq k n _ _ (hmap ρ hρ)).trans
    ((congrArg (AdicCompletion.evalₐ _ n) (RingHom.congr_fun hnode a)).trans
      (chart_eval_eq k n _ _ (hmap ψ hψ)).symm)

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

private def weight (i : ℤ) : ℕ := if 0 ≤ i then q.val * i.toNat else (d-q.val-1)*(-i).toNat

private lemma nodeMap_basis (i : ℤ) :
    nodeMap k d hd q (nodeBasis k i) =
      (PowerSeries.X ^ weight d q i : PowerSeries k) • nodeBasis k i := by
  cases i with
  | ofNat n =>
    change nodeMap k d hd q (nodeBasis k (n : ℤ)) =
      (PowerSeries.X ^ weight d q (n : ℤ) : PowerSeries k) • nodeBasis k (n : ℤ)
    rw [nodeBasis_nat, map_pow, nodeMap_x, mul_pow]
    simp only [weight, Int.natCast_nonneg, if_true, Int.toNat_natCast,
      Algebra.smul_def, map_pow, pow_mul]
    simp [ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter]
  | negSucc n =>
    have hi : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
    rw [hi, nodeBasis_neg, map_pow, nodeMap_y, mul_pow]
    simp only [weight, show ¬ (0 : ℤ) ≤ -((n+1 : ℕ) : ℤ) by omega, if_false,
      neg_neg, Int.toNat_natCast, Algebra.smul_def, map_pow, pow_mul]
    simp [ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter]

private def nodeLinear : Node k →ₛₗ[baseMap k d hd] Node k where
  toFun := nodeMap k d hd q
  map_add' := map_add _
  map_smul' a z := by simp [Algebra.smul_def, map_mul, nodeMap_base]

private def coefficientLinear (i : ℤ) : Node k →ₛₗ[baseMap k d hd] PowerSeries k where
  toFun a := baseMap k d hd ((nodeBasis k).coord i a) * PowerSeries.X ^ weight d q i
  map_add' a b := by simp [map_add, add_mul]
  map_smul' a z := by simp [map_smul, map_mul, mul_assoc]

private lemma coefficient_nodeMap (i : ℤ) (a : Node k) :
    (nodeBasis k).coord i (nodeMap k d hd q a) =
      baseMap k d hd ((nodeBasis k).coord i a) * PowerSeries.X ^ weight d q i := by
  have hh : ((nodeBasis k).coord i).comp (nodeLinear k d hd q) =
      coefficientLinear k d hd q i := by
    apply (nodeBasis k).ext
    intro j
    change (nodeBasis k).coord i (nodeMap k d hd q (nodeBasis k j)) = _
    rw [nodeMap_basis, map_smul]
    change PowerSeries.X ^ weight d q j * (nodeBasis k).repr (nodeBasis k j) i =
      baseMap k d hd ((nodeBasis k).repr (nodeBasis k j) i) * PowerSeries.X ^ weight d q i
    rw [Module.Basis.repr_self_apply]
    by_cases h : j = i
    · subst j; simp
    · simp [h]
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

private lemma ramification_injective : Function.Injective (ramification k d hd q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply chartCoefficient_ext_zero k z
  intro i n
  let m := d*n + weight d q i + 1
  have hnm : n < m := by
    have hdn : n ≤ d*n := by nlinarith
    dsimp [m]; omega
  obtain ⟨a, ha⟩ := approximation k m z
  have hmap : (ramification k d hd q) (z-complete k a) ∈ chartIdeal k ^ m := by
    have hh := Ideal.mem_map_of_mem (ramification k d hd q) ha
    rw [Ideal.map_pow] at hh
    exact (pow_le_pow_left' (chart_map_ideal k d hd q _ (ramification_spec k d hd q)) m) hh
  have hamem : complete k (nodeMap k d hd q a) ∈ chartIdeal k ^ m := by
    simpa only [map_sub, hz, ramification_complete, zero_sub, neg_mem_iff] using hmap
  have hc := node_coefficient_vanish k i m (d*n + weight d q i) (by dsimp [m]; omega)
    (nodeMap k d hd q a) (complete_mem_reflect k m _ hamem)
  rw [coefficient_nodeMap, PowerSeries.coeff_mul_X_pow] at hc
  change PowerSeries.coeff (d*n) (PowerSeries.expand d (Nat.ne_of_gt hd)
    ((nodeBasis k).coord i a)) = 0 at hc
  rw [PowerSeries.coeff_expand_mul] at hc
  exact (chartCoefficient_approx k i n m hnm z a ha).trans hc

private lemma field_extension (ρ : Chart k →+* Chart k) (hρ : Function.Injective ρ) :
    ∃! E : ArithmeticThetaKatoAnnularR0152.ChartField k →+*
      ArithmeticThetaKatoAnnularR0152.ChartField k, ExtendsChart k ρ E := by
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
  let f := (ArithmeticThetaKatoAnnularR0152.chartToField k).comp ρ
  have hf : Function.Injective f := hcf.comp hρ
  have hunit : IsUnit (f (tau k)) := isUnit_iff_ne_zero.mpr (by
    exact fun h => ht (hf (h.trans (map_zero f).symm)))
  let g : GenericChart k →+* ArithmeticThetaKatoAnnularR0152.ChartField k :=
    IsLocalization.Away.lift (tau k) hunit
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (tau k)) g).mpr
    intro a b
    simp only [g, IsLocalization.Away.lift_eq]
    exact hloc.eq_iff.trans hf.eq_iff.symm
  let E : ArithmeticThetaKatoAnnularR0152.ChartField k →+*
      ArithmeticThetaKatoAnnularR0152.ChartField k := IsFractionRing.lift hg
  have hE : ExtendsChart k ρ E := by
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

end CompletedChartRamificationR0154

/-- The completed node pullback for every refined chart, with its unique
fraction-field extension. The full coefficient-ring action is part of the specification. -/
theorem completed_chart_ramification :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d) (q : Fin d),
      ∃! ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k,
        IsChartRamification k d hd q ρ ∧ Function.Injective ρ ∧
          (∃! E : ArithmeticThetaKatoAnnularR0152.ChartField k →+*
            ArithmeticThetaKatoAnnularR0152.ChartField k, ExtendsChart k ρ E) := by
  intro k _ _ d hd q
  refine ⟨CompletedChartRamificationR0154.ramification k d hd q, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact CompletedChartRamificationR0154.ramification_spec k d hd q
  · exact CompletedChartRamificationR0154.ramification_injective k d hd q
  · exact CompletedChartRamificationR0154.field_extension k _
      (CompletedChartRamificationR0154.ramification_injective k d hd q)
  · intro ρ hρ
    exact CompletedChartRamificationR0154.ramification_unique k d hd q _ _ hρ.1
      (CompletedChartRamificationR0154.ramification_spec k d hd q)

end ArithmeticThetaRamifiedPeriodR0154

#print axioms ArithmeticThetaRamifiedPeriodR0154.completed_chart_ramification
