module

public import OriginInitialDefinitionsR0161

@[expose] public section

/-! Taylor expansion on the completed node, with the base parameter fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
namespace CompletedChartTaylorR0161

section Extension
variable {R S : Type*} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
variable (f : R →+* S) (hf : I.map f ≤ J)

private def stageQuot (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]; exact pow_le_pow_left' hf n))

private def stage (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
  (stageQuot I J f hf n).comp (AdicCompletion.evalₐ I n).toRingHom

omit [IsAdicComplete J S] in
private lemma stage_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (stage I J f hf n) = stage I J f hf m := by
  have hq : (Ideal.Quotient.factorPow J h).comp (stageQuot I J f hf n) =
      (stageQuot I J f hf m).comp (Ideal.Quotient.factorPow I h) := by
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

private def extend : AdicCompletion I R →+* S :=
  IsAdicComplete.liftRingHom J (stage I J f hf) (fun h => stage_compat I J f hf h)

private lemma extend_of (a : R) :
    extend I J f hf (algebraMap R _ a) = f a := by
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  rw [extend, IsAdicComplete.mk_liftRingHom]
  rfl
end Extension

variable (k : Type) [Field k] [CharZero k]

private def swap : Bivariate k →+* Bivariate k where
  toFun F := PowerSeries.mk (fun i => PowerSeries.mk (fun j =>
    PowerSeries.coeff i (PowerSeries.coeff j F)))
  map_zero' := by ext i j; simp
  map_one' := by
    ext i j
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs <;> simp_all
  map_add' F G := by ext i j; simp
  map_mul' F G := by
    ext i j
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum]
    exact Finset.sum_comm

omit [CharZero k] in
private lemma swap_coeff (F : Bivariate k) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (swap k F)) =
      PowerSeries.coeff i (PowerSeries.coeff j F) := by
  simp [swap]

private lemma swap_map (b : PowerSeries k) :
    swap k (PowerSeries.map PowerSeries.C b) = PowerSeries.C b := by
  ext i j
  simp only [swap_coeff, PowerSeries.coeff_map, PowerSeries.coeff_C]
  split_ifs <;> simp_all

private lemma swap_C (b : PowerSeries k) :
    swap k (PowerSeries.C b) = PowerSeries.map PowerSeries.C b := by
  ext i j
  simp only [swap_coeff, PowerSeries.coeff_map, PowerSeries.coeff_C]
  split_ifs <;> simp_all

private lemma swap_X : swap k PowerSeries.X = PowerSeries.C PowerSeries.X := by
  ext i j
  simp only [swap_coeff, PowerSeries.coeff_X, PowerSeries.coeff_C]
  split_ifs <;> simp_all [PowerSeries.coeff_X]

private def zi : PowerSeries k := PowerSeries.invOfUnit (1 + PowerSeries.X) 1
omit [CharZero k] in
private lemma zi_mul : (1 + PowerSeries.X) * zi k = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

private lemma swap_C_zi : swap k (PowerSeries.C (zi k)) = zInverse k := by
  have ha : (1 + PowerSeries.X) * swap k (PowerSeries.C (zi k)) = 1 := by
    have hh := congrArg (fun b : PowerSeries k => swap k (PowerSeries.C b)) (zi_mul k)
    simpa only [map_mul, map_add, map_one, swap_C, PowerSeries.map_X] using hh
  have hb : (1 + PowerSeries.X) * zInverse k = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  calc
    swap k (PowerSeries.C (zi k)) = swap k (PowerSeries.C (zi k)) *
        ((1 + PowerSeries.X) * zInverse k) := by rw [hb, mul_one]
    _ = zInverse k := by rw [← mul_assoc, mul_comm _ (1 + PowerSeries.X), ha, one_mul]

private def polynomialMap : ArithmeticThetaScaledTateBridgeR0046.PolynomialChart k →+* Bivariate k :=
  MvPolynomial.eval₂Hom (PowerSeries.map PowerSeries.C)
    (fun i => if i = 0 then PowerSeries.C (1 + PowerSeries.X)
      else PowerSeries.X * PowerSeries.C (zi k))

private lemma polynomialMap_relation :
    polynomialMap k (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 := by
  simp only [polynomialMap, ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one,
    map_sub, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    PowerSeries.map_X]
  norm_num only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  rw [mul_left_comm, ← map_mul, zi_mul, map_one, mul_one, sub_self]

private def nodeMap : ArithmeticThetaAnnularTorsionPrereqR0053.Node k →+* Bivariate k :=
  Ideal.Quotient.lift (ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1)
    (polynomialMap k) (by
      change ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 ≤ RingHom.ker (polynomialMap k)
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact polynomialMap_relation k)

private lemma nodeMap_base (b : PowerSeries k) :
    nodeMap k (algebraMap (PowerSeries k) _ b) = PowerSeries.map PowerSeries.C b := by
  change polynomialMap k (MvPolynomial.C b) = _
  simp [polynomialMap]

private lemma nodeMap_t : nodeMap k (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
    PowerSeries.X := by
  simp [ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter, nodeMap_base]

private lemma nodeMap_ideal :
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map (nodeMap k) ≤
      Ideal.span {PowerSeries.X} := by
  rw [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span,
    Set.image_singleton, nodeMap_t]

private def taylor : Chart k →+* Bivariate k :=
  (swap k).comp (extend (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (Ideal.span {PowerSeries.X}) (nodeMap k) (nodeMap_ideal k))

private lemma taylor_complete (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    taylor k (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) = swap k (nodeMap k a) := by
  change swap k (extend _ _ _ _ (algebraMap _ _ a)) = _
  rw [extend_of]

private lemma taylor_base (b : PowerSeries k) :
    taylor k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = PowerSeries.C b := by
  change taylor k (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (algebraMap (PowerSeries k) _ b)) = _
  rw [taylor_complete, nodeMap_base, swap_map]

private lemma taylor_x :
    taylor k (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = 1 + PowerSeries.X := by
  rw [show ArithmeticThetaAnnularTorsionPrereqR0053.cx k =
    ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      (ArithmeticThetaScaledTateBridgeR0046.x k 1) from rfl, taylor_complete]
  change swap k (polynomialMap k (MvPolynomial.X 0)) = _
  simp [polynomialMap, swap_C]

private lemma taylor_y :
    taylor k (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      PowerSeries.C PowerSeries.X * zInverse k := by
  rw [show ArithmeticThetaAnnularTorsionPrereqR0053.cy k =
    ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      (ArithmeticThetaScaledTateBridgeR0046.y k 1) from rfl, taylor_complete]
  change swap k (polynomialMap k (MvPolynomial.X 1)) = _
  simp only [polynomialMap, MvPolynomial.eval₂Hom_X', show (1 : Fin 2) ≠ 0 from by decide,
    ite_false, map_mul, swap_X, swap_C_zi]

omit [CharZero k] in
private lemma parameter_eq :
    ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X := by
  simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.base,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

/-- Fixing the base coefficients already forces the required filtration bound. -/
private lemma filtered (f : Chart k →+* Bivariate k)
    (hf : ∀ b, f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = PowerSeries.C b)
    (n : ℕ) (b : Chart k) (hb : b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n)
    (i : ℕ) : PowerSeries.coeff i (f b) ∈
      (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) ^ n := by
  change b ∈ (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1}) ^ n at hb
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨a, rfl⟩ := hb
  rw [map_mul, map_pow, parameter_eq, hf, ← map_pow, PowerSeries.coeff_C_mul]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

private lemma taylor_spec : IsChartTaylor k (taylor k) :=
  ⟨taylor_base k, taylor_x k, taylor_y k, filtered k _ (taylor_base k)⟩

private lemma unique (f g : Chart k →+* Bivariate k)
    (hf : IsChartTaylor k f) (hg : IsChartTaylor k g) : f = g := by
  have hfg : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      exact (hf.1 b).trans (hg.1 b).symm
    · intro i
      fin_cases i
      · exact hf.2.1.trans hg.2.1.symm
      · exact hf.2.2.1.trans hg.2.2.1.symm
  apply RingHom.ext
  intro z
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  obtain ⟨a, ha⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by decide)).2.2.2.2.2.2 (j+1) z
  let a' := ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 a
  have hap : z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a' ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (j+1) := ha
  have hcoeff (q : Chart k →+* Bivariate k) (hq : IsChartTaylor k q) :
      PowerSeries.coeff j (PowerSeries.coeff i (q z)) =
        PowerSeries.coeff j (PowerSeries.coeff i
          (q (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a'))) := by
    have hh := hq.2.2.2 (j+1) _ hap i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hh
    have hz := PowerSeries.X_pow_dvd_iff.mp hh j (Nat.lt_succ_self j)
    simpa only [map_sub, sub_eq_zero] using hz
  rw [hcoeff f hf, hcoeff g hg]
  exact congrArg (fun b : Bivariate k => PowerSeries.coeff j (PowerSeries.coeff i b))
    (RingHom.congr_fun hfg a')

end CompletedChartTaylorR0161

/-- The actual completed node admits exactly one Taylor map with the specified
base action, coordinates, and coefficientwise base-adic continuity. -/
theorem completed_chart_taylor :
    ∀ (k : Type) [Field k] [CharZero k],
      ∃! σ : Chart k →+* Bivariate k, IsChartTaylor k σ := by
  intro k _ _
  exact ⟨CompletedChartTaylorR0161.taylor k, CompletedChartTaylorR0161.taylor_spec k,
    fun σ hσ => CompletedChartTaylorR0161.unique k σ _ hσ
      (CompletedChartTaylorR0161.taylor_spec k)⟩

end ArithmeticThetaOriginInitialR0161

#print axioms ArithmeticThetaOriginInitialR0161.completed_chart_taylor
