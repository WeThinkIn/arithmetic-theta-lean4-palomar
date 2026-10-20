module

public import InfinitesimalPolygonDefinitionsR0129

@[expose] public section

/-! Finite quotients of the actual node completion and coordinate completions. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129

private lemma completion_eval_kernel {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I m).toRingHom =
      (I.map (algebraMap S (AdicCompletion I S))) ^ m := by
  ext w
  have hi : Function.Injective (Ideal.Quotient.factor
      (show I ^ m • (⊤ : Ideal S) ≤ I ^ m by simp)) := by
    have he : I ^ m • (⊤ : Ideal S) = I ^ m := by simp
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      using Ideal.map_mk_eq_bot_of_le (le_of_eq he.symm)
  rw [← Ideal.map_pow]
  change AdicCompletion.evalₐ I m w = 0 ↔
    w ∈ (Ideal.map (algebraMap S (AdicCompletion I S)) (I ^ m)).restrictScalars S
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI,
    LinearMap.mem_ker]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I w (by simp)]
  exact map_eq_zero_iff _ hi

private def completionQuotient {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) :
    (AdicCompletion I S ⧸ (I.map (algebraMap S (AdicCompletion I S))) ^ m) ≃+*
      S ⧸ I ^ m :=
  (Ideal.quotEquivOfEq (completion_eval_kernel I hI m).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ I m))

private lemma completionQuotient_mk {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) (z : AdicCompletion I S) :
    completionQuotient I hI m (Ideal.Quotient.mk _ z) = AdicCompletion.evalₐ I m z := by
  rfl

private lemma completionQuotient_of {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) (s : S) :
    completionQuotient I hI m (Ideal.Quotient.mk _ (algebraMap S _ s)) =
      Ideal.Quotient.mk _ s := by
  rw [completionQuotient_mk, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simp

private lemma completion_approx {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) (z : AdicCompletion I S) :
    ∃ s : S, z - algebraMap S _ s ∈ (I.map (algebraMap S (AdicCompletion I S))) ^ m := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I m z)
  refine ⟨s, ?_⟩
  rw [← completion_eval_kernel I hI m]
  change AdicCompletion.evalₐ I m (z - algebraMap S _ s) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simpa using sub_eq_zero.mpr hs.symm

open ArithmeticThetaIndexedOverlapsR0058
variable (k : Type u) [Field k] [CharZero k]

private abbrev sourceIdeal := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1
private abbrev sourceParameter := ArithmeticThetaScaledTateBridgeR0046.t k 1

omit [CharZero k] in
private lemma nodeEquiv_parameter : nodeEquiv k (sourceParameter k) =
    ArithmeticThetaNodeCharts.t k := by
  simp [nodeEquiv, sourceParameter, ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter, ArithmeticThetaNodeCharts.t,
    ArithmeticThetaNodeCharts.parameter]

omit [CharZero k] in
private lemma tau_eq : ArithmeticThetaAnnularTorsionPrereqR0053.tau k =
    algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Hat k)
      (sourceParameter k) := by
  simp [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
    ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap, sourceParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaScaledTateBridgeR0046.toCompleted]

omit [CharZero k] in
private lemma ot_eq (side : Bool) : ot k 0 side = openParameter k side := by
  change algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side)
    (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
  have h : ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X =
      sourceParameter k := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase, sourceParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter]
  rw [h, nodeEquiv_parameter]
  rfl

omit [CharZero k] in
private lemma node_ideal_eq :
    (sourceIdeal k).map (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k)
      (Hat k)) = Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k} := by
  rw [tau_eq]
  simp [sourceIdeal, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
    sourceParameter, Ideal.map_span]

private def nodeComparison (n : ℕ) : HatA k n ≃+* A k n :=
  (Ideal.quotEquivOfEq (congrArg (fun I => I ^ (n+1)) (node_ideal_eq k).symm)).trans
    ((completionQuotient (sourceIdeal k) (Submodule.fg_span (Set.finite_singleton _)) (n+1)).trans
    (Ideal.quotientEquiv _ _ (nodeEquiv k) (by
      rw [Ideal.map_pow]
      simp [sourceIdeal, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
        Ideal.map_span, nodeEquiv_parameter])))

set_option backward.isDefEq.respectTransparency true in
private def openComparison (n : ℕ) (side : Bool) : HatB k n side ≃+* B k n side :=
  (Ideal.quotEquivOfEq (show
      (Ideal.span {completeOpen k 0 side (openParameter k side)}) ^ (n+1) =
      ((openIdeal k 0 side).map (algebraMap (RawOpen k side) (HatOpen k side))) ^ (n+1) by
    simp [openIdeal, Ideal.map_span, ot_eq, completeOpen])).trans
    ((completionQuotient (openIdeal k 0 side)
      (Submodule.fg_span (Set.finite_singleton _)) (n+1)).trans
    (Ideal.quotEquivOfEq (by simp [openIdeal, ot_eq])))

omit [CharZero k] in
private lemma nodeComparison_of (n : ℕ) (s : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    nodeComparison k n (trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k s)) =
    trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
      (nodeEquiv k s) := by
  simp only [nodeComparison, RingEquiv.trans_apply, trunc, Ideal.quotEquivOfEq_mk]
  rw [show ArithmeticThetaAnnularTorsionPrereqR0053.complete k s = algebraMap _ _ s by rfl,
    completionQuotient_of]
  rfl

omit [CharZero k] in
private lemma openComparison_of (n : ℕ) (side : Bool) (s : RawOpen k side) :
    openComparison k n side (trunc (HatOpen k side)
      (completeOpen k 0 side (openParameter k side)) n (completeOpen k 0 side s)) =
    trunc (RawOpen k side) (openParameter k side) n s := by
  simp only [openComparison, RingEquiv.trans_apply, trunc, Ideal.quotEquivOfEq_mk]
  rw [show completeOpen k 0 side s = algebraMap _ _ s by rfl, completionQuotient_of]
  rfl

/-- The actual completion maps and completed coordinate restrictions agree with
all algebraic finite stages, uniformly in the coefficient field and thickness. -/
theorem finite_stage_completion_comparison :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ n : ℕ,
      ∃ (e : HatA k n ≃+* A k n) (o : ∀ side : Bool, HatB k n side ≃+* B k n side),
        CompletionComparison k n e o := by
  intro k _ _ n
  refine ⟨nodeComparison k n, openComparison k n, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro s
    exact nodeComparison_of k n s
  · intro side
    apply RingHom.ext
    intro s
    exact openComparison_of k n side s
  · intro side z
    let f := Classical.choose (completed_coordinate_restrictions k 0 side)
    have hf : IsRestriction k 0 side f :=
      (Classical.choose_spec (completed_coordinate_restrictions k 0 side)).1
    obtain ⟨s, hs⟩ := completion_approx (sourceIdeal k)
      (Submodule.fg_span (Set.finite_singleton _))
      (n+1) z
    have hnode : trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z =
        trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n
          (ArithmeticThetaAnnularTorsionPrereqR0053.complete k s) := by
      apply Ideal.Quotient.eq.mpr
      rw [node_ideal_eq] at hs
      exact hs
    have hfil : z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k s ∈
        ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) := by
      change z - algebraMap _ _ s ∈
        (Ideal.span {algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k)
          (Hat k) (sourceParameter k)}) ^ (n+1)
      rw [← tau_eq, ← node_ideal_eq]
      exact hs
    have hopen : trunc (HatOpen k side) (completeOpen k 0 side (openParameter k side)) n
        (f z) = trunc (HatOpen k side) (completeOpen k 0 side (openParameter k side)) n
          (completeOpen k 0 side (openMap k 0 side s)) := by
      apply Ideal.Quotient.eq.mpr
      have hh := hf.2 (n+1) _ hfil
      have hfs : f (ArithmeticThetaAnnularTorsionPrereqR0053.complete k s) =
          completeOpen k 0 side (openMap k 0 side s) := RingHom.congr_fun hf.1 s
      rw [map_sub, hfs] at hh
      simpa only [hatPower, ot_eq] using hh
    change openComparison k n side (trunc _ _ n (f z)) = _
    rw [hopen, openComparison_of, hnode, nodeComparison_of]
    rfl

end ArithmeticThetaInfinitesimalPolygonR0129
