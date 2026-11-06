import KatoAnnularDefinitionsR0152
import AlgebraizedMarkedIdealSpecializationR0136
import CompletedSectionKernelsR0053

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152
namespace CompletedMarkedChartIdealR0152
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
open MarkedIdealTowerBaseChangeR0133 GlobalMarkedIdealChartsR0133

variable (k : Type u) [Field k] [CharZero k]

lemma equation_regular {r : ℕ} {hr : 0 < r} (j i : Fin r) (a : kˣ) :
    IsRegular (ArithmeticThetaKatoAnnularR0152.markedEquation k (hr := hr) j i a) := by
  have reg (side : Bool) (b : kˣ) :
      IsRegular (ArithmeticThetaAnnularTorsionPrereqR0053.sectionEquation k side (b : k)) := by
    obtain ⟨hex, hall⟩ := ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels
      k side (b : k) b.ne_zero
    obtain ⟨σ, hσ, _⟩ := hex
    exact isRegular_iff_mem_nonZeroDivisors.mpr (hall σ hσ).2.2.2
  unfold ArithmeticThetaKatoAnnularR0152.markedEquation
  apply IsRegular.mul
  · split_ifs
    · exact reg true a
    · exact isRegular_one
  · split_ifs
    · exact reg false a⁻¹
    · exact isRegular_one

omit [CharZero k] in
lemma chart_complete : IsAdicComplete
    (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}) (Chart k) := by
  have h : (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}) =
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span,
      Set.image_singleton, ArithmeticThetaAnnularTorsionPrereqR0053.complete,
      ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  rw [h]
  exact AdicCompletion.isAdicComplete_self _ (Submodule.fg_span_singleton _)

lemma ideals_eq_of_quotients {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) [IsAdicComplete I S] (J K : Ideal S)
    (h : ∀ n : ℕ, J.map (Ideal.Quotient.mk (I ^ (n+1))) =
      K.map (Ideal.Quotient.mk (I ^ (n+1)))) : J = K := by
  have le (J K : Ideal S) (h : ∀ n : ℕ,
      J.map (Ideal.Quotient.mk (I ^ (n+1))) =
      K.map (Ideal.Quotient.mk (I ^ (n+1)))) : J ≤ K := by
    intro z hz
    have hsep : (⨅ n : ℕ, I ^ n • (⊤ : Submodule S (S ⧸ K))) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I (IsAdicComplete.le_jacobson_bot I)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hm : Ideal.Quotient.mk K z ∈
        (⨅ n : ℕ, I ^ n • (⊤ : Submodule S (S ⧸ K))) := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n =>
        have hz' : Ideal.Quotient.mk (I ^ (n+1)) z ∈
            K.map (Ideal.Quotient.mk (I ^ (n+1))) := h n ▸ Ideal.mem_map_of_mem _ hz
        obtain ⟨w, hw, he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz'
        have hd : z - w ∈ I ^ (n+1) := Ideal.Quotient.eq.mp he.symm
        rw [Ideal.smul_top_eq_map]
        change Ideal.Quotient.mk K z ∈ (I ^ (n+1)).map (Ideal.Quotient.mk K)
        have : Ideal.Quotient.mk K (z-w) ∈ (I ^ (n+1)).map (Ideal.Quotient.mk K) :=
          Ideal.mem_map_of_mem _ hd
        simpa only [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hw, sub_zero] using this
    rw [hsep] at hm
    exact hm
  exact le_antisymm (le J K h) (le K J (fun n => (h n).symm))

lemma ideals_eq_of_reductions (J K : Ideal (Chart k))
    (h : ∀ n : ℕ, J.map (reduction k n) = K.map (reduction k n)) : J = K := by
  let := chart_complete k
  let : IsNoetherianRing (Chart k) :=
    (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1
  apply ideals_eq_of_quotients (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})
  intro n
  let e := Classical.choose (finite_stage_completion_comparison k n)
  have hh := congrArg (Ideal.map e.symm.toRingHom) (h n)
  have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
    ext z
    exact e.symm_apply_apply z
  change (J.map (e.toRingHom.comp (trunc _ _ n))).map e.symm.toRingHom =
    (K.map (e.toRingHom.comp (trunc _ _ n))).map e.symm.toRingHom at hh
  simpa only [Ideal.map_map, ← RingHom.comp_assoc, hc, RingHom.id_comp, trunc] using hh

lemma reduction_complete (n : ℕ) (z : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k z) := by
  have h := (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1
  exact RingHom.congr_fun h z

lemma reduction_x (n : ℕ) :
    reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n := by
  change reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_complete]
  rfl

lemma reduction_y (n : ℕ) :
    reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [reduction_complete]
  rfl

lemma reduction_base (n : ℕ) (z : PowerSeries k) :
    reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k z) =
      base k n (trunc _ PowerSeries.X n z) := by
  change reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k z)) = _
  rw [reduction_complete]
  rfl

lemma next_ne {r : ℕ} (hr : 0 < r) (h3 : 3 ≤ r) (j : Fin r) : next r hr j ≠ j := by
  intro h
  have hv : (j.val+1)%r = j.val := congrArg Fin.val h
  by_cases hj : j.val+1 < r
  · rw [Nat.mod_eq_of_lt hj] at hv
    omega
  · have hjr : j.val+1 = r := by omega
    rw [hjr, Nat.mod_self] at hv
    omega

lemma section_square {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (i : Fin r) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) (n : ℕ) :
    IsPullback (markedSection k r n hr (T.atlas n) i a)
      (baseInclusion k n) (M.inclusion n) p := by
  have outer : IsPullback (markedSection k r n hr (T.atlas n) i a ≫
      (T.atlas n).p) (baseInclusion k n) (baseInclusion k n) (p ≫ M.p) := by
    rw [SmoothMarkedSections.section_over, hp.1]
    exact IsPullback.id_horiz (baseInclusion k n)
  exact outer.of_right (hp.2 n).symm (hM.2.2.1 n).flip

lemma reduced_ideal {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (i j : Fin r) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) (n : ℕ) :
    (markedChartIdeal k M p χ).map (reduction k n) =
      specIdeal ((markedSection k r n hr (T.atlas n) i a).ker.comap ((T.atlas n).chart j)) := by
  let : IsClosedImmersion p := AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM p hp.1
  change (specIdeal (p.ker.comap χ)).map (reduction k n) = _
  rw [← specIdeal_comap, ← Scheme.IdealSheafData.comap_comp, hχ.2 n,
    Scheme.IdealSheafData.comap_comp,
    AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange (section_square k M hM i a p hp n)]

lemma finite_ideal {r : ℕ} (hr : 0 < r) (h3 : 3 ≤ r) (n : ℕ)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    (i j : Fin r) (a : kˣ) :
    specIdeal ((markedSection k r n hr D i a).ker.comap (D.chart j)) =
      Ideal.span {reduction k n (ArithmeticThetaKatoAnnularR0152.markedEquation k (hr := hr) j i a)} := by
  classical
  let : IsOpenImmersion (D.chart j) := D.chart_open j
  let : IsSeparated D.p := D.isSeparated hE
  have hs := SmoothMarkedSections.section_over k r n hr D i a
  let : IsClosedImmersion (markedSection k r n hr D i a ≫ D.p) := by
    rw [hs]
    infer_instance
  let : IsClosedImmersion (markedSection k r n hr D i a) :=
    IsClosedImmersion.of_comp _ D.p
  by_cases hj : j = i
  · subst i
    have he : (markedSection k r n hr D j a).ker.comap (D.chart j) =
        (Spec.map (CommRingCat.ofHom (markedPoint k n a))).ker :=
      comap_kernel_factor _ _ _ rfl
    rw [he]
    change Ideal.map _ _ = _
    rw [spec_kernel, (marked_cartier_equation k n a).2]
    congr 1
    congr 1
    simp only [ArithmeticThetaKatoAnnularR0152.markedEquation, ite_true,
      if_neg (next_ne hr h3 j), mul_one, map_sub, reduction_x, reduction_base]
    rfl
  · by_cases hn : next r hr j = i
    · subst i
      rw [comap_kernel_factor (D.chart j) _
        (Spec.map (CommRingCat.ofHom (leftMarkedPoint k n a))) (left_factor k r n hr hE D j a)]
      change Ideal.map _ _ = _
      rw [spec_kernel, LocalMarkedPairR0133.left_kernel]
      congr 1
      congr 1
      simp only [ArithmeticThetaKatoAnnularR0152.markedEquation, if_neg hj, ite_true,
        one_mul, map_sub, reduction_y, reduction_base]
      rfl
    · rw [comap_kernel_disjoint _ _ (chart_disjoint_other k r n hr D j i (Ne.symm hj) (Ne.symm hn) a)]
      simp [specIdeal, ArithmeticThetaKatoAnnularR0152.markedEquation, hj, hn, Ideal.map_top]

end CompletedMarkedChartIdealR0152
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136

/-- The actual pullback of a marked-section kernel is generated by the prescribed
regular equation on every completed annular chart. -/
theorem completed_marked_chart_ideal :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M) (i j : Fin r) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X), IsChartMap k M j χ →
    markedChartIdeal k M p χ = Ideal.span ({markedEquation k (hr := hr) j i a} : Set (Chart k)) ∧
      IsRegular (markedEquation k (hr := hr) j i a) := by
  intro k _ _ r hr h3 T M hM i j a p hp χ hχ
  refine ⟨?_, CompletedMarkedChartIdealR0152.equation_regular k j i a⟩
  apply CompletedMarkedChartIdealR0152.ideals_eq_of_reductions k
  intro n
  rw [CompletedMarkedChartIdealR0152.reduced_ideal k M hM i j a p hp χ hχ n,
    CompletedMarkedChartIdealR0152.finite_ideal k hr h3 n (T.atlas n) (T.overlap_spec n),
    Ideal.map_span, Set.image_singleton]

end ArithmeticThetaKatoAnnularR0152
#print axioms ArithmeticThetaKatoAnnularR0152.completed_marked_chart_ideal
