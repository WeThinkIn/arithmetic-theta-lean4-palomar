module

public import ConservativeKernelDefinitionsR0189

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaConservativeKernelR0189
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaSectionCompletion

namespace LiftedCuspCompletionR0189

/-- A local map carrying a uniformizer to a uniformizer and surjecting on
residues induces the required equivalence on completions. -/
private lemma completion_of_uniformizer
    {A : Type} [CommRing A] [IsLocalRing A]
    (k : Type) [Field k] (σ : A →+* PowerSeries k) [IsLocalHom σ]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (hσ : IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {σ π})
    (hres : ∀ w : PowerSeries k, ∃ a : A,
      w - σ a ∈ IsLocalRing.maximalIdeal (PowerSeries k)) :
    ∃ e : completedLocalRing A ≃+* PowerSeries k,
      ∀ a, e (algebraMap A (completedLocalRing A) a) = σ a := by
  have hσ0 : σ π ≠ 0 := by
    intro hz
    rw [hz, Ideal.span_singleton_zero] at hσ
    exact IsDiscreteValuationRing.not_a_field (PowerSeries k) hσ
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfiltered (n : ℕ) : IsLocalRing.maximalIdeal A ^ n ≤
      (IsLocalRing.maximalIdeal (PowerSeries k) ^ n).comap σ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le σ) n
  obtain ⟨e, he⟩ :=
    AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal (PowerSeries k)) σ
      (by
        intro n w
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
        obtain ⟨a, ha⟩ := CompletedLocalParameter.approximate_mod_pow σ π hσ hres n w
        exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩)
      (by
        intro n
        ext a
        change (Ideal.Quotient.mk _ (σ a) = 0) ↔ _
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact ⟨CompletedLocalParameter.mem_pow_of_map_mem_pow σ π hπ hσ hσ0 n a,
          fun ha => hfiltered n ha⟩)
  refine ⟨e.trans (AdicCompletion.ofAlgEquiv
    (IsLocalRing.maximalIdeal (PowerSeries k))).symm.toRingEquiv, ?_⟩
  intro a
  change (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal (PowerSeries k))).symm
    (e (algebraMap _ _ a)) = _
  rw [he]
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

end LiftedCuspCompletionR0189

/-- Lifting the actual full-level disk preserves its completed local parameter. -/
theorem lifted_cusp_completion :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ),
    3 ≤ L → Even L → ∀ (D : LevelData k L) (X : Compactification k L D)
      (V : DiskTest k L D X) (b : ℕ)
      (R : RootCover k (Component k L D X (V.disk (closedPoint k)))
        (projection k L D X (V.disk (closedPoint k))) b)
      (g : Disk k ⟶ R.space),
    g ≫ (R.map ≫ inclusion k L D X (V.disk (closedPoint k))) = V.disk →
    IsDominant (genericInclusion k ≫ g) →
    Order.coheight (g (closedPoint k)) = 1 ∧
      ∃ e : completedLocalRing (R.space.presheaf.stalk (g (closedPoint k))) ≃+* PowerSeries k,
        CompatibleCompletion k R.space g e := by
  intro k _ _ _ L hL heven D X V b R g hg _
  let p := R.map ≫ inclusion k L D X (V.disk (closedPoint k))
  have hp : g ≫ p = V.disk := hg
  have hd : Extends k L D X V.base (g ≫ p) := by rw [hp]; exact V.extends_eq
  have hc := tate_completed_local_parameter k L hL heven D V.level X V.base
    ⟨V.map, V.classifies⟩ (g ≫ p) hd
  obtain ⟨π, hπ, hπimage⟩ :=
    (CompletedLocalParameter.isCompletedParameter_iff_uniformizer k L D X V.base
      (g ≫ p) hd).mp hc
  let σ : R.space.presheaf.stalk (g (closedPoint k)) →+* PowerSeries k :=
    (Scheme.stalkClosedPointTo g).hom
  letI : IsLocalHom σ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo g).hom)
  let τ : CuspStalk k L D X (g ≫ p) →+*
      R.space.presheaf.stalk (g (closedPoint k)) := (p.stalkMap (g (closedPoint k))).hom
  have hcomp : CompletedLocalParameter.localMap k L D X (g ≫ p) = σ.comp τ := by
    unfold CompletedLocalParameter.localMap
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have himage : IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {σ (τ π)} := by
    simpa only [hcomp, RingHom.comp_apply] using hπimage
  have hirrImage : Irreducible (σ (τ π)) := by
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr himage
  have hirr : Irreducible (τ π) := hirrImage.of_map
  letI := R.integral
  letI := R.smooth
  have hne : g (closedPoint k) ≠ genericPoint R.space := by
    intro heq
    have h : ∃ a : R.space.presheaf.stalk (g (closedPoint k)), Irreducible a := ⟨τ π, hirr⟩
    rw [heq] at h
    obtain ⟨a, ha⟩ := h
    exact ha.not_isUnit (isUnit_iff_ne_zero.mpr ha.ne_zero)
  have hco := ArithmeticThetaGeometricNormR0150.NormOrders.smooth_coheight_one_of_ne_generic
    k (R.map ≫ projection k L D X (V.disk (closedPoint k))) _ hne
  have hclosed := ArithmeticThetaGeometricNormR0150.NormOrders.smooth_closed_of_ne_generic
    k (R.map ≫ projection k L D X (V.disk (closedPoint k))) _ hne
  obtain ⟨hdom, hdvr⟩ := BoundaryGeometry.dvr_of_closed
    (R.map ≫ projection k L D X (V.disk (closedPoint k))) _ hclosed
  letI := hdom
  letI := hdvr
  have hres : ∀ w : PowerSeries k, ∃ a : R.space.presheaf.stalk (g (closedPoint k)),
      w - σ a ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    intro w
    obtain ⟨a, ha⟩ := CompletedLocalParameter.localMap_residue_surjective
      k L D X (g ≫ p) hd.1 w
    exact ⟨τ a, by simpa only [hcomp, RingHom.comp_apply] using ha⟩
  obtain ⟨e, he⟩ := LiftedCuspCompletionR0189.completion_of_uniformizer k σ (τ π)
    hirr.maximalIdeal_eq himage hres
  refine ⟨hco, e, ?_⟩
  have heσ : completionExpansion (R.space.presheaf.stalk (g (closedPoint k))) k e = σ :=
    RingHom.ext he
  unfold CompatibleCompletion
  rw [heσ, CompletedLocalParameter.diskGerm_eq]
  change ((g.stalkMap (closedPoint k) ≫
    (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).hom) ≫
      (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).inv).hom = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

#print axioms lifted_cusp_completion
end ArithmeticThetaConservativeKernelR0189
