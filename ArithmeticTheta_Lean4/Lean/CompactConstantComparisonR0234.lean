import LevelConstantsDefinitionsR0234

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaLevelConstantsR0234
namespace CompactComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179

/-- Separatedness gives uniqueness over the actual coefficient map. -/
theorem extension_unique {k l : Type} [Field k] [Field l] {L : ℕ}
    (ι : k →+* l) (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (F G : Y.space ⟶ X.space)
    (hF : Extends ι D E X Y f F) (hG : Extends ι D E X Y f G) : F = G := by
  letI := CompactifiedLevelForgetting.reduced l E Y
  letI := X.proper
  letI : IsDominant Y.inclusion := ⟨Y.dense⟩
  exact ext_of_isDominant_of_isSeparated X.projection (hF.1.trans hG.1.symm)
    Y.inclusion (hF.2.trans hG.2.symm)

/-- Extend from the fixed level compactification into any proper target over
its field. This will be applied to the base-changed compact curve. -/
theorem extend_to_proper {l : Type} [Field l] [CharZero l] {L : ℕ}
    (hL : 3 ≤ L) (heven : Even L) (E : LevelData l L)
    (Y : Compactification l L E) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of l)) [IsProper p]
    (g : OpenBase l L E ⟶ Z) (hg : g ≫ p = openStructure l L E) :
    ∃ G : Y.space ⟶ Z, G ≫ p = Y.projection ∧ Y.inclusion ≫ G = g := by
  letI := Y.openImmersion
  letI := Y.proper
  letI := CompactifiedLevelForgetting.reduced l E Y
  letI : IsLocallyNoetherian Y.space := LocallyOfFiniteType.isLocallyNoetherian Y.projection
  let U := Y.inclusion.opensRange
  let e : OpenBase l L E ≅ (U : Scheme.{0}) :=
    IsOpenImmersion.isoOfRangeEq Y.inclusion U.ι (by simp [U])
  have hei : e.inv ≫ Y.inclusion = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have heh : e.hom ≫ U.ι = Y.inclusion := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hval : ∀ x : Y.space, x ∉ U →
      (∃ _ : IsDomain (Y.space.presheaf.stalk x), IsDiscreteValuationRing (Y.space.presheaf.stalk x)) ∧
        ∃ y : Y.space, y ∈ U ∧ y ⤳ x := by
    intro x hx
    obtain ⟨_, hdom, hdvr, _⟩ := (level_boundary_geometry l L hL heven E Y).2.2 x hx
    letI := hdom
    refine ⟨⟨hdom, hdvr⟩, ?_⟩
    let η := P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.genPt x
    obtain ⟨V, hxV, hV⟩ :=
      P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.exists_opens_forall_genPt_specializes x
    obtain ⟨z, hzV, hzU⟩ := Y.dense.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨η, (hV z hzV).mem_open U.isOpen hzU,
      P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.genPt_specializes_self x⟩
  obtain ⟨G, hG, hGi⟩ :=
    exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
      Y.projection p U (e.inv ≫ g) (by
        rw [Category.assoc, hg, ← Y.over_eq, ← Category.assoc, hei]) hval
  refine ⟨G, hG, ?_⟩
  rw [← heh, Category.assoc, hGi]
  simp

/-- A proper extension of a dense open isomorphism into a smooth curve is
an isomorphism; the source may have several components. -/
theorem isIso_extension {l : Type} [Field l] {L : ℕ}
    (E : LevelData l L) (Y : Compactification l L E) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of l)) [IsProper p] [SmoothOfRelativeDimension 1 p]
    (g : OpenBase l L E ⟶ Z) [IsOpenImmersion g] (hd : DenseRange g)
    (G : Y.space ⟶ Z) (hp : G ≫ p = Y.projection) (hi : Y.inclusion ≫ G = g) :
    IsIso G := by
  letI := Y.proper
  letI := Y.openImmersion
  letI := CompactifiedLevelForgetting.reduced l E Y
  letI : IsProper (G ≫ p) := hp.symm ▸ Y.proper
  letI : IsProper G := IsProper.of_comp G p
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  letI : LocallyQuasiFinite G := LocallyQuasiFinite.of_finite_preimage_singleton G fun z => by
    have hfin := (Set.finite_singleton z).preimage g.isOpenEmbedding.injective.injOn
    apply ((hfin.image Y.inclusion.base).union (BoundaryGeometry.boundary_finite l L E Y)).subset
    intro y hy
    by_cases hyi : y ∈ Set.range Y.inclusion.base
    · obtain ⟨w, rfl⟩ := hyi
      refine Or.inl ⟨w, ?_, rfl⟩
      change g w = z
      rw [← hi]
      exact hy
    · exact Or.inr hyi
  let V := g.opensRange
  let e : OpenBase l L E ≅ (V : Scheme.{0}) :=
    IsOpenImmersion.isoOfRangeEq g V.ι (by simp [V])
  have he : e.inv ≫ g = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have hnormal : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z) := by
    let e₀ : l ≃+* Γ(Spec (CommRingCat.of l), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of l)).symm.commRingCatIsoToRingEquiv
    letI : IsDomain Γ(Spec (CommRingCat.of l), ⊤) := MulEquiv.isDomain l e₀.symm.toMulEquiv
    letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of l), ⊤) := IsIntegrallyClosed.of_equiv e₀
    exact Smooth.isDomain_and_isIntegrallyClosed_stalk p
  letI : IsOpenImmersion G :=
    isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange G
      hnormal V hd (e.inv ≫ Y.inclusion) (by rw [Category.assoc, hi, he])
      (Y.dense.comp (ConcreteCategory.bijective_of_isIso e.inv.base).2.denseRange
        Y.inclusion.continuous)
  letI : IsDominant G := ⟨by
    apply hd.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨Y.inclusion x, congrArg (fun a => a x) hi⟩⟩
  letI : Surjective G := inferInstance
  exact (isIso_iff_isOpenImmersion_and_surjective G).mpr ⟨inferInstance, inferInstance⟩

/-- Pulling a dense open back by an open morphism preserves density. -/
theorem dense_open_baseChange {U V X Z : Scheme.{0}} (i : U ⟶ X)
    (q : Z ⟶ X) (g : V ⟶ Z) (f : V ⟶ U)
    (h : IsPullback f g i q) (hd : DenseRange i) (hq : IsOpenMap q) :
    DenseRange g := by
  have heq : Set.range g = q ⁻¹' Set.range i := by
    rw [← h.isoPullback_hom_snd]
    change Set.range ((pullback.snd i q) ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, (ConcreteCategory.bijective_of_isIso h.isoPullback.hom.base).2.range_eq,
      Set.image_univ, Scheme.Pullback.range_snd]
  change Dense (Set.range g)
  rw [heq]
  exact hd.preimage hq

end CompactComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179

/-- The specified compactifications compare by the actual base change of fields. -/
theorem compact_constant_comparison
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (hf : IsPullback f (openStructure l L E) (openStructure k L D) (constants ι)) :
    ∃! F : Y.space ⟶ X.space,
      Extends ι D E X Y f F ∧
      IsPullback F Y.projection X.projection (constants ι) ∧
      IsPullback Y.inclusion f F X.inclusion := by
  letI := X.proper
  letI := X.smooth
  letI := X.openImmersion
  let Z := pullback X.projection (constants ι)
  let p : Z ⟶ Spec (CommRingCat.of l) := pullback.snd X.projection (constants ι)
  let q : Z ⟶ X.space := pullback.fst X.projection (constants ι)
  let g : OpenBase l L E ⟶ Z := pullback.lift (f ≫ X.inclusion)
    (openStructure l L E) (by rw [Category.assoc, X.over_eq, hf.w])
  have hgq : g ≫ q = f ≫ X.inclusion := pullback.lift_fst _ _ _
  have hgp : g ≫ p = openStructure l L E := pullback.lift_snd _ _ _
  have hz : IsPullback q p X.projection (constants ι) := IsPullback.of_hasPullback _ _
  have hgi : IsPullback f g X.inclusion q := by
    apply IsPullback.of_bot (v₂₁ := p) (v₂₂ := X.projection) _ hgq.symm hz
    simpa only [hgp, X.over_eq] using hf
  letI : IsOpenImmersion g := MorphismProperty.of_isPullback hgi X.openImmersion
  have hgd : DenseRange g := CompactComparison.dense_open_baseChange
    X.inclusion q g f hgi X.dense q.isOpenMap
  obtain ⟨G, hGp, hGi⟩ := CompactComparison.extend_to_proper hL heven E Y p g hgp
  letI : IsIso G := CompactComparison.isIso_extension E Y p g hgd G hGp hGi
  let F : Y.space ⟶ X.space := G ≫ q
  have hF : Extends ι D E X Y f F := by
    constructor
    · dsimp [F]
      rw [Category.assoc, hz.w, ← Category.assoc, hGp]
    · dsimp [F]
      rw [← Category.assoc, hGi, hgq]
  have hcart : IsPullback F Y.projection X.projection (constants ι) :=
    IsPullback.of_iso_pullback ⟨hF.1⟩ (asIso G) rfl hGp
  refine ⟨F, ⟨hF, hcart, ?_⟩, ?_⟩
  · apply IsPullback.flip
    apply IsPullback.of_bot (v₂₁ := Y.projection) (v₂₂ := X.projection) _ hF.2.symm hcart
    simpa only [Y.over_eq, X.over_eq] using hf
  · intro F' hF'
    exact CompactComparison.extension_unique ι D E X Y f F' F hF'.1 hF

#print axioms compact_constant_comparison

namespace CompactComparison

/-- The scalar action used here is precisely the one induced by `ι`. -/
theorem finite_constants_properties {k l : Type} [Field k] [CharZero k]
    [Field l] (ι : k →+* l) (h : FiniteConstants ι) :
    IsFinite (constants ι) ∧ Etale (constants ι) ∧ Surjective (constants ι) ∧
      ∀ x, (constants ι).finrank x = constantDegree ι := by
  letI : Algebra k l := ι.toAlgebra
  letI : Module k l := @Algebra.toModule k l _ _ ι.toAlgebra
  letI : FiniteDimensional k l := h
  have hι : algebraMap k l = ι := rfl
  letI : IsFinite (constants ι) := by
    rw [constants, ← hι, IsFinite.SpecMap_iff]
    change (algebraMap k l).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  letI : Algebra.FormallyEtale k l := Algebra.FormallyEtale.of_isSeparable k l
  letI : Algebra.FinitePresentation k l := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.Etale k l := ⟨inferInstance, inferInstance⟩
  have he : Etale (constants ι) := by
    rw [constants, ← hι]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  have hs : Surjective (constants ι) := ⟨Function.surjective_to_subsingleton _⟩
  refine ⟨inferInstance, he, hs, ?_⟩
  intro x
  change (Spec.map (CommRingCat.ofHom (algebraMap k l))).finrank x = Module.finrank k l
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

end CompactComparison

/-- Finite coefficient extensions give finite etale maps with the exact
constant-field rank for the specified compact comparison. -/
theorem finite_constant_degree
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (hf : IsPullback f (openStructure l L E) (openStructure k L D) (constants ι))
    (F : Y.space ⟶ X.space) (hF : Extends ι D E X Y f F)
    (hfin : FiniteConstants ι) :
    IsFinite F ∧ Etale F ∧ Surjective F ∧
      ∀ x : X.space, F.finrank x = constantDegree ι := by
  obtain ⟨G, hG, _⟩ := compact_constant_comparison k l ι L hL heven D E X Y f hf
  have hFG := CompactComparison.extension_unique ι D E X Y f F G hF hG.1
  subst F
  have hp := hG.2.1.flip
  obtain ⟨hfinite, hetale, hsurj, hdegree⟩ := CompactComparison.finite_constants_properties ι hfin
  letI := hfinite
  letI := hetale
  letI := hsurj
  refine ⟨MorphismProperty.of_isPullback hp hfinite,
    MorphismProperty.of_isPullback hp hetale,
    MorphismProperty.of_isPullback hp hsurj, ?_⟩
  intro x
  rw [Scheme.Hom.finrank_of_isPullback Y.projection G (constants ι) X.projection hp]
  exact hdegree _

#print axioms finite_constant_degree

end ArithmeticThetaLevelConstantsR0234
