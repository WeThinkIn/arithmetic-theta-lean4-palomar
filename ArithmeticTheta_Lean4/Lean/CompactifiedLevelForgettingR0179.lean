import LevelBoundaryGeometryR0179
import LevelForgettingMapR0179
import Theorems.Thm_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field

import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLevelCompactificationR0179
namespace CompactifiedLevelForgetting
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

variable (k : Type u) [Field k] {L d : ℕ}
variable (D : LevelData k L) (E : LevelData k d)
variable (X : Compactification k L D) (Y : Compactification k d E)

lemma reduced : IsReduced X.space := by
  letI := X.smooth
  exact isReduced_of_smooth_over_field (g := X.projection) inferInstance

lemma extension_unique (f : OpenBase k L D ⟶ OpenBase k d E)
    (F G : X.space ⟶ Y.space)
    (hF : F ≫ Y.projection = X.projection)
    (hG : G ≫ Y.projection = X.projection)
    (hFi : X.inclusion ≫ F = f ≫ Y.inclusion)
    (hGi : X.inclusion ≫ G = f ≫ Y.inclusion) : F = G := by
  letI := reduced k D X
  letI := Y.proper
  letI : IsDominant X.inclusion := ⟨X.dense⟩
  exact ext_of_isDominant_of_isSeparated Y.projection (hF.trans hG.symm)
    X.inclusion (hFi.trans hGi.symm)

lemma extension_exists [CharZero k] (hL : 3 ≤ L) (heven : Even L)
    (f : OpenBase k L D ⟶ OpenBase k d E)
    (hf : f ≫ openStructure k d E = openStructure k L D) :
    ∃ F : X.space ⟶ Y.space,
      F ≫ Y.projection = X.projection ∧ X.inclusion ≫ F = f ≫ Y.inclusion := by
  letI := X.openImmersion
  letI := X.proper
  letI := Y.proper
  letI := reduced k D X
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  let U := X.inclusion.opensRange
  let e : OpenBase k L D ≅ (U : Scheme.{u}) :=
    IsOpenImmersion.isoOfRangeEq X.inclusion U.ι (by simp [U])
  have hei : e.inv ≫ X.inclusion = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have heh : e.hom ≫ U.ι = X.inclusion := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hval : ∀ x : X.space, x ∉ U →
      (∃ _ : IsDomain (X.space.presheaf.stalk x), IsDiscreteValuationRing (X.space.presheaf.stalk x)) ∧
        ∃ y : X.space, y ∈ U ∧ y ⤳ x := by
    intro x hx
    obtain ⟨_, hdom, hdvr, _⟩ := (level_boundary_geometry k L hL heven D X).2.2 x hx
    letI := hdom
    refine ⟨⟨hdom, hdvr⟩, ?_⟩
    let η := P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.genPt x
    obtain ⟨V, hxV, hV⟩ :=
      P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.exists_opens_forall_genPt_specializes x
    obtain ⟨z, hzV, hzU⟩ := X.dense.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨η, (hV z hzV).mem_open U.isOpen hzU,
      P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.ExtendAux.genPt_specializes_self x⟩
  obtain ⟨F, hF, hFi⟩ :=
    exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
      X.projection Y.projection U (e.inv ≫ f ≫ Y.inclusion) (by
        rw [Category.assoc, Category.assoc, Y.over_eq, hf, ← X.over_eq,
          ← Category.assoc, hei]) hval
  refine ⟨F, hF, ?_⟩
  rw [← heh, Category.assoc, hFi]
  simp

lemma extension_proper (F : X.space ⟶ Y.space)
    (hF : F ≫ Y.projection = X.projection) : IsProper F := by
  letI := X.proper
  letI := Y.proper
  letI : IsProper (F ≫ Y.projection) := hF.symm ▸ X.proper
  exact IsProper.of_comp F Y.projection

lemma extension_finite (f : OpenBase k L D ⟶ OpenBase k d E) [IsFinite f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) : IsFinite F := by
  letI := extension_proper k D E X Y F hF
  letI := Y.openImmersion
  letI : LocallyQuasiFinite F := LocallyQuasiFinite.of_finite_preimage_singleton F fun y => by
    have hfin := f.finite_preimage ((Set.finite_singleton y).preimage
      Y.inclusion.isOpenEmbedding.injective.injOn)
    apply ((hfin.image X.inclusion.base).union (BoundaryGeometry.boundary_finite k L D X)).subset
    intro x hx
    by_cases hxi : x ∈ Set.range X.inclusion.base
    · obtain ⟨z, rfl⟩ := hxi
      apply Or.inl
      refine ⟨z, ?_, rfl⟩
      change (f ≫ Y.inclusion) z = y
      rw [← hi]
      exact hx
    · exact Or.inr hxi
  exact IsFinite.of_isProper_of_locallyQuasiFinite F

lemma extension_surjective (f : OpenBase k L D ⟶ OpenBase k d E) [Surjective f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) : Surjective F := by
  letI := extension_proper k D E X Y F hF
  refine ⟨fun y => ?_⟩
  apply F.isClosedMap.isClosed_range.closure_subset_iff.mpr ?_ (Y.dense y)
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, rfl⟩ := f.surjective z
  exact ⟨X.inclusion w, congrArg (fun a => a w) hi⟩

lemma extension_flat (f : OpenBase k L D ⟶ OpenBase k d E) [IsFinite f] [Flat f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) : Flat F := by
  letI := X.openImmersion
  letI := Y.openImmersion
  letI := X.smooth
  letI := Y.smooth
  letI := extension_finite k D E X Y f F hF hi
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  letI : IsLocallyNoetherian Y.space := LocallyOfFiniteType.isLocallyNoetherian Y.projection
  apply Flat.of_stalkMap
  intro x
  by_cases hx : x ∈ Set.range X.inclusion.base
  · obtain ⟨z, rfl⟩ := hx
    letI : Flat (X.inclusion ≫ F) := by rw [hi]; infer_instance
    have h := Flat.stalkMap (X.inclusion ≫ F) z
    rw [Scheme.Hom.stalkMap_comp] at h
    exact (RingHom.Flat.comp_iff_of_bijective_left
      ((asIso (X.inclusion.stalkMap z)).commRingCatIsoToRingEquiv.bijective)).mp h
  · have hc := BoundaryGeometry.boundary_point_closed k L D X x hx
    have hcy : IsClosed ({F x} : Set Y.space) := by
      simpa only [Set.image_singleton] using F.isClosedMap {x} hc
    letI := Smooth.isRegularLocalRing_stalk (f := X.projection) x
    letI := Smooth.isRegularLocalRing_stalk (f := Y.projection) (F x)
    letI : Algebra (Y.space.presheaf.stalk (F x)) (X.space.presheaf.stalk x) :=
      (F.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.space.presheaf.stalk (F x))
        (X.space.presheaf.stalk x)) := inferInstanceAs (IsLocalHom (F.stalkMap x).hom)
    exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (Y.space.presheaf.stalk (F x)) (X.space.presheaf.stalk x)
      (LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero F x)
      ((SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed k X.projection 1 x hc).trans
        (SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed k Y.projection 1 (F x) hcy).symm)

lemma extension_cartesian (f : OpenBase k L D ⟶ OpenBase k d E) [IsFinite f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) :
    IsPullback X.inclusion f F Y.inclusion := by
  letI := X.openImmersion
  letI := Y.openImmersion
  letI := extension_finite k D E X Y f F hF hi
  let a : OpenBase k L D ⟶ pullback F Y.inclusion := pullback.lift X.inclusion f hi
  have ha : a ≫ pullback.fst F Y.inclusion = X.inclusion := pullback.lift_fst _ _ _
  have hb : a ≫ pullback.snd F Y.inclusion = f := pullback.lift_snd _ _ _
  letI : IsOpenImmersion (a ≫ pullback.fst F Y.inclusion) := ha.symm ▸ X.openImmersion
  letI : IsOpenImmersion a := IsOpenImmersion.of_comp a (pullback.fst F Y.inclusion)
  letI : IsProper (a ≫ pullback.snd F Y.inclusion) := by rw [hb]; infer_instance
  letI : IsProper a := IsProper.of_comp a (pullback.snd F Y.inclusion)
  letI : IsDominant a := ⟨by
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    have ho := (pullback.fst F Y.inclusion).isOpenEmbedding.isOpenMap O hO
    obtain ⟨x, ⟨z, hzO, hzx⟩, w, hwx⟩ :=
      X.dense.inter_open_nonempty _ ho (hOne.image (pullback.fst F Y.inclusion))
    refine ⟨z, hzO, w, ?_⟩
    apply (pullback.fst F Y.inclusion).isOpenEmbedding.injective
    exact (congrArg (fun m => m w) ha).trans (hwx.trans hzx.symm)⟩
  letI : Surjective a := inferInstance
  letI : IsIso a := (isIso_iff_isOpenImmersion_and_surjective a).mpr ⟨inferInstance, inferInstance⟩
  exact IsPullback.of_iso_pullback ⟨hi⟩ (asIso a) ha hb

lemma extension_degree (f : OpenBase k L D ⟶ OpenBase k d E) [IsFinite f] [Flat f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion)
    (n : ℕ) (hn : ∀ y, f.finrank y = n) : ∀ y, F.finrank y = n := by
  letI := Y.proper
  letI : IsLocallyNoetherian Y.space := LocallyOfFiniteType.isLocallyNoetherian Y.projection
  letI := extension_finite k D E X Y f F hF hi
  letI := extension_flat k D E X Y f F hF hi
  have hpb := extension_cartesian k D E X Y f F hF hi
  intro y
  obtain ⟨U, hU, hy, he⟩ := (IsLocallyConstant.iff_exists_open _).mp F.isLocallyConstant_finrank y
  obtain ⟨z, hz, w, hw⟩ := Y.dense.inter_open_nonempty U hU ⟨y, hy⟩
  rw [← he z hz, ← hw, ← Scheme.Hom.finrank_of_isPullback X.inclusion f F Y.inclusion hpb]
  exact hn w

end CompactifiedLevelForgetting
open CategoryTheory AlgebraicGeometry

/-- The actual reduction map extends uniquely to arbitrary smooth projective
completions, with its finite flat degree and its full Cartesian open square. -/
theorem compactified_level_forgetting
    (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (d : ℕ) (hd : 3 ≤ d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d)
    (X : Compactification k L D) (Y : Compactification k d E) :
    ∃! f : Quiver.Hom (OpenBase k L D) (OpenBase k d E),
      IsReduction k L D E f ∧
        ∃! F : Quiver.Hom X.space Y.space, ExtendsReduction k L D E X Y f F := by
  obtain ⟨f, hf, hfu⟩ := level_forgetting_map k L hL heven d hd hdeven hdL D E
  letI := hf.2.1
  letI := hf.2.2.1
  letI := hf.2.2.2.1
  obtain ⟨F, hF, hi⟩ := CompactifiedLevelForgetting.extension_exists
    k D E X Y hL heven f hf.1.1
  refine ⟨f, ⟨hf, F, ?_, ?_⟩, fun g hg => hfu g hg.1⟩
  · exact ⟨hF, hi,
      CompactifiedLevelForgetting.extension_cartesian k D E X Y f F hF hi,
      CompactifiedLevelForgetting.extension_finite k D E X Y f F hF hi,
      CompactifiedLevelForgetting.extension_flat k D E X Y f F hF hi,
      CompactifiedLevelForgetting.extension_surjective k D E X Y f F hF hi,
      CompactifiedLevelForgetting.extension_degree k D E X Y f F hF hi _ hf.2.2.2.2⟩
  · intro G hG
    exact CompactifiedLevelForgetting.extension_unique k D E X Y f G F hG.1 hF hG.2.1 hi

#print axioms compactified_level_forgetting
end ArithmeticThetaLevelCompactificationR0179
