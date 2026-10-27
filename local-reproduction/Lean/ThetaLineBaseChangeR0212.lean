import EvenThetaRigidificationR0212
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaThetaEvaluationR0212
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeFourCharacterR0211

namespace ThetaLineBaseChange
open EvenThetaRigidification
open Scheme.Modules

lemma pre_injective {X : Scheme.{u}} {A B : X.Modules}
    (hB : Scheme.Modules.IsInvertible B) (a b : A ⟶ B)
    (h : (MonoidalClosed.pre a).app (𝟙_ X.Modules) =
      (MonoidalClosed.pre b).app (𝟙_ X.Modules)) : a = b := by
  let d := MonoidalClosed.curry
    ((β_ (Scheme.Modules.dual B) B).hom ≫ (ihom.ev B).app (𝟙_ X.Modules))
  haveI : IsIso d := hB.isIso_ev_app_and_isIso_curry_braiding_ev.2
  apply (cancel_mono d).mp
  dsimp only [d]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left,
    BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    ← MonoidalClosed.uncurry_pre, ← MonoidalClosed.uncurry_pre, h]

lemma section_cancel {X : Scheme.{u}} {A B : X.Modules}
    (hA : Scheme.Modules.IsInvertible A) (hB : Scheme.Modules.IsInvertible B)
    (s : (𝟙_ X.Modules) ⟶ A) (hZ : (zeroSchemeIdeal s).IsInvertible)
    (a b : A ⟶ B) (h : s ≫ a = s ≫ b) : a = b := by
  obtain ⟨e, he⟩ := hA.exists_dual_iso_module_zeroSchemeIdeal s hZ
  haveI : Mono (zeroSchemeIdeal s).moduleι :=
    inferInstanceAs (Mono (kernel.ι (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit))
  haveI : Mono (sectionDual s) := by
    rw [← he]
    infer_instance
  apply pre_injective hB
  apply (cancel_mono (sectionDual s)).mp
  change (MonoidalClosed.pre a).app _ ≫ (MonoidalClosed.pre s).app _ ≫ _ =
    (MonoidalClosed.pre b).app _ ≫ (MonoidalClosed.pre s).app _ ≫ _
  simp only [← Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map, h]

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G) (M : FullLevel R W G 4 (𝟙 (Base R)))
  (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S]
  [IsIntegrallyClosed S] [Algebra ℚ S] (V : WeierstrassCurve S) [V.IsElliptic]
  (H : Law S V) (hH : IsOriginLaw S V H) (N : FullLevel S V H 4 (𝟙 (Base S)))
  (ι : R →+* S) (f : Curve S V ⟶ Curve R W)
  (hb : IsBaseChange R W G S V H ι f)
  (hm : MarkingCompatible R W G M S V H N ι f)

include hG hH hb hm in
lemma evenPoint_natural : evenPoint S V H N ≫ f = baseMap R S ι ≫ evenPoint R W G M := by
  have hx : BaseChange.point hb (𝟙 _) N.x =
      WeierstrassProjModel.schemeHomOverComp (baseMap R S ι) (by simp) M.x :=
    Subtype.ext hm.1
  have hy : BaseChange.point hb (𝟙 _) N.y =
      WeierstrassProjModel.schemeHomOverComp (baseMap R S ι) (by simp) M.y :=
    Subtype.ext hm.2
  have hc := BaseChange.point_combination hb hG hH (𝟙 _) N.x N.y 2 2
  rw [hx, hy] at hc
  change (H.mul _ (H.nsmul _ 2 N.x) (H.nsmul _ 2 N.y)).val ≫ f = _
  rw [show (H.mul _ (H.nsmul _ 2 N.x) (H.nsmul _ 2 N.y)).val ≫ f = _ from
    congrArg Subtype.val hc]
  rw [← G.nsmul_natural, ← G.nsmul_natural, ← G.mul_natural]
  rfl

include hG hH hb hm in
lemma evenPoint_cartesian :
    IsPullback (evenPoint S V H N) (baseMap R S ι) f (evenPoint R W G M) := by
  have hc := evenPoint_natural R W G hG M S V H hH N ι f hb hm
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hc
    (fun s => s.fst ≫ structureMap S V) (fun s => ?_) (fun s => ?_)
    (fun s m hm _ => ?_))
  · apply hb.1.hom_ext
    · rw [Category.assoc, hc, Category.assoc]
      change s.fst ≫ structureMap S V ≫ Spec.map (CommRingCat.ofHom ι) ≫ evenPoint R W G M = _
      rw [← hb.1.w_assoc, ← Category.assoc s.fst f, s.condition]
      simp only [Category.assoc]
      rw [← Category.assoc (evenPoint R W G M) (structureMap R W), evenPoint_over,
        Category.id_comp]
    · rw [Category.assoc, evenPoint_over, Category.comp_id]
  · have H := congrArg (fun a => a ≫ structureMap R W) s.condition
    simpa only [Category.assoc, hb.1.w, evenPoint_over, Category.comp_id, baseMap] using H
  · rw [← hm, Category.assoc, evenPoint_over, Category.comp_id]

include hG hH hb hm in
lemma thetaIdeal_comap : (thetaIdeal R W G M).comap f = thetaIdeal S V H N := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  haveI : IsClosedImmersion (evenPoint R W G M ≫ structureMap R W) := by
    rw [evenPoint_over]; infer_instance
  haveI : IsClosedImmersion (evenPoint R W G M) :=
    IsClosedImmersion.of_comp _ (structureMap R W)
  have hp := evenPoint_cartesian R W G hG M S V H hH N ι f hb hm
  unfold thetaIdeal
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

end ThetaLineBaseChange

/-- The canonical theta line and its section commute uniquely with the given
pointed Cartesian comparison preserving the two full-four markings. -/
theorem theta_line_base_change :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∀ (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (V : WeierstrassCurve S) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law S V), ArithmeticThetaRelativeKatoR0169.IsOriginLaw S V H → ∀ (N : ArithmeticThetaFullLevelCoverR0175.FullLevel S V H 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (f : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S V) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι f), ArithmeticThetaRelativeFourCharacterR0211.MarkingCompatible R W G M S V H N ι f → (ArithmeticThetaThetaEvaluationR0212.thetaIdeal R W G M).comap f = ArithmeticThetaThetaEvaluationR0212.thetaIdeal S V H N ∧ (∃! q : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (f)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) (ArithmeticThetaThetaEvaluationR0212.thetaLine S V H N), ArithmeticThetaThetaEvaluationR0212.PreservesThetaSection R W G M S V H N f q) := by
  intro R _ _ _ _ _ W _ G hG M S _ _ _ _ _ V _ H hH N ι f hb hm
  have hI := ThetaLineBaseChange.thetaIdeal_comap R W G hG M S V H hH N ι f hb hm
  refine ⟨hI, ?_⟩
  have hL := (EvenThetaRigidification.thetaIdeal_invertible R W G M).isInvertible_invModule
  have hLs := (EvenThetaRigidification.thetaIdeal_invertible S V H N).isInvertible_invModule
  let s := Scheme.Modules.pullbackSection f (thetaMap R W G M)
  have hz : Scheme.Modules.zeroSchemeIdeal s = thetaIdeal S V H N := by
    rw [← hL.comap_zeroSchemeIdeal, EvenThetaRigidification.thetaMap_eq,
      (EvenThetaRigidification.thetaIdeal_invertible R W G M).zeroSchemeIdeal_invModuleSection,
      hI]
  have hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible := by
    rw [hz]; exact EvenThetaRigidification.thetaIdeal_invertible S V H N
  obtain ⟨q, hq⟩ := (hL.pullback f).exists_iso_invModule_zeroSchemeIdeal s hZ
  have hq' : ∃ q : (Scheme.Modules.pullback f).obj (thetaLine R W G M) ≅
      thetaLine S V H N, s ≫ q.hom = thetaMap S V H N := by
    rw [EvenThetaRigidification.thetaMap_eq]
    change ∃ q : (Scheme.Modules.pullback f).obj (thetaLine R W G M) ≅
      (thetaIdeal S V H N).invModule, s ≫ q.hom = (thetaIdeal S V H N).invModuleSection
    rw [← hz]
    exact ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hq'
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  exact ThetaLineBaseChange.section_cancel (hL.pullback f) hLs s hZ q'.hom q.hom
    (hq'.trans hq.symm)

#print axioms theta_line_base_change
end ArithmeticThetaThetaEvaluationR0212
