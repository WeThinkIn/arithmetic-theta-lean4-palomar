module

public import ThetaEvaluationDefinitionsR0212
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

@[expose] public section

/-! The actual even theta divisor and its normalized identity rigidification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaThetaEvaluationR0212
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190

namespace EvenThetaRigidification
open Scheme.Modules
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133

lemma fromSection_ihom {X : Scheme.{u}} (A B : X.Modules) (f : A ⟶ B) :
    fromSection ((ihom A).obj B) ((ihomGlobalSectionsEquiv A B).symm f) =
      MonoidalClosed.curry' f := by
  apply ihom_hom_ext
  intro U m p
  change Γ(X, U) at p
  rw [fromSection_apply, ihomEval_smul_right, ihomEval_map_ihomGlobalSectionsEquiv_symm]
  unfold MonoidalClosed.curry'
  rw [ihomEval_curry_app]
  rw [Hom.comp_app, ConcreteCategory.comp_apply]
  erw [rightUnitor_hom_app_tensorSections m p]
  exact (Hom.app_smul f p m).symm

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
  (M : FullLevel R W G 4 (𝟙 (Base R)))

lemma thetaMap_eq : thetaMap R W G M = (thetaIdeal R W G M).invModuleSection :=
  fromSection_ihom _ _ _

lemma evenPoint_over : evenPoint R W G M ≫ structureMap R W = 𝟙 _ := by
  exact (G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y)).property

lemma evenPoint_disjoint :
    Disjoint (Set.range (evenPoint R W G M)) (Set.range (origin R W)) := by
  exact M.avoids (2 : Fin 4) (2 : Fin 4) (Or.inl (by decide))

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
  [W.IsElliptic]

lemma thetaIdeal_invertible : (thetaIdeal R W G M).IsInvertible := by
  let : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (relative_curve_geometry R W).2.2.2.2.2.1
  let : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (evenPoint_over R W G M)

lemma originGenerator_isIso : IsIso (originGenerator R W G M) := by
  let : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have : IsClosedImmersion (evenPoint R W G M ≫ structureMap R W) := by
    rw [evenPoint_over]; infer_instance
  have : IsClosedImmersion (evenPoint R W G M) :=
    IsClosedImmersion.of_comp _ (structureMap R W)
  have hI := thetaIdeal_invertible R W G M
  have hL := hI.isInvertible_invModule
  have hz : zeroSchemeIdeal (thetaMap R W G M) = thetaIdeal R W G M := by
    rw [thetaMap_eq]; exact hI.zeroSchemeIdeal_invModuleSection
  have hd : Disjoint (Set.range (origin R W)) ((thetaIdeal R W G M).support : Set _) := by
    change Disjoint (Set.range (origin R W)) ((evenPoint R W G M).ker.support : Set (Curve R W))
    rw [Scheme.Hom.support_ker, (evenPoint R W G M).isClosedEmbedding.isClosed_range.closure_eq]
    exact (evenPoint_disjoint R W G M).symm
  have ht := ((thetaIdeal R W G M).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    (origin R W) hd).1
  have hp : zeroSchemeIdeal (originGenerator R W G M) = ⊤ := by
    change zeroSchemeIdeal (pullbackSection (origin R W) (thetaMap R W G M)) = ⊤
    rw [← hL.comap_zeroSchemeIdeal, hz, ht]
  apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.isIso_of_frame_top
  apply (hL.pullback (origin R W)).isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
  rw [hp, Scheme.IdealSheafData.support_top]
  exact disjoint_bot_right

end EvenThetaRigidification

/-- The inverse ideal of the marked even point, with its canonical section,
has exactly one identity rigidification sending that section to one. -/
theorem even_theta_rigidification :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : Law R W), IsOriginLaw R W G →
      ∀ M : FullLevel R W G 4 (𝟙 (Base R)),
      (thetaIdeal R W G M).IsInvertible ∧
      Scheme.Modules.IsInvertible (thetaLine R W G M) ∧
      Scheme.Modules.zeroSchemeIdeal (thetaMap R W G M) = thetaIdeal R W G M ∧
      (∃! e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅
        (SheafOfModules.unit (Base R).ringCatSheaf), IsRigidification R W G M e) := by
  intro R _ _ _ _ _ W _ G _ M
  have hI := EvenThetaRigidification.thetaIdeal_invertible R W G M
  refine ⟨hI, hI.isInvertible_invModule, ?_, ?_⟩
  · rw [EvenThetaRigidification.thetaMap_eq]
    exact hI.zeroSchemeIdeal_invModuleSection
  · have := EvenThetaRigidification.originGenerator_isIso R W G M
    refine ⟨(asIso (originGenerator R W G M)).symm, ?_, ?_⟩
    · exact IsIso.hom_inv_id _
    · intro e he
      apply Iso.ext
      apply (cancel_epi (originGenerator R W G M)).mp
      exact he.trans (IsIso.hom_inv_id _).symm

#print axioms even_theta_rigidification
end ArithmeticThetaThetaEvaluationR0212
