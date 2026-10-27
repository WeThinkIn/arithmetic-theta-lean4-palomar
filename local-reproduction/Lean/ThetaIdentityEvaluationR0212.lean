import EvenThetaRigidificationR0212
import ThetaPushforwardGeneratorR0212

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaThetaEvaluationR0212
namespace IdentityEvaluation
open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules
/-- The unit comparison is the adjoint of the actual structural map. -/
lemma unit_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules) ≫
      (pushforward f).map (pullbackUnitIso f).hom = f.unitToPushforwardUnit := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

/-- Restriction of a section followed by a normalized trivialization is the
structural pullback of scalars. -/
lemma normalized_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (s : 𝟙_ Y.Modules ⟶ L)
    (e : (pullback f).obj L ≅ 𝟙_ X.Modules)
    (he : (pullbackUnitIso f).inv ≫ (pullback f).map s ≫ e.hom = 𝟙 _) :
    s ≫ (pullbackPushforwardAdjunction f).unit.app L ≫
      (pushforward f).map e.hom = f.unitToPushforwardUnit := by
  have h : (pullback f).map s ≫ e.hom = (pullbackUnitIso f).hom := by
    calc
      _ = (pullbackUnitIso f).hom ≫
          ((pullbackUnitIso f).inv ≫ (pullback f).map s ≫ e.hom) := by simp
      _ = _ := by rw [he]; simp
  have hn : s ≫ (pullbackPushforwardAdjunction f).unit.app L =
      (pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules) ≫
        (pushforward f).map ((pullback f).map s) :=
    (pullbackPushforwardAdjunction f).unit.naturality s
  rw [← Category.assoc, hn, Category.assoc]
  rw [← Functor.map_comp, h, unit_adjunction]

/-- The two structural maps along a section compose to the identity. -/
lemma section_unit {X Y : Scheme.{u}} (π : X ⟶ Y) (z : Y ⟶ X)
    (hz : z ≫ π = 𝟙 Y) :
    π.unitToPushforwardUnit ≫ (pushforward π).map z.unitToPushforwardUnit ≫
      (pushforwardComp z π).hom.app (𝟙_ Y.Modules) ≫
      (pushforwardCongr hz).hom.app (𝟙_ Y.Modules) ≫
      (pushforwardId Y).hom.app (𝟙_ Y.Modules) = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  change Y.presheaf.map (eqToHom (show U = (z ≫ π) ⁻¹ᵁ U by rw [hz]; rfl)).op
    (z.app (π ⁻¹ᵁ U) (π.app U a)) = a
  have h := Scheme.Hom.congr_app hz.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.id_app] at h
  have hh := congrArg (fun f => f a) h
  exact hh.symm

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- The adjunction-defined evaluation has value one on the specified generator. -/
lemma generator_evaluation (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : (pullback (origin R W)).obj (thetaLine R W G M) ≅ 𝟙_ (Base R).Modules)
    (he : IsRigidification R W G M e) :
    generator R W G M ≫ evaluation R W G M e = 𝟙 _ := by
  have hn := normalized_restriction (origin R W) (thetaLine R W G M)
    (thetaMap R W G M) e he
  unfold generator evaluation
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hn]
  exact section_unit (structureMap R W) (origin R W)
    (WeierstrassProjModel.kwZeroSect R W).property

/-- An isomorphism to the unit gives a frame of the internal-Hom dual on
all opens, with the section specified by the internal-Hom correspondence. -/
lemma dual_frame {X : Scheme.{u}} (L : X.Modules)
    (g : 𝟙_ X.Modules ⟶ L) [IsIso g] (v : L ⟶ 𝟙_ X.Modules)
    (h : g ≫ v = 𝟙 _) :
    IsFrame (dual L) ⊤ ((ihomGlobalSectionsEquiv L (𝟙_ X.Modules)).symm v) := by
  let p := (MonoidalClosed.pre g).app (𝟙_ X.Modules)
  let q := (MonoidalClosed.pre (inv g)).app (𝟙_ X.Modules)
  have hpq : p ≫ q = 𝟙 _ := by
    dsimp [p, q]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, IsIso.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  have hqp : q ≫ p = 𝟙 _ := by
    dsimp [p, q]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, IsIso.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  let δ : dual L ≅ 𝟙_ X.Modules :=
    (⟨p, q, hpq, hqp⟩ : dual L ≅ (ihom (𝟙_ X.Modules)).obj (𝟙_ X.Modules)) ≪≫
      MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)
  intro U hU
  have hd : Function.Bijective (δ.hom.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  apply (Function.Bijective.of_comp_iff' hd _).mp
  have he : (fun a : Γ(X, U) => δ.hom.app U
      (a • res (dual L) hU ((ihomGlobalSectionsEquiv L (𝟙_ X.Modules)).symm v))) =
      (fun a : Γ(X, U) => a) := by
    funext a
    rw [Hom.app_smul]
    change a • (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom.app U
      (p.app U ((dual L).presheaf.map (homOfLE hU).op
        ((ihomGlobalSectionsEquiv L (𝟙_ X.Modules)).symm v))) = a
    rw [unitIsoSelf_hom_app, ihomEval_pre_app, ihomEval_map_ihomGlobalSectionsEquiv_symm]
    have hv := congrArg (fun f => f.app U (unitSection U)) h
    change v.app U (g.app U (unitSection U)) = unitSection U at hv
    rw [hv]
    exact mul_one a
  change Function.Bijective (fun a : Γ(X, U) => δ.hom.app U
    (a • res (dual L) hU ((ihomGlobalSectionsEquiv L (𝟙_ X.Modules)).symm v)))
  rw [he]
  exact Function.bijective_id

end IdentityEvaluation
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- Actual identity evaluation is inverse to the canonical generator, and its
internal-Hom section frames the dual pushforward on every base open. -/
theorem theta_identity_evaluation :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e → CategoryTheory.IsIso (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaThetaEvaluationR0212.generator R W G M) (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M e) = CategoryTheory.CategoryStruct.id ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaThetaEvaluationR0212.pushforwardLine R W G M)) ⊤ (ArithmeticThetaThetaEvaluationR0212.evaluationSection R W G M e) := by
  intro R _ _ _ _ _ W _ G hG M e he
  haveI := theta_pushforward_generator R W G hG M
  have h := IdentityEvaluation.generator_evaluation R W G M e he
  have hv : evaluation R W G M e = inv (generator R W G M) := by
    apply (cancel_epi (generator R W G M)).mp
    exact h.trans (IsIso.hom_inv_id _).symm
  refine ⟨?_, h, ?_⟩
  · rw [hv]
    infer_instance
  · exact IdentityEvaluation.dual_frame (pushforwardLine R W G M)
      (generator R W G M) (evaluation R W G M e) h

#print axioms theta_identity_evaluation
end ArithmeticThetaThetaEvaluationR0212
