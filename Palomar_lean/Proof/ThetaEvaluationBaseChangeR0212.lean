module

public import ThetaLineBaseChangeR0212
public import ThetaIdentityEvaluationR0212
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
public import RelativeFourCharacterDefinitionsR0211

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaThetaEvaluationR0212
namespace EvaluationBaseChange
open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules

lemma congr_unit {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (pullbackCongr h).hom.app (𝟙_ Y.Modules) ≫ (pullbackUnitIso g).hom =
      (pullbackUnitIso f).hom := by
  subst g
  simp [pullbackCongr]

#print axioms congr_unit

lemma square_unit {X T X' T' : Scheme.{u}}
    {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {f : X' ⟶ X}
    (h : f ≫ π = π' ≫ ψ) :
    (pullbackTwoSquare h).natTrans.app (𝟙_ T.Modules) ≫
      (pullback f).map (pullbackUnitIso π).hom ≫ (pullbackUnitIso f).hom =
    (pullback π').map (pullbackUnitIso ψ).hom ≫ (pullbackUnitIso π').hom := by
  rw [← pullbackComp_hom_app_comp_pullbackUnitIso_hom]
  change ((pullbackComp π' ψ).hom.app _ ≫ (pullbackCongr h.symm).hom.app _ ≫
    (pullbackComp f π).inv.app _) ≫ _ = _
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [congr_unit, pullbackComp_hom_app_comp_pullbackUnitIso_hom]

#print axioms square_unit

lemma base_change_unit {X T X' T' : Scheme.{u}}
    {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {f : X' ⟶ X}
    (h : f ≫ π = π' ≫ ψ) :
    (pullback ψ).map π.unitToPushforwardUnit ≫ baseChangeHom h (𝟙_ X.Modules) ≫
      (pushforward π').map (pullbackUnitIso f).hom =
    (pullbackUnitIso ψ).hom ≫ π'.unitToPushforwardUnit := by
  rw [← IdentityEvaluation.unit_adjunction π, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (baseChangeHom_naturality h (pullbackUnitIso π).hom)]
  erw [← Category.assoc, unit_baseChangeHom h (𝟙_ T.Modules)]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [square_unit h, Functor.map_comp]
  erw [← Category.assoc, ← (pullbackPushforwardAdjunction π').unit.naturality (pullbackUnitIso ψ).hom]
  simp only [Category.assoc]
  erw [IdentityEvaluation.unit_adjunction π']
  rfl

#print axioms base_change_unit

/-- Canonical base change carries the structural generator to the generator
specified by the pulled-back section. No flatness assumption enters. -/
lemma base_change_generator {X T X' T' : Scheme.{u}}
    {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {f : X' ⟶ X}
    (h : f ≫ π = π' ≫ ψ) {L : X.Modules} {K : X'.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (t : 𝟙_ X'.Modules ⟶ K)
    (q : (pullback f).obj L ⟶ K)
    (hq : (pullbackUnitIso f).inv ≫ (pullback f).map s ≫ q = t) :
    (pullback ψ).map (π.unitToPushforwardUnit ≫ (pushforward π).map s) ≫
      (baseChangeHom h L ≫ (pushforward π').map q) =
    (pullbackUnitIso ψ).hom ≫ π'.unitToPushforwardUnit ≫ (pushforward π').map t := by
  have hq' : (pullback f).map s ≫ q = (pullbackUnitIso f).hom ≫ t := by
    rw [← hq]
    simp
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (baseChangeHom_naturality h s)]
  rw [← Functor.map_comp, hq', Functor.map_comp]
  exact (reassoc_of% (base_change_unit h)) ((pushforward π').map t)

#print axioms base_change_generator

/-- Cancellation of the actual generators gives both invertibility and the
naturality of their normalized evaluations. -/
lemma iso_and_naturality {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A J : C} {B K : D}
    (g : A ⟶ J) (k : B ⟶ K) [IsIso g] [IsIso k]
    (u : F.obj A ≅ B) (v : J ⟶ A) (w : K ⟶ B)
    (c : F.obj J ⟶ K) (hv : g ≫ v = 𝟙 _) (hw : k ≫ w = 𝟙 _)
    (hc : F.map g ≫ c = u.hom ≫ k) :
    IsIso c ∧ c ≫ w = F.map v ≫ u.hom := by
  have hi : c = inv (F.map g) ≫ u.hom ≫ k := by
    apply (cancel_epi (F.map g)).mp
    simpa only [IsIso.hom_inv_id_assoc] using hc
  refine ⟨?_, ?_⟩
  · rw [hi]
    infer_instance
  · apply (cancel_epi (F.map g)).mp
    rw [← Category.assoc, hc, Category.assoc, hw, Category.comp_id,
      ← Category.assoc, ← Functor.map_comp, hv, CategoryTheory.Functor.map_id, Category.id_comp]

#print axioms iso_and_naturality

/-- A presentation with named maps keeps their declared domains during
specialization. The equations identify all three maps with their definitions. -/
lemma named_generator {X T X' T' : Scheme.{u}}
    {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {f : X' ⟶ X}
    (h : f ≫ π = π' ≫ ψ) {L : X.Modules} {K : X'.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (t : 𝟙_ X'.Modules ⟶ K)
    (q : (pullback f).obj L ⟶ K)
    (hq : (pullbackUnitIso f).inv ≫ (pullback f).map s ≫ q = t)
    (g : 𝟙_ T.Modules ⟶ (pushforward π).obj L)
    (k : 𝟙_ T'.Modules ⟶ (pushforward π').obj K)
    (c : (pullback ψ).obj ((pushforward π).obj L) ⟶ (pushforward π').obj K)
    (hg : g = π.unitToPushforwardUnit ≫ (pushforward π).map s)
    (hk : k = π'.unitToPushforwardUnit ≫ (pushforward π').map t)
    (hc : c = baseChangeHom h L ≫ (pushforward π').map q) :
    (pullback ψ).map g ≫ c = (pullbackUnitIso ψ).hom ≫ k := by
  subst g k c
  exact base_change_generator h s t q hq

#print axioms named_generator

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

set_option maxHeartbeats 200000 in
lemma comparison_generator
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G 4 (𝟙 (Base R)))
    (S : Type u) [CommRing S] (V : WeierstrassCurve S) (H : Law S V)
    (N : FullLevel S V H 4 (𝟙 (Base S))) (ι : R →+* S)
    (f : Curve S V ⟶ Curve R W)
    (h : f ≫ structureMap R W = structureMap S V ≫ baseMap R S ι)
    (q : (pullback f).obj (thetaLine R W G M) ≅ thetaLine S V H N)
    (hq : PreservesThetaSection R W G M S V H N f q) :
    (pullback (baseMap R S ι)).map (generator R W G M) ≫
      pushforwardComparison R W G M S V H N ι f h q =
      (pullbackUnitIso (baseMap R S ι)).hom ≫ generator S V H N := by
  have hp := @named_generator (Curve R W) (Spec (.of R)) (Curve S V) (Spec (.of S))
    (structureMap R W) (baseMap R S ι) (structureMap S V) f h
  have hL := @hp (thetaLine R W G M) (thetaLine S V H N)
  have hs := hL (thetaMap R W G M) (thetaMap S V H N) q.hom
  have ht := hs hq
  have hg := ht (generator R W G M)
  have hk := hg (generator S V H N)
  have hc := hk (pushforwardComparison R W G M S V H N ι f h q)
  apply hc rfl rfl
  unfold pushforwardComparison
  rfl

#print axioms comparison_generator

end EvaluationBaseChange
open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- The actual pushforward comparison is invertible and intertwines the
geometric identity evaluations for every allowed pointed base change. -/
theorem theta_evaluation_base_change :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∀ (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (V : WeierstrassCurve S) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law S V), ArithmeticThetaRelativeKatoR0169.IsOriginLaw S V H → ∀ (N : ArithmeticThetaFullLevelCoverR0175.FullLevel S V H 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (f : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S V) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι f), ArithmeticThetaRelativeFourCharacterR0211.MarkingCompatible R W G M S V H N ι f → ∀ (q : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (f)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) (ArithmeticThetaThetaEvaluationR0212.thetaLine S V H N)), ArithmeticThetaThetaEvaluationR0212.PreservesThetaSection R W G M S V H N f q → ∀ (eR : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf))) (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin S V)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine S V H N)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base S).ringCatSheaf))), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M eR → ArithmeticThetaThetaEvaluationR0212.IsRigidification S V H N eS → CategoryTheory.IsIso (ArithmeticThetaThetaEvaluationR0212.pushforwardComparison R W G M S V H N ι f hb.1.w q) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaThetaEvaluationR0212.pushforwardComparison R W G M S V H N ι f hb.1.w q) (ArithmeticThetaThetaEvaluationR0212.evaluation S V H N eS) = CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).map (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M eR)) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).hom) := by
  intro R _ _ _ _ _ W _ G hG M S _ _ _ _ _ V _ H hH N ι f hb hm q hq eR eS heR heS
  exact @EvaluationBaseChange.iso_and_naturality
    (Base R).Modules (Base S).Modules _ _ (pullback (baseMap R S ι))
    (𝟙_ (Base R).Modules) (pushforwardLine R W G M)
    (𝟙_ (Base S).Modules) (pushforwardLine S V H N)
    (generator R W G M) (generator S V H N)
    (theta_pushforward_generator R W G hG M) (theta_pushforward_generator S V H hH N)
    (pullbackUnitIso (baseMap R S ι)) (evaluation R W G M eR)
    (evaluation S V H N eS) (pushforwardComparison R W G M S V H N ι f hb.1.w q)
    (IdentityEvaluation.generator_evaluation R W G M eR heR)
    (IdentityEvaluation.generator_evaluation S V H N eS heS)
    (EvaluationBaseChange.comparison_generator R W G M S V H N ι f hb.1.w q hq)

#print axioms theta_evaluation_base_change
end ArithmeticThetaThetaEvaluationR0212
