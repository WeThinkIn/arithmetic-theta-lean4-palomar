import PhaseFreeMultiplierR0219

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219.AlphaProof
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaPullback ArithmeticThetaSheafTensor
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open Scheme.Modules
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

/-- Comparison from the explicit sheafification to the categorical tensor. -/
def tensorBridge {X : Scheme.{u}} (M N : X.Modules) : sheafTensor X M N ≅ M ⊗ N :=
  tensorIsoSheafify M N

lemma tensorBridge_section {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorBridge M N).hom.app U (tensorSection X M N U s t) = tensorSections s t := by
  rfl

/-- Evaluation of the actual cotangent line against its internal-Hom dual. -/
def evaluationIso : productLine E (MultiplierProof.line E) ≅ 𝟙_ S.Modules := by
  letI := ((MultiplierProof.cotangent_invertible E).isIso_ihom_ev_app_monoidalV2).1
    (𝟙_ S.Modules)
  exact tensorBridge _ _ ≪≫ asIso ((ihom.ev (Cotangent E)).app (𝟙_ S.Modules))

/-- The two tensor comparisons agree on the generating local tensor sections. -/
lemma tensor_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback_sheafTensor_iso X Y f M N).hom ≫
      (tensorBridge ((pullback f).obj M) ((pullback f).obj N)).hom =
    (pullback f).map (tensorBridge M N).hom ≫ (pullbackTensorObjIso f M N).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ArithmeticThetaSheafTensor.tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change (tensorBridge ((pullback f).obj M) ((pullback f).obj N)).hom.app _
      ((pullback_sheafTensor_iso X Y f M N).hom.app (f ⁻¹ᵁ U.unop)
        (pullbackLocalSection f (tensorSection Y M N U.unop s t))) =
    (pullbackTensorObjIso f M N).hom.app (f ⁻¹ᵁ U.unop)
      (((pullback f).map (tensorBridge M N).hom).app _
        (pullbackLocalSection f (tensorSection Y M N U.unop s t)))
  rw [← pullbackLocalSection_app, tensorBridge_section,
    AlphaTensorCoherence.pullback_tensor_local,
    pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2, tensorBridge_section]

def canonicalSection : Γ(productLine E (MultiplierProof.line E), ⊤) :=
  (evaluationIso E).inv.app ⊤ (1 : Γ(S, ⊤))

lemma canonicalSection_frame :
    IsFrame (productLine E (MultiplierProof.line E)) ⊤ (canonicalSection E) :=
  frame_iso (evaluationIso E).symm _ (InverseCharacterMultiplier.unit_frame S)

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)

lemma canonical_tensor (A : MarkedTest E P) :
    (pullback_sheafTensor_iso A.base S A.map (Cotangent E) (MultiplierProof.line E)).hom.app ⊤
      (pullbackGlobalSection A.map _ (canonicalSection E)) =
      tensorSection A.base _ _ ⊤ (MultiplierProof.pulledAlpha E P k σ A)
        (MultiplierProof.frames E P k σ A) := by
  letI := ((MultiplierProof.cotangent_invertible E).isIso_ihom_ev_app_monoidalV2).1
    (𝟙_ S.Modules)
  letI := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unitPullback_isIso A.map
  letI : IsIso (MultiplierProof.pairing A.map (Cotangent E)) := by
    unfold MultiplierProof.pairing
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso
    ((tensorBridge _ _).hom.app ⊤)).1
  rw [tensorBridge_section]
  apply (ConcreteCategory.bijective_of_isIso
    ((MultiplierProof.pairing A.map (Cotangent E)).app ⊤)).1
  have ht := congrArg (fun q => q.app ⊤ (pullbackGlobalSection A.map _ (canonicalSection E)))
    (tensor_comparison A.map (Cotangent E) (MultiplierProof.line E))
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at ht
  rw [ht]
  have hmap : (pullbackTensorObjIso A.map (Cotangent E) (MultiplierProof.line E)).hom ≫
      MultiplierProof.pairing A.map (Cotangent E) =
      (pullback A.map).map ((ihom.ev (Cotangent E)).app (𝟙_ S.Modules)) ≫
        ArithmeticThetaPolygonCartierR0133.unitPullback A.map := by
    dsimp only [MultiplierProof.pairing]
    rw [Iso.hom_inv_id_assoc]
  have heval : ((pullback A.map).map (tensorBridge (Cotangent E) (MultiplierProof.line E)).hom ≫
      (pullbackTensorObjIso A.map (Cotangent E) (MultiplierProof.line E)).hom ≫
      MultiplierProof.pairing A.map (Cotangent E)) =
      (pullback A.map).map (evaluationIso E).hom ≫
        ArithmeticThetaPolygonCartierR0133.unitPullback A.map := by
    rw [hmap, ← Category.assoc, ← Functor.map_comp]
    rfl
  have h := congrArg (fun q => q.app ⊤ (pullbackGlobalSection A.map _ (canonicalSection E))) heval
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at h
  rw [h]
  erw [MultiplierBaseChange.global_app]
  have he : (evaluationIso E).hom.app ⊤ (canonicalSection E) = (1 : Γ(S, ⊤)) := by
    exact ConcreteCategory.congr_hom (congrArg (fun q => q.app ⊤) (evaluationIso E).inv_hom_id) _
  rw [he]
  erw [unitPullback_app A.map ⊤ (1 : Γ(S, ⊤)), map_one]
  exact (MultiplierProof.frames_eval E P k σ A).symm.trans
    (MultiplierProof.pairing_eval A.map (Cotangent E) _ _)

/-- The canonical duality section has the full all-test alpha equality. -/
lemma canonical_descends : Descends E P (MultiplierProof.line E)
    (MultiplierProof.frames E P k σ) (canonicalSection E) := by
  intro A
  refine ⟨⟨MultiplierProof.comparison E P A, MultiplierProof.comparison_spec E P A⟩,
    ⟨MultiplierProof.alpha E P k σ A, MultiplierProof.alpha_spec E P k σ A⟩, ?_⟩
  intro c hc a ha
  have hcEq : c = MultiplierProof.comparison E P A :=
    (MultiplierProof.comparison_exists E P A).unique hc (MultiplierProof.comparison_spec E P A)
  have haEq : a = MultiplierProof.alpha E P k σ A :=
    (scheme_alpha_section k A.base (A.map ≫ σ) A.family A.marking).1.unique ha
      (MultiplierProof.alpha_spec E P k σ A)
  subst c; subst a
  simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
  erw [canonical_tensor E P k σ A]
  erw [sheafTensorCongr_section]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun q => q.app ⊤) (MultiplierProof.comparison E P A).inv_hom_id)
      (MultiplierProof.alpha E P k σ A)
  change (MultiplierProof.comparison E P A).hom.app ⊤
      (MultiplierProof.pulledAlpha E P k σ A) = MultiplierProof.alpha E P k σ A at h
  rw [h]
  rfl

/-- Transport uses the actual tensor of the frame-preserving comparison. -/
lemma descends_transport {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
    (v : L ≅ K) (hv : PreservesFrames E P m n v)
    (β : Γ(productLine E L, ⊤)) (hβ : Descends E P L m β) :
    Descends E P K n ((sheafTensorCongr S (Iso.refl (Cotangent E)) v).hom.app ⊤ β) := by
  intro A
  refine ⟨(hβ A).1, (hβ A).2.1, ?_⟩
  intro c hc a ha
  have h := ArithmeticThetaPhaseSwitchR0218.KeyPhaseSwitch.tensor_map_section
    A.map (Cotangent E) L K (Cotangent A.family) c v β a (m A)
    ((hβ A).2.2 c hc a ha)
  rw [hv A] at h
  exact h

/-- A global trivialization gives invertibility, also over the empty base. -/
lemma invertible_of_trivialization {M : S.Modules} (e : M ≅ 𝟙_ S.Modules) :
    Scheme.Modules.IsInvertible M := by
  constructor
  intro x
  refine ⟨⊤, trivial, ⟨?_⟩⟩
  exact (pullback (⊤ : S.Opens).ι).mapIso e ≪≫ pullbackUnitIso _

include k σ in
lemma descends_unique {L : S.Modules} (m : Frames E P L)
    (hL : Scheme.Modules.IsInvertible (productLine E L))
    (β γ : Γ(productLine E L, ⊤))
    (hβ : Descends E P L m β) (hγ : Descends E P L m γ) : β = γ := by
  obtain ⟨D, hD, hgeom⟩ := (unphased_marking_cover k S σ E P).1
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  let A := MultiplierProof.coverTest E P D hD
  let c := MultiplierProof.comparison E P A
  let a := MultiplierProof.alpha E P k σ A
  have hc := MultiplierProof.comparison_spec E P A
  have ha := MultiplierProof.alpha_spec E P k σ A
  apply AlphaDescentFaithfulness.pullback_section_injective D.projection hL
  apply (ConcreteCategory.bijective_of_isIso
    ((pullback_sheafTensor_iso A.base S A.map (Cotangent E) L ≪≫
      sheafTensorCongr A.base c (Iso.refl _)).hom.app ⊤)).1
  exact ((hβ A).2.2 c hc a ha).trans ((hγ A).2.2 c hc a ha).symm

end ArithmeticThetaPhaseFreeKeyR0219.AlphaProof

namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaPullback
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Intrinsic alpha tensored with every inverse-character frame descends uniquely
without a chosen phase, and the resulting section is nowhere vanishing. -/
theorem phase_free_alpha_descent :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
      (E : Family S) (P : EvenPoint E),
      ∀ (L : S.Modules) (m : Frames E P L), IsMultiplier E P L m →
        (∃! β : Γ(productLine E L, ⊤), Descends E P L m β) ∧
        (∀ β : Γ(productLine E L, ⊤), Descends E P L m β →
          IsFrame (productLine E L) ⊤ β) := by
  intro k _ _ S σ E P L m hm
  obtain ⟨v, hv⟩ := MultiplierProof.multiplier_iso_exists E P k σ
    (MultiplierProof.frames E P k σ) m (MultiplierProof.constructed_multiplier E P k σ) hm
  let t := sheafTensorCongr S (Iso.refl (Cotangent E)) v
  let β := t.hom.app ⊤ (AlphaProof.canonicalSection E)
  have hβ : Descends E P L m β := AlphaProof.descends_transport E P
    (MultiplierProof.frames E P k σ) m v hv _ (AlphaProof.canonical_descends E P k σ)
  have hf : IsFrame (productLine E L) ⊤ β :=
    frame_iso t _ (AlphaProof.canonicalSection_frame E)
  have hL := AlphaProof.invertible_of_trivialization (t.symm ≪≫ AlphaProof.evaluationIso E)
  have hu : ∀ γ : Γ(productLine E L, ⊤), Descends E P L m γ → γ = β :=
    fun γ hγ => AlphaProof.descends_unique E P k σ m hL γ β hγ hβ
  exact ⟨⟨β, hβ, hu⟩, fun γ hγ => (hu γ hγ) ▸ hf⟩

#print axioms phase_free_alpha_descent
end ArithmeticThetaPhaseFreeKeyR0219

