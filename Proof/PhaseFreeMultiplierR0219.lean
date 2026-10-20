module

public import UnphasedMarkingCoverR0219
public import PhaseOverlapSplittingR0219
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj

@[expose] public section

/-! The intrinsic alpha frame on every marked test, transported through the
actual identity-ideal comparison. All helpers are specific to this module. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219.MultiplierProof
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaPullback
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

lemma cotangent_invertible : Scheme.Modules.IsInvertible (Cotangent E) :=
  Scheme.Modules.IsInvertible.pullback E.zero
    (CartesianIdentityIdeal.zero_ideal_invertible E).isInvertible_module

/-- The proposed line is the actual internal-Hom dual of the identity cotangent. -/
abbrev line : S.Modules := Scheme.Modules.dual (Cotangent E)

lemma line_invertible : Scheme.Modules.IsInvertible (line E) :=
  (cotangent_invertible E).dual.1

lemma comparison_exists (A : MarkedTest E P) :
    ∃! c : (Scheme.Modules.pullback A.map).obj (Cotangent E) ≅ Cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c := by
  obtain ⟨i, hi, hu⟩ := cartesian_identity_ideal S A.base E A.family A.map
    A.comparison A.cartesian.1 A.cartesian.2.1
  refine ⟨cotangentComparison E A.family A.map A.comparison A.cartesian.2.1 i,
    ⟨i, hi, rfl⟩, ?_⟩
  rintro e ⟨j, hj, rfl⟩
  rw [hu j hj]

def comparison (A : MarkedTest E P) :
    (Scheme.Modules.pullback A.map).obj (Cotangent E) ≅ Cotangent A.family :=
  (comparison_exists E P A).choose

lemma comparison_spec (A : MarkedTest E P) :
    CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1
      (comparison E P A) := (comparison_exists E P A).choose_spec.1

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)

def alpha (A : MarkedTest E P) : Γ(Cotangent A.family, ⊤) :=
  (scheme_alpha_section k A.base (A.map ≫ σ) A.family A.marking).1.choose

lemma alpha_spec (A : MarkedTest E P) :
    RealizesAlpha A.family A.marking (alpha E P k σ A) :=
  (scheme_alpha_section k A.base (A.map ≫ σ) A.family A.marking).1.choose_spec.1

def pulledAlpha (A : MarkedTest E P) :
    Γ((Scheme.Modules.pullback A.map).obj (Cotangent E), ⊤) :=
  (comparison E P A).inv.app ⊤ (alpha E P k σ A)

lemma pulledAlpha_frame (A : MarkedTest E P) :
    IsFrame ((Scheme.Modules.pullback A.map).obj (Cotangent E)) ⊤
      (pulledAlpha E P k σ A) := by
  apply frame_iso (comparison E P A).symm
  exact (scheme_alpha_section k A.base (A.map ≫ σ) A.family A.marking).2 _
    (alpha_spec E P k σ A)

lemma comparison_remark (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) :
    comparison E P (remark E P A N hN) = comparison E P A := by
  exact (comparison_exists E P A).unique
    (comparison_spec E P (remark E P A N hN)) (comparison_spec E P A)

lemma pulledAlpha_character (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (g : ArithmeticThetaFourTorsion.Mat4) (hg : ArithmeticThetaFourTorsion.PreservesEven g)
    (hchange : Changes A.family A.marking N g) :
    pulledAlpha E P k σ (remark E P A N hN) =
      z ^ (ArithmeticThetaFourTorsion.characterExponent g).val • pulledAlpha E P k σ A := by
  have h := SchemeAlphaCharacter.section_character A.family A.marking k (A.map ≫ σ)
    N g hg hchange z hz (alpha E P k σ A) (alpha E P k σ (remark E P A N hN))
    (alpha_spec E P k σ A) (alpha_spec E P k σ (remark E P A N hN))
  dsimp only [pulledAlpha]
  rw [comparison_remark, h, Scheme.Modules.Hom.app_smul]
  rfl

lemma pulledAlpha_reversal (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val)
    (hchange : Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal) :
    pulledAlpha E P k σ (remark E P A N hN) = pulledAlpha E P k σ A := by
  have h := ((ArithmeticThetaPhaseSwitchR0218.scheme_pairing_reversal
    k A.base (A.map ≫ σ) A.family A.marking).2 N hchange).2.2.2
  have ha : alpha E P k σ (remark E P A N hN) = alpha E P k σ A :=
    (scheme_alpha_section k A.base (A.map ≫ σ) A.family N).1.unique
      (alpha_spec E P k σ (remark E P A N hN))
      ((h _).mp (alpha_spec E P k σ A))
  dsimp only [pulledAlpha]
  rw [comparison_remark, ha]
  rfl

lemma compatible_congr {T : Scheme.{u}} (F : Family T)
    (b b' : T ⟶ S) (f f' : F.curve ⟶ E.curve) (hb : b' = b) (hf : f' = f)
    (hz : F.zero ≫ f = b ≫ E.zero) (hz' : F.zero ≫ f' = b' ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hz e) :
    CotangentCompatible E F b' f' hz'
      ((Scheme.Modules.pullbackCongr hb).app (Cotangent E) ≪≫ e) := by
  subst b'; subst f'
  change CotangentCompatible E F b f hz e at he
  change CotangentCompatible E F b f hz ((Iso.refl _) ≪≫ e)
  simpa using he

lemma comparison_test (A B : MarkedTest E P) (H : TestMap E P A B)
    (c : (Scheme.Modules.pullback H.map).obj (Cotangent B.family) ≅ Cotangent A.family)
    (hc : CotangentCompatible B.family A.family H.map H.familyMap H.marked.2.1 c) :
    (Scheme.Modules.pullback H.map).map (comparison E P B).hom ≫ c.hom =
      (((Scheme.Modules.pullbackComp H.map B.map).app (Cotangent E)) ≪≫
        (Scheme.Modules.pullbackCongr H.commutes).app (Cotangent E)).hom ≫
          (comparison E P A).hom := by
  have hz : A.family.zero ≫ (H.familyMap ≫ B.comparison) =
      (H.map ≫ B.map) ≫ E.zero := by
    rw [H.triangle, H.commutes]
    exact A.cartesian.2.1
  exact scheme_cotangent_coherence.2 S B.base A.base E B.family A.family B.map H.map
    B.comparison H.familyMap B.cartesian.2.1 H.marked.2.1 hz
    (comparison E P B) c
    ((Scheme.Modules.pullbackCongr H.commutes).app (Cotangent E) ≪≫ comparison E P A)
    (comparison_spec E P B) hc
    (compatible_congr E A.family _ _ _ _ H.commutes H.triangle _ hz
      (comparison E P A) (comparison_spec E P A))

lemma pulledAlpha_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    testPull E P (Cotangent E) H (pulledAlpha E P k σ B) = pulledAlpha E P k σ A := by
  obtain ⟨c, hc, _⟩ := SchemeAlphaNaturality.cotangent_exists_unique
    B.family A.family B.marking A.marking H.map H.familyMap H.marked
  have hn := (scheme_alpha_naturality k B.base (B.map ≫ σ) B.family B.marking
    A.base (H.map ≫ (B.map ≫ σ)) A.family A.marking H.map H.familyMap rfl H.marked).2
    c hc (alpha E P k σ B) (alpha E P k σ A)
    (alpha_spec E P k σ B) (alpha_spec E P k σ A)
  apply (ConcreteCategory.bijective_of_isIso ((comparison E P A).hom.app ⊤)).1
  have h := congrArg (fun f => f.app ⊤
    (pullbackGlobalSection H.map _ (pulledAlpha E P k σ B)))
    (comparison_test E P A B H c hc)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  change c.hom.app ⊤
    (((Scheme.Modules.pullback H.map).map (comparison E P B).hom).app ⊤
      (pullbackGlobalSection H.map _ (pulledAlpha E P k σ B))) =
      (comparison E P A).hom.app ⊤ (testPull E P (Cotangent E) H (pulledAlpha E P k σ B)) at h
  rw [← h]
  rw [MultiplierBaseChange.global_app]
  have hb : (comparison E P B).hom.app ⊤ (pulledAlpha E P k σ B) =
      alpha E P k σ B := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.app ⊤) (comparison E P B).inv_hom_id) _
  have ha : (comparison E P A).hom.app ⊤ (pulledAlpha E P k σ A) =
      alpha E P k σ A := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.app ⊤) (comparison E P A).inv_hom_id) _
  rw [hb, ha]
  exact hn

open Scheme.Modules
open InverseCharacterMultiplier
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Duality with a global frame is characterized by evaluation equal to one. -/
lemma dual_frame_exists {X : Scheme.{u}} (M : X.Modules)
    (a : Γ(M, ⊤)) (ha : IsFrame M ⊤ a) :
    ∃ t : Γ(dual M, ⊤), IsFrame (dual M) ⊤ t ∧
      ihomEval M (𝟙_ X.Modules) ⊤ a t = (1 : Γ(X, ⊤)) := by
  obtain ⟨e, he⟩ := exists_frame_iso M a ha
  refine ⟨(ihomGlobalSectionsEquiv M _).symm e.inv,
    ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.dual_frame M e.hom e.inv
      e.hom_inv_id, ?_⟩
  rw [ihomEval_ihomGlobalSectionsEquiv_symm, ← he]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤) e.hom_inv_id) _

lemma dual_eval_injective {X : Scheme.{u}} (M : X.Modules)
    (a : Γ(M, ⊤)) (ha : IsFrame M ⊤ a) :
    Function.Injective (ihomEval M (𝟙_ X.Modules) ⊤ a) := by
  intro t t' h
  apply (ihomGlobalSectionsEquiv M _).injective
  apply hom_ext_of_frame a ha
  simp only [ihomGlobalSectionsEquiv_app_apply]
  change ihomEval M (𝟙_ X.Modules) ⊤ a (((dual M).presheaf.map (𝟙 _)) t) =
    ihomEval M (𝟙_ X.Modules) ⊤ a (((dual M).presheaf.map (𝟙 _)) t')
  simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using h

def dualFrame {X : Scheme.{u}} (M : X.Modules)
    (a : Γ(M, ⊤)) (ha : IsFrame M ⊤ a) : Γ(dual M, ⊤) :=
  (dual_frame_exists M a ha).choose

lemma dualFrame_frame {X : Scheme.{u}} (M : X.Modules)
    (a : Γ(M, ⊤)) (ha : IsFrame M ⊤ a) :
    IsFrame (dual M) ⊤ (dualFrame M a ha) :=
  (dual_frame_exists M a ha).choose_spec.1

lemma dualFrame_eval {X : Scheme.{u}} (M : X.Modules)
    (a : Γ(M, ⊤)) (ha : IsFrame M ⊤ a) :
    ihomEval M (𝟙_ X.Modules) ⊤ a (dualFrame M a ha) = (1 : Γ(X, ⊤)) :=
  (dual_frame_exists M a ha).choose_spec.2

def dualComparisonIso (A : MarkedTest E P) :
    (Scheme.Modules.pullback A.map).obj (line E) ≅ dual ((Scheme.Modules.pullback A.map).obj (Cotangent E)) := by
  letI := dualComparison_isIso A.map (Cotangent E) (cotangent_invertible E)
  exact asIso (dualComparison A.map (Cotangent E))

def frames : Frames E P (line E) := fun A =>
  (dualComparisonIso E P A).inv.app ⊤
    (dualFrame _ (pulledAlpha E P k σ A) (pulledAlpha_frame E P k σ A))

lemma frames_frame (A : MarkedTest E P) :
    IsFrame ((Scheme.Modules.pullback A.map).obj (line E)) ⊤ (frames E P k σ A) :=
  frame_iso (dualComparisonIso E P A).symm _
    (dualFrame_frame _ (pulledAlpha E P k σ A) (pulledAlpha_frame E P k σ A))

lemma frames_eval (A : MarkedTest E P) :
    ihomEval ((Scheme.Modules.pullback A.map).obj (Cotangent E)) (𝟙_ A.base.Modules) ⊤
      (pulledAlpha E P k σ A)
      ((dualComparisonIso E P A).hom.app ⊤ (frames E P k σ A)) =
        (1 : Γ(A.base, ⊤)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app ⊤) (dualComparisonIso E P A).inv_hom_id)
    (dualFrame _ (pulledAlpha E P k σ A) (pulledAlpha_frame E P k σ A))
  change (dualComparisonIso E P A).hom.app ⊤ (frames E P k σ A) = _ at h
  simp only [Hom.id_app, ConcreteCategory.id_apply] at h
  rw [h]
  exact dualFrame_eval _ _ (pulledAlpha_frame E P k σ A)

lemma frames_ext (A : MarkedTest E P) (s t : Γ((Scheme.Modules.pullback A.map).obj (line E), ⊤))
    (h : ihomEval ((Scheme.Modules.pullback A.map).obj (Cotangent E)) (𝟙_ A.base.Modules) ⊤
      (pulledAlpha E P k σ A) ((dualComparisonIso E P A).hom.app ⊤ s) =
      ihomEval ((Scheme.Modules.pullback A.map).obj (Cotangent E)) (𝟙_ A.base.Modules) ⊤
      (pulledAlpha E P k σ A) ((dualComparisonIso E P A).hom.app ⊤ t)) : s = t :=
  (ConcreteCategory.bijective_of_isIso ((dualComparisonIso E P A).hom.app ⊤)).1
    (dual_eval_injective _ _ (pulledAlpha_frame E P k σ A) h)

lemma frames_character (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (g : ArithmeticThetaFourTorsion.Mat4) (hg : ArithmeticThetaFourTorsion.PreservesEven g)
    (hchange : Changes A.family A.marking N g) :
    frames E P k σ (remark E P A N hN) =
      z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) • frames E P k σ A := by
  apply frames_ext E P k σ (remark E P A N hN)
  rw [frames_eval, pulledAlpha_character E P k σ A N hN z hz g hg hchange,
    Hom.app_smul, ihomEval_smul_left, ihomEval_smul_right]
  change (1 : Γ(A.base, ⊤)) = z ^ (ArithmeticThetaFourTorsion.characterExponent g).val •
    (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) •
      ihomEval ((Scheme.Modules.pullback A.map).obj (Cotangent E)) (𝟙_ A.base.Modules) ⊤
        (pulledAlpha E P k σ A) ((dualComparisonIso E P A).hom.app ⊤ (frames E P k σ A)))
  rw [frames_eval]
  change (1 : Γ(A.base, ⊤)) = z ^ (ArithmeticThetaFourTorsion.characterExponent g).val *
    (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) * 1)
  rw [mul_one, mul_comm]
  exact (inverse_character_mul z
    ((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).2 z hz).2.1 _).symm

lemma frames_reversal (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val)
    (hchange : Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal) :
    frames E P k σ (remark E P A N hN) = frames E P k σ A := by
  apply frames_ext E P k σ (remark E P A N hN)
  rw [frames_eval, pulledAlpha_reversal E P k σ A N hN hchange]
  exact (frames_eval E P k σ A).symm

#print axioms pulledAlpha_natural
#print axioms frames_character
#print axioms frames_reversal

/-- The universal unphased cover is itself one of the tests in the predicate. -/
def coverTest (D : Cover E) (hD : RepresentsUnphased E P D) : MarkedTest E P :=
  ⟨D.space, D.family, D.marking, D.projection, D.comparison, D.cartesian, hD.1⟩

lemma preservesFrames_of_cover (D : Cover E) (hD : RepresentsUnphased E P D)
    {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
    (hm : IsMultiplier E P L m) (hn : IsMultiplier E P K n) (v : L ≅ K)
    (hv : ((Scheme.Modules.pullback D.projection).map v.hom).app ⊤ (m (coverTest E P D hD)) =
      n (coverTest E P D hD)) : PreservesFrames E P m n v := by
  intro A
  obtain ⟨q, ⟨f, hf, ht⟩, _⟩ := hD.2 A
  let H : TestMap E P A (coverTest E P D hD) := ⟨q.val, q.property, f, hf, ht⟩
  rw [← hm.2.2.1 A _ H]
  have h := ArithmeticThetaPhaseSwitchR0218.MultiplierPhaseSwitch.along_natural
    A.map D.projection q.val q.property v.hom (m (coverTest E P D hD))
  change ((Scheme.Modules.pullback A.map).map v.hom).app ⊤
    (testPull E P L H (m (coverTest E P D hD))) =
    testPull E P K H (((Scheme.Modules.pullback D.projection).map v.hom).app ⊤
      (m (coverTest E P D hD))) at h
  rw [h, hv]
  exact hn.2.2.1 A _ H

include k σ in
/-- Faithfulness on the degree-32 cover proves the uniqueness part independently
of how the line and comparison are constructed. -/
lemma frame_preserving_unique {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
    (hm : IsMultiplier E P L m) (hn : IsMultiplier E P K n)
    (v w : L ≅ K) (hv : PreservesFrames E P m n v)
    (hw : PreservesFrames E P m n w) : v = w := by
  obtain ⟨D, hD, hgeom⟩ := (unphased_marking_cover k S σ E P).1
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  apply Iso.ext
  apply AlphaDescentFaithfulness.pullback_hom_injective D.projection hm.1 hn.1
  exact hom_ext_of_frame (m (coverTest E P D hD)) (hm.2.1 _) _ _
    ((hv _).trans (hw _).symm)

#print axioms frame_preserving_unique

open ArithmeticThetaPolygonCartierR0133

lemma tensor_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) :
    (((pullbackComp f g).app M).hom ⊗ₘ ((pullbackComp f g).app N).hom) ≫
      (pullbackTensorObjIso (f ≫ g) M N).inv =
    (pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).inv ≫
      (Scheme.Modules.pullback f).map (pullbackTensorObjIso g M N).inv ≫
        ((pullbackComp f g).app (M ⊗ N)).hom := by
  have h := congrArg Iso.hom (pullbackComp_app_tensorObj f g M N)
  have h' := congrArg (fun q =>
    (pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).inv ≫
      (Scheme.Modules.pullback f).map (pullbackTensorObjIso g M N).inv ≫ q) h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorIso_hom, ← Functor.map_comp_assoc, Iso.inv_hom_id] at h'
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc] at h'
  exact h'.symm

def pairing {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj (dual M) ⟶ 𝟙_ X.Modules :=
  (pullbackTensorObjIso f M (dual M)).inv ≫
    (Scheme.Modules.pullback f).map ((ihom.ev M).app (𝟙_ Y.Modules)) ≫ unitPullback f

lemma pairing_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (((pullbackComp f g).app M).hom ⊗ₘ ((pullbackComp f g).app (dual M)).hom) ≫
      pairing (f ≫ g) M =
    (pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj (dual M))).inv ≫
      (Scheme.Modules.pullback f).map (pairing g M) ≫ unitPullback f := by
  dsimp only [pairing]
  rw [← Category.assoc, tensor_comp_inv]
  simp only [Category.assoc, Functor.map_comp]
  have hu := pullbackComp_hom_app_comp_pullbackUnitIso_hom f g
  change ((pullbackComp f g).app (𝟙_ Z.Modules)).hom ≫ unitPullback (f ≫ g) =
    (Scheme.Modules.pullback f).map (unitPullback g) ≫ unitPullback f at hu
  have hn := congrArg (fun t => t ≫ unitPullback (f ≫ g))
    ((pullbackComp f g).hom.naturality ((ihom.ev M).app (𝟙_ Z.Modules))).symm
  simp only [Category.assoc] at hn
  erw [hu] at hn
  exact congrArg (fun t =>
    (pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj (dual M))).inv ≫
      (Scheme.Modules.pullback f).map (pullbackTensorObjIso g M (dual M)).inv ≫ t) hn

#print axioms pairing_comp

lemma tensorHom_sections {X : Scheme.{u}} {M N M' N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (a : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    (f ⊗ₘ g).app ⊤ (tensorSections a t) = tensorSections (f.app ⊤ a) (g.app ⊤ t) := by
  exact SheafOfModules.tensorHom_val_app_tmulSection _ _ _ _ _ _ _

lemma pairing_eval {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (a : Γ((Scheme.Modules.pullback f).obj M, ⊤)) (t : Γ((Scheme.Modules.pullback f).obj (dual M), ⊤)) :
    ihomEval ((Scheme.Modules.pullback f).obj M) (𝟙_ X.Modules) ⊤ a ((dualComparison f M).app ⊤ t) =
      (pairing f M).app ⊤ (tensorSections a t) :=
  ihomEval_curry_app (pairing f M) ⊤ a t

lemma pairing_comp_sections {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (a : Γ((Scheme.Modules.pullback g).obj M, ⊤))
    (t : Γ((Scheme.Modules.pullback g).obj (dual M), ⊤)) :
    (pairing (f ≫ g) M).app ⊤
      (tensorSections (((pullbackComp f g).app M).hom.app ⊤ (pullbackGlobalSection f _ a))
        (((pullbackComp f g).app (dual M)).hom.app ⊤ (pullbackGlobalSection f _ t))) =
      f.appTop ((pairing g M).app ⊤ (tensorSections a t)) := by
  have h := congrArg (fun q => q.app ⊤
    (tensorSections (pullbackGlobalSection f _ a) (pullbackGlobalSection f _ t)))
    (pairing_comp f g M)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_sections] at h
  rw [h]
  have ht : (pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj (dual M))).hom.app ⊤
      (pullbackGlobalSection f _ (tensorSections a t)) =
      tensorSections (pullbackGlobalSection f _ a) (pullbackGlobalSection f _ t) :=
    pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 f a t
  rw [← ht]
  erw [MultiplierBaseChange.iso_inv_hom_section, MultiplierBaseChange.global_app]
  exact unitPullback_app f ⊤ _

#print axioms pairing_comp_sections

lemma pairing_along {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Z) (hp : f ≫ g = p) (M : Z.Modules)
    (a : Γ((Scheme.Modules.pullback g).obj M, ⊤)) (t : Γ((Scheme.Modules.pullback g).obj (dual M), ⊤)) :
    ihomEval ((Scheme.Modules.pullback p).obj M) (𝟙_ X.Modules) ⊤
      (ArithmeticThetaPhaseSwitchR0218.MultiplierPhaseSwitch.along p g f hp M a)
      ((dualComparison p M).app ⊤
        (ArithmeticThetaPhaseSwitchR0218.MultiplierPhaseSwitch.along p g f hp (dual M) t)) =
    f.appTop (ihomEval ((Scheme.Modules.pullback g).obj M) (𝟙_ Y.Modules) ⊤ a
      ((dualComparison g M).app ⊤ t)) := by
  subst p
  rw [pairing_eval, pairing_eval]
  simpa only [ArithmeticThetaPhaseSwitchR0218.MultiplierPhaseSwitch.along,
    P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules.τ,
    pullbackCongr, eqToIso_refl, Iso.refl_hom, Iso.trans_hom, NatTrans.comp_app,
    Category.comp_id, Iso.app_hom] using pairing_comp_sections f g M a t

lemma frames_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    testPull E P (line E) H (frames E P k σ B) = frames E P k σ A := by
  apply frames_ext E P k σ A
  rw [frames_eval]
  have h := pairing_along H.map B.map A.map H.commutes (Cotangent E)
    (pulledAlpha E P k σ B) (frames E P k σ B)
  change ihomEval ((Scheme.Modules.pullback A.map).obj (Cotangent E)) (𝟙_ A.base.Modules) ⊤
      (testPull E P (Cotangent E) H (pulledAlpha E P k σ B))
      ((dualComparisonIso E P A).hom.app ⊤ (testPull E P (line E) H (frames E P k σ B))) =
    H.map.appTop (ihomEval ((Scheme.Modules.pullback B.map).obj (Cotangent E)) (𝟙_ B.base.Modules) ⊤
      (pulledAlpha E P k σ B) ((dualComparisonIso E P B).hom.app ⊤ (frames E P k σ B))) at h
  rw [pulledAlpha_natural, frames_eval, map_one] at h
  exact h

theorem constructed_multiplier : IsMultiplier E P (line E) (frames E P k σ) :=
  ⟨line_invertible E, frames_frame E P k σ, frames_natural E P k σ,
    frames_character E P k σ, frames_reversal E P k σ⟩

#print axioms constructed_multiplier

section ComparisonDescent
variable {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
  (hm : IsMultiplier E P L m) (hn : IsMultiplier E P K n)

def testIso (A : MarkedTest E P) : (Scheme.Modules.pullback A.map).obj L ≅ (Scheme.Modules.pullback A.map).obj K :=
  (existsUnique_frame_iso _ _ (m A) (n A) (hm.2.1 A) (hn.2.1 A)).choose

lemma testIso_spec (A : MarkedTest E P) :
    (testIso E P m n hm hn A).hom.app ⊤ (m A) = n A :=
  (existsUnique_frame_iso _ _ (m A) (n A) (hm.2.1 A) (hn.2.1 A)).choose_spec.1

lemma testIso_character (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (g : ArithmeticThetaFourTorsion.Mat4) (hg : ArithmeticThetaFourTorsion.PreservesEven g)
    (hchange : Changes A.family A.marking N g) :
    testIso E P m n hm hn (remark E P A N hN) = testIso E P m n hm hn A := by
  apply Iso.ext
  apply hom_ext_of_frame (m (remark E P A N hN)) (hm.2.1 _)
  erw [testIso_spec, hm.2.2.2.1 A N hN z hz g hg hchange,
    Hom.app_smul, testIso_spec, hn.2.2.2.1 A N hN z hz g hg hchange]

lemma testIso_reversal (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val)
    (hchange : Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal) :
    testIso E P m n hm hn (remark E P A N hN) = testIso E P m n hm hn A := by
  apply Iso.ext
  apply hom_ext_of_frame (m (remark E P A N hN)) (hm.2.1 _)
  erw [testIso_spec, hm.2.2.2.2 A N hN hchange, testIso_spec,
    hn.2.2.2.2 A N hN hchange]

lemma testIso_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    (Scheme.Modules.pullback H.map).map (testIso E P m n hm hn B).hom ≫
      (((pullbackComp H.map B.map).app K) ≪≫ (pullbackCongr H.commutes).app K).hom =
    (((pullbackComp H.map B.map).app L) ≪≫ (pullbackCongr H.commutes).app L).hom ≫
      (testIso E P m n hm hn A).hom := by
  apply hom_ext_of_frame (pullbackGlobalSection H.map _ (m B))
    (HodgeBaseChange.pullback_frame H.map _ _ (hm.2.1 B))
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [MultiplierBaseChange.global_app, testIso_spec]
  change testPull E P K H (n B) = (testIso E P m n hm hn A).hom.app ⊤
    (testPull E P L H (m B))
  rw [hm.2.2.1 A B H, hn.2.2.1 A B H, testIso_spec]

end ComparisonDescent

open CategoryTheory.Limits
open ArithmeticThetaUniversalEvaluationR0213

/-- Restriction of a marked test uses the actual Cartesian base-change family. -/
def restrictedFamily (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base) : Family T :=
  SchemeFamilyBaseChange.baseChangeFamily A.family b

lemma restrictedCartesian (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base) :
    Cartesian A.family (restrictedFamily E P A b) b (pullback.fst A.family.p b) :=
  ⟨IsPullback.of_hasPullback A.family.p b,
    SchemeFamilyBaseChange.baseChangeLaw_zero A.family b,
    SchemeFamilyBaseChange.baseChangeFamily_multiplicative A.family b⟩

def restrictedMarking (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base)
    (N : FullLevel A.family 4) : FullLevel (restrictedFamily E P A b) 4 :=
  CartesianFullMarking.up A.family (restrictedFamily E P A b) b (pullback.fst A.family.p b)
    (restrictedCartesian E P A b).1 (restrictedCartesian E P A b).2.1
    (restrictedCartesian E P A b).2.2 4 N

lemma restrictedMarked (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base)
    (N : FullLevel A.family 4) :
    MarkedCartesian A.family (restrictedFamily E P A b) N (restrictedMarking E P A b N)
      b (pullback.fst A.family.p b) :=
  ⟨(restrictedCartesian E P A b).1, (restrictedCartesian E P A b).2.1,
    (restrictedCartesian E P A b).2.2,
    CartesianFullMarking.lift_comp _ _ _ _ (restrictedCartesian E P A b).1 N.x,
    CartesianFullMarking.lift_comp _ _ _ _ (restrictedCartesian E P A b).1 N.y⟩

def restrictTest (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base) : MarkedTest E P where
  base := T
  family := restrictedFamily E P A b
  marking := restrictedMarking E P A b A.marking
  map := b ≫ A.map
  comparison := pullback.fst A.family.p b ≫ A.comparison
  cartesian := SchemeFourCover.cartesian_comp E A.family (restrictedFamily E P A b)
    A.map A.comparison A.cartesian b (pullback.fst A.family.p b) (restrictedCartesian E P A b)
  characteristic := by
    rw [← Category.assoc, SchemeThetaEvaluation.evenPoint_natural
      A.family A.marking (restrictedFamily E P A b) (restrictedMarking E P A b A.marking)
      b (pullback.fst A.family.p b) (restrictedMarked E P A b A.marking),
      Category.assoc, A.characteristic, Category.assoc]

def restrictionMap (A : MarkedTest E P) {T : Scheme.{u}} (b : T ⟶ A.base) :
    TestMap E P (restrictTest E P A b) A :=
  ⟨b, rfl, pullback.fst A.family.p b, restrictedMarked E P A b A.marking, rfl⟩

#print axioms testIso_natural
#print axioms restrictionMap

open ArithmeticThetaPhaseSwitchR0218
include k σ in
/-- Two phases are equal or opposite locally on actual open subschemes.
The sign can vary; equality is obtained from étale sections, not residue values alone. -/
lemma phases_locally_signed (z w : Γ(S, ⊤)) (hz : z ^ 2 = -1) (hw : w ^ 2 = -1)
    (s : S) : ∃ U : S.Opens, s ∈ U ∧
      (U.ι.appTop z = U.ι.appTop w ∨ U.ι.appTop z = -(U.ι.appTop w)) := by
  let Q := phaseSpace k S σ
  let p := phaseProjection k S σ
  let v := phaseValue k S σ
  letI : Etale p := (phase_cover k S σ).2.1
  obtain ⟨a, ha, _⟩ := PhaseCoverProof.represents k S σ S (𝟙 S) z hz
  obtain ⟨b, hb, _⟩ := PhaseCoverProof.represents k S σ S (𝟙 S) w hw
  obtain ⟨τ, hτ, _⟩ := PhaseCoverProof.involution k S σ
  let F := S.residueField s
  let q := S.fromSpecResidueField s
  let x : Spec F := Classical.choice inferInstance
  have hqx : q x = s := S.fromSpecResidueField_apply s x
  have hbase : (q ≫ a) ≫ p = (q ≫ b) ≫ p := by
    simp only [p, Category.assoc, ha.1, hb.1]
  rcases PhaseOverlapProof.field_sign k S σ (q ≫ a) (q ≫ b) hbase with he | he
  · have hepoint : a s = b s := by
      have h := congrArg (fun f : Spec F ⟶ Q => f x) he
      change a (q x) = b (q x) at h
      rw [hqx] at h
      exact h
    obtain ⟨U, hs, hU⟩ := LocallyConstantMarkingComparison.etale_sections_locally_equal
      p a b ha.1 hb.1 s hepoint
    refine ⟨U, hs, Or.inl ?_⟩
    have h := congrArg (fun f => f.appTop v) hU
    change U.ι.appTop (a.appTop v) = U.ι.appTop (b.appTop v) at h
    simpa only [v, ha.2, hb.2] using h
  · have heq : q ≫ a = q ≫ (b ≫ τ.hom) := by
      apply PhaseCoverProof.hom_ext k S σ
      · simpa only [Category.assoc, hτ.1] using hbase
      · change (q ≫ a).appTop v = q.appTop (b.appTop (τ.hom.appTop v))
        rw [show τ.hom.appTop v = -v from hτ.2, map_neg, map_neg]
        exact he
    have hbτ : (b ≫ τ.hom) ≫ p = 𝟙 S := by rw [Category.assoc, hτ.1, hb.1]
    have hepoint : a s = (b ≫ τ.hom) s := by
      have h := congrArg (fun f : Spec F ⟶ Q => f x) heq
      change a (q x) = (b ≫ τ.hom) (q x) at h
      rw [hqx] at h
      exact h
    obtain ⟨U, hs, hU⟩ := LocallyConstantMarkingComparison.etale_sections_locally_equal
      p a (b ≫ τ.hom) ha.1 hbτ s hepoint
    refine ⟨U, hs, Or.inr ?_⟩
    have h := congrArg (fun f => f.appTop v) hU
    change U.ι.appTop (a.appTop v) = U.ι.appTop (b.appTop (τ.hom.appTop v)) at h
    rw [show τ.hom.appTop v = -v from hτ.2, map_neg, map_neg] at h
    simpa only [v, ha.2, hb.2] using h

#print axioms phases_locally_signed

lemma restrictTest_remark (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    {T : Scheme.{u}} (b : T ⟶ A.base) :
    restrictTest E P (remark E P A N hN) b =
      remark E P (restrictTest E P A b) (restrictedMarking E P A b N)
        (restrictTest E P (remark E P A N hN) b).characteristic := rfl

lemma restrictedChanged (A : MarkedTest E P) (N : FullLevel A.family 4)
    {T : Scheme.{u}} (b : T ⟶ A.base) (g : ArithmeticThetaFourTorsion.Mat4)
    (hx : b ≫ N.x.val = b ≫ changedX A.family A.marking g)
    (hy : b ≫ N.y.val = b ≫ changedY A.family A.marking g) :
    Changes (restrictedFamily E P A b) (restrictedMarking E P A b A.marking)
      (restrictedMarking E P A b N) g := by
  have hc := restrictedCartesian E P A b
  have hn := restrictedMarked E P A b N
  have hg := EvenCoverRightAction.changed_comp A.family (restrictedFamily E P A b)
    A.marking (restrictedMarking E P A b A.marking) b (pullback.fst A.family.p b)
    (restrictedMarked E P A b A.marking) g
  constructor
  · apply Subtype.ext
    apply hc.1.hom_ext
    · exact hn.2.2.2.1.trans (hx.trans hg.1.symm)
    · exact (restrictedMarking E P A b N).x.property.trans
        (EvenCoverTorsor.changedX_over _ _ _).symm
  · apply Subtype.ext
    apply hc.1.hom_ext
    · exact hn.2.2.2.2.trans (hy.trans hg.2.symm)
    · exact (restrictedMarking E P A b N).y.property.trans
        (EvenCoverTorsor.changedY_over _ _ _).symm

section MarkingIndependence
variable {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
  (hm : IsMultiplier E P L m) (hn : IsMultiplier E P K n)

lemma testIso_restrict_eq (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    {T : Scheme.{u}} (b : T ⟶ A.base)
    (he : testIso E P m n hm hn (restrictTest E P A b) =
      testIso E P m n hm hn (restrictTest E P (remark E P A N hN) b)) :
    (Scheme.Modules.pullback b).map (testIso E P m n hm hn A).hom =
      (Scheme.Modules.pullback b).map (testIso E P m n hm hn (remark E P A N hN)).hom := by
  have h1 := testIso_natural E P m n hm hn _ A (restrictionMap E P A b)
  have h2 := testIso_natural E P m n hm hn _ (remark E P A N hN)
    (restrictionMap E P (remark E P A N hN) b)
  apply (cancel_mono (((pullbackComp b A.map).app K) ≪≫ (pullbackCongr rfl).app K).hom).mp
  change (Scheme.Modules.pullback b).map (testIso E P m n hm hn A).hom ≫
    (((pullbackComp b A.map).app K) ≪≫ (pullbackCongr rfl).app K).hom =
    (((pullbackComp b A.map).app L) ≪≫ (pullbackCongr rfl).app L).hom ≫
      (testIso E P m n hm hn (restrictTest E P A b)).hom at h1
  change (Scheme.Modules.pullback b).map (testIso E P m n hm hn (remark E P A N hN)).hom ≫
    (((pullbackComp b A.map).app K) ≪≫ (pullbackCongr rfl).app K).hom =
    (((pullbackComp b A.map).app L) ≪≫ (pullbackCongr rfl).app L).hom ≫
      (testIso E P m n hm hn (restrictTest E P (remark E P A N hN) b)).hom at h2
  rw [h1, h2, he]

include k σ in
lemma testIso_samePhase (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (hzN : MillerPhase A.family N z) :
    testIso E P m n hm hn A = testIso E P m n hm hn (remark E P A N hN) := by
  have hp : evenPoint A.family A.marking = evenPoint A.family N := by
    apply A.cartesian.1.hom_ext
    · exact A.characteristic.trans hN.symm
    · rw [SchemeThetaEvaluation.evenPoint_over, SchemeThetaEvaluation.evenPoint_over]
  apply Iso.ext
  apply hom_ext_local_pullback (m A) (hm.2.1 A)
  intro s
  obtain ⟨g, U, hs, hx, hy⟩ := LocallyConstantMarkingComparison.localWitness_exists
    A.family A.marking k (A.map ≫ σ) N z hz hzN hp s
  refine ⟨U, hs, testIso_restrict_eq E P m n hm hn A N hN U.ι ?_⟩
  change testIso E P m n hm hn (restrictTest E P A U.ι) =
    testIso E P m n hm hn (remark E P (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N)
      (restrictTest E P (remark E P A N hN) U.ι).characteristic)
  symm
  exact testIso_character E P m n hm hn (restrictTest E P A U.ι)
    (restrictedMarking E P A U.ι N) _ (U.ι.appTop z)
    (SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
      A.marking (restrictedMarking E P A U.ι A.marking) U.ι (pullback.fst A.family.p U.ι)
      (restrictedMarked E P A U.ι A.marking) z hz)
    g.val g.property (restrictedChanged E P A N U.ι g.val hx hy)

include k σ in
lemma testIso_oppositePhase (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (hzN : MillerPhase A.family N (-z)) :
    testIso E P m n hm hn A = testIso E P m n hm hn (remark E P A N hN) := by
  obtain ⟨R, hR, _⟩ := (scheme_pairing_reversal k A.base (A.map ≫ σ) A.family N).1
  have hr := (scheme_pairing_reversal k A.base (A.map ≫ σ) A.family N).2 R hR
  have hRchar : evenPoint A.family R ≫ A.comparison = A.map ≫ P.point.val := by
    rw [hr.2.1, hN]
  have hphase : MillerPhase A.family R z := by simpa only [neg_neg] using hr.2.2.1 (-z) hzN
  have h1 := testIso_samePhase E P k σ m n hm hn A R hRchar z hz hphase
  have h2 := testIso_reversal E P m n hm hn (remark E P A N hN) R hRchar hR
  exact h1.trans h2

include k σ in
/-- Comparisons are independent of the marking, including locally varying phase signs. -/
lemma testIso_marking_independent (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val) :
    testIso E P m n hm hn A = testIso E P m n hm hn (remark E P A N hN) := by
  obtain ⟨z, hz, _⟩ := (scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).1
  obtain ⟨w, hw, _⟩ := (scheme_miller_phase k A.base (A.map ≫ σ) A.family N).1
  have hz2 := ((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).2 z hz).2.1
  have hw2 := ((scheme_miller_phase k A.base (A.map ≫ σ) A.family N).2 w hw).2.1
  apply Iso.ext
  apply hom_ext_local_pullback (m A) (hm.2.1 A)
  intro s
  obtain ⟨U, hs, hsign⟩ := phases_locally_signed k (A.map ≫ σ) z w hz2 hw2 s
  refine ⟨U, hs, testIso_restrict_eq E P m n hm hn A N hN U.ι ?_⟩
  change testIso E P m n hm hn (restrictTest E P A U.ι) =
    testIso E P m n hm hn (remark E P (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N)
      (restrictTest E P (remark E P A N hN) U.ι).characteristic)
  have hza := SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
    A.marking (restrictedMarking E P A U.ι A.marking) U.ι (pullback.fst A.family.p U.ι)
    (restrictedMarked E P A U.ι A.marking) z hz
  have hwa := SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
    N (restrictedMarking E P A U.ι N) U.ι (pullback.fst A.family.p U.ι)
    (restrictedMarked E P A U.ι N) w hw
  rcases hsign with hpos | hneg
  · rw [← hpos] at hwa
    exact testIso_samePhase E P k σ m n hm hn (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N) _ (U.ι.appTop z) hza hwa
  · have he : U.ι.appTop w = -(U.ι.appTop z) := by rw [hneg, neg_neg]
    rw [he] at hwa
    exact testIso_oppositePhase E P k σ m n hm hn (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N) _ (U.ι.appTop z) hza hwa

end MarkingIndependence
#print axioms testIso_samePhase
#print axioms testIso_marking_independent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2

section FinalDescent
variable {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
  (hm : IsMultiplier E P L m) (hn : IsMultiplier E P K n)

lemma testIso_pullHom (A B : MarkedTest E P) (H : TestMap E P A B) :
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K) (f₁ := B.map) (f₂ := B.map)
      (testIso E P m n hm hn B).hom H.map A.map A.map H.commutes H.commutes =
      (testIso E P m n hm hn A).hom := by
  rw [pullHom_eq₂]
  have h := congrArg (fun v =>
    (((pullbackComp H.map B.map).app L) ≪≫ (pullbackCongr H.commutes).app L).inv ≫ v)
    (testIso_natural E P m n hm hn A B H)
  simp only [Iso.inv_hom_id_assoc] at h
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc] at h
  exact h

include k σ in
lemma testIso_pair_eq (D : Cover E) (hD : RepresentsUnphased E P D) :
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection)
      (testIso E P m n hm hn (coverTest E P D hD)).hom
      (first E D) (first E D ≫ D.projection) (first E D ≫ D.projection) rfl rfl =
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection)
      (testIso E P m n hm hn (coverTest E P D hD)).hom
      (second E D) (first E D ≫ D.projection) (first E D ≫ D.projection)
      pullback.condition.symm pullback.condition.symm := by
  let T := overlap E D
  let b := first E D ≫ D.projection
  obtain ⟨F, f, hpb, hz, hmul⟩ := scheme_family_base_change S T E b
  have hc : Cartesian E F b f := ⟨hpb, hz, hmul⟩
  obtain ⟨M, g, hg, hgf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D F b f hc
    (first E D) rfl
  obtain ⟨N, j, hj, hjf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D F b f hc
    (second E D) pullback.condition.symm
  have char (Q : FullLevel F 4) (a : T ⟶ D.space) (ha : a ≫ D.projection = b)
      (v : F.curve ⟶ D.family.curve) (hv : MarkedCartesian D.family F D.marking Q a v)
      (hvc : v ≫ D.comparison = f) : evenPoint F Q ≫ f = b ≫ P.point.val := by
    rw [← hvc, ← Category.assoc, SchemeThetaEvaluation.evenPoint_natural D.family D.marking F Q a v hv,
      Category.assoc, hD.1, ← Category.assoc, ha]
  have hM := char M (first E D) rfl g hg hgf
  have hN := char N (second E D) pullback.condition.symm j hj hjf
  let A : MarkedTest E P := ⟨T, F, M, b, f, hc, hM⟩
  let B : MarkedTest E P := remark E P A N hN
  let H₁ : TestMap E P A (coverTest E P D hD) := ⟨first E D, rfl, g, hg, hgf⟩
  let H₂ : TestMap E P B (coverTest E P D hD) :=
    ⟨second E D, pullback.condition.symm, j, hj, hjf⟩
  exact (testIso_pullHom E P m n hm hn A _ H₁).trans
    ((congrArg Iso.hom (testIso_marking_independent E P k σ m n hm hn A N hN)).trans
      (testIso_pullHom E P m n hm hn B _ H₂).symm)

include k σ hm hn in
/-- The frame comparison satisfies the complete Čech compatibility equation and
therefore descends along the actual finite étale unphased marking cover. -/
theorem multiplier_iso_exists : ∃ v : L ≅ K, PreservesFrames E P m n v := by
  obtain ⟨D, hD, hgeom⟩ := (unphased_marking_cover k S σ E P).1
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  let η := testIso E P m n hm hn (coverTest E P D hD)
  have hη := compatible_of_pair_eq E D η (testIso_pair_eq E P k σ m n hm hn D hD)
  obtain ⟨v, hv, _⟩ :=
    P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one.KcDescAlong.existsUnique_of_comm
      D.projection (first E D) (second E D) (IsPullback.of_hasPullback _ _) hm.1 hn.1 η hη
  refine ⟨v, preservesFrames_of_cover E P D hD m n hm hn v ?_⟩
  have h := congrArg (fun e => e.hom.app ⊤ (m (coverTest E P D hD))) hv
  exact h.trans (testIso_spec E P m n hm hn (coverTest E P D hD))

end FinalDescent
#print axioms multiplier_iso_exists

end ArithmeticThetaPhaseFreeKeyR0219.MultiplierProof

namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216

/-- The inverse-character multiplier exists without a phase on the base and is
unique up to the unique isomorphism preserving every actual marked-test frame. -/
theorem phase_free_multiplier :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
      (E : Family S) (P : EvenPoint E),
      ∃ (L : S.Modules) (m : Frames E P L), IsMultiplier E P L m ∧
        (∀ (K : S.Modules) (n : Frames E P K), IsMultiplier E P K n →
          ∃! v : L ≅ K, PreservesFrames E P m n v) := by
  intro k _ _ S σ E P
  let m := MultiplierProof.frames E P k σ
  have hm := MultiplierProof.constructed_multiplier E P k σ
  refine ⟨MultiplierProof.line E, m, hm, ?_⟩
  intro K n hn
  obtain ⟨v, hv⟩ := MultiplierProof.multiplier_iso_exists E P k σ m n hm hn
  exact ⟨v, hv, fun w hw => MultiplierProof.frame_preserving_unique E P k σ m n hm hn w v hw hv⟩

#print axioms phase_free_multiplier
end ArithmeticThetaPhaseFreeKeyR0219
