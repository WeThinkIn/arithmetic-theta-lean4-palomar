import EvenKeyIsomorphismR0217
import AlphaTensorBaseChangeR0217
import EvenPointEvaluationBaseChangeR0217
import GenericDualLocalizationR0140

/-! Naturality of the fixed-pairing key map. The comparison on inverse squares
is constructed from the actual pushforward base-change map by duality and tensor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaPullback ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open Scheme.Modules

namespace EvenKeyBaseChange
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Contravariant transport of the actual internal-Hom dual. -/
def dualIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) : dual M ≅ dual N where
  hom := (MonoidalClosed.pre e.inv).app (𝟙_ X.Modules)
  inv := (MonoidalClosed.pre e.hom).app (𝟙_ X.Modules)
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]

lemma dualIso_section {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (t : Γ(dual M, ⊤)) :
    ihomGlobalSectionsEquiv N (𝟙_ X.Modules) ((dualIso e).hom.app ⊤ t) =
      e.inv ≫ ihomGlobalSectionsEquiv M (𝟙_ X.Modules) t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [ihomGlobalSectionsEquiv_app_apply]
  have hn := ((MonoidalClosed.pre e.inv).app (𝟙_ X.Modules)).mapPresheaf.naturality_apply
    (homOfLE (show U ≤ ⊤ from le_top)).op t
  change ihomEval N (𝟙_ X.Modules) U x
    ((dual N).presheaf.map (homOfLE le_top).op
      (((MonoidalClosed.pre e.inv).app (𝟙_ X.Modules)).app ⊤ t)) = _
  erw [← hn, ihomEval_pre_app]
  exact (ihomGlobalSectionsEquiv_app_apply t U (e.inv.app U x)).symm

/-- Functorial isomorphism on the genuine recursively defined tensor power. -/
def powerIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    (r : ℕ) → tensorPower X M r ≅ tensorPower X N r
  | 0 => Iso.refl _
  | r + 1 => sheafTensorCongr X (powerIso e r) e

lemma powerIso_section {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (r : ℕ) (t : Γ(M, ⊤)) :
    (powerIso e r).hom.app ⊤ (tensorPowerSection X M r ⊤ t) =
      tensorPowerSection X N r ⊤ (e.hom.app ⊤ t) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (sheafTensorCongr X (powerIso e r) e).hom.app ⊤
      (tensorSection X _ _ ⊤ (tensorPowerSection X M r ⊤ t) t) = _
    rw [sheafTensorCongr_section, ih]
    rfl

/-- Pull back the evaluation pairing, then precompose with the inverse of
precisely the actual pushforward comparison. -/
def dualBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (M : S.Modules)
    (hM : Scheme.Modules.IsInvertible M) {N : T.Modules}
    (p : (pullback b).obj M ≅ N) : (pullback b).obj (dual M) ≅ dual N := by
  letI := dualComparison_isIso b M hM
  exact asIso (dualComparison b M) ≪≫ dualIso p

lemma dualBaseChange_section {S T : Scheme.{u}} (b : T ⟶ S) (M : S.Modules)
    (hM : Scheme.Modules.IsInvertible M) {N : T.Modules}
    (p : (pullback b).obj M ≅ N) (a : M ⟶ 𝟙_ S.Modules) (d : N ⟶ 𝟙_ T.Modules)
    (h : p.hom ≫ d = (pullback b).map a ≫ (pullbackUnitIso b).hom) :
    (dualBaseChange b M hM p).hom.app ⊤
      (pullbackGlobalSection b (dual M) ((ihomGlobalSectionsEquiv M _).symm a)) =
      (ihomGlobalSectionsEquiv N _).symm d := by
  apply (ihomGlobalSectionsEquiv N _).injective
  change ihomGlobalSectionsEquiv N _ ((dualIso p).hom.app ⊤
    ((dualComparison b M).app ⊤ (pullbackLocalSection b
      ((ihomGlobalSectionsEquiv M _).symm a)))) = _
  rw [dualIso_section, dualComparison_global, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  change p.inv ≫ (pullback b).map a ≫ (pullbackUnitIso b).hom = d
  rw [← h, Iso.inv_hom_id_assoc]

/-- This is the dual tensor-square of p, with the canonical pullback/tensor
comparison; no independently chosen scalar action enters the definition. -/
def squareBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (M : S.Modules)
    (hM : Scheme.Modules.IsInvertible M) {N : T.Modules}
    (p : (pullback b).obj M ≅ N) :
    (pullback b).obj (tensorPower S (dual M) 2) ≅ tensorPower T (dual N) 2 :=
  pullback_tensorPower_iso T S b (dual M) 2 ≪≫ powerIso (dualBaseChange b M hM p) 2

lemma squareBaseChange_section {S T : Scheme.{u}} (b : T ⟶ S) (M : S.Modules)
    (hM : Scheme.Modules.IsInvertible M) {N : T.Modules}
    (p : (pullback b).obj M ≅ N) (a : M ⟶ 𝟙_ S.Modules) (d : N ⟶ 𝟙_ T.Modules)
    (h : p.hom ≫ d = (pullback b).map a ≫ (pullbackUnitIso b).hom) :
    (squareBaseChange b M hM p).hom.app ⊤
      (pullbackGlobalSection b _ (tensorPowerSection S (dual M) 2 ⊤
        ((ihomGlobalSectionsEquiv M _).symm a))) =
      tensorPowerSection T (dual N) 2 ⊤ ((ihomGlobalSectionsEquiv N _).symm d) := by
  change (powerIso (dualBaseChange b M hM p) 2).hom.app ⊤
    ((pullback_tensorPower_iso T S b (dual M) 2).hom.app ⊤ _) = _
  erw [pullback_tensorPower_section, powerIso_section, dualBaseChange_section b M hM p a d h]

end EvenKeyBaseChange

/-- The key formula commutes with arbitrary pointed Cartesian base change.
The existential witness is explicitly the dual square of the actual baseChangeHom. -/
theorem even_key_base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ∀ (L : S.Modules) (m : ((AlgebraicGeometry.Scheme.Modules.pullback D.projection).obj (L)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.Multiplier E D z L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom (T) (S)) (f : Quiver.Hom (F.curve) (E.curve)) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover F), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven F Q (b.appTop z) C → ∀ (K : T.Modules) (n : ((AlgebraicGeometry.Scheme.Modules.pullback C.projection).obj (K)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.Multiplier F C (b.appTop z) K n → ∀ (B : ArithmeticThetaMultiplierKeyR0217.CoverChange E D F b f C) (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 c → ∀ (v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (L)) (K)), ArithmeticThetaMultiplierKeyR0217.MultiplierCompatible E D F b f C B L K m n v → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaMultiplierKeyR0217.productLine F K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.DescendsAlpha E D L m β → ArithmeticThetaMultiplierKeyR0217.DescendsAlpha F C K n γ → ∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine F Q)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P eS → ArithmeticThetaMultiplierKeyR0217.IsRigidification F Q eT → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)) (κT : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q) (ArithmeticThetaMultiplierKeyR0217.productLine F K)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L eS β κ → ArithmeticThetaMultiplierKeyR0217.IsKey F Q K eT γ κT → (∃! j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j) ∧ (∀ j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j → CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map κ.hom) (ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v).hom = CategoryTheory.CategoryStruct.comp j.hom κT.hom) := by
  intro k _ _ S σ E P z hz D hD L m hm T F Q b f hb hQ C hC K n hn
    B c hc v hv β γ hβ hγ eS eT heS heT κ κT hκ hκT
  have hE := even_point_theta_evaluation k S σ E P
  have hF := even_point_theta_evaluation k T (b ≫ σ) F Q
  have hs : IsFrame (inverseSquare E P) ⊤ (evaluationSquare E P eS) :=
    HodgeBaseChange.tensorPower_frame (dual (pushforwardLine E P))
      (evaluationSection E P eS) ((hE.2.2.2.2.2 eS heS).2.2) 2
  have hsp := HodgeBaseChange.pullback_frame b (inverseSquare E P)
    (evaluationSquare E P eS) hs
  letI : IsIso (generator E P) := hE.2.2.2.2.1
  have hJ : Scheme.Modules.IsInvertible (pushforwardLine E P) := by
    constructor
    intro x
    refine ⟨⊤, trivial, ⟨?_⟩⟩
    exact (pullback (⊤ : S.Opens).ι).mapIso (asIso (generator E P)).symm ≪≫
      pullbackUnitIso _
  have hbc := even_point_evaluation_base_change k S σ E P T F Q b f hb hQ
  obtain ⟨q, hq, _⟩ := hbc.2.1
  have hp := hbc.2.2 q hq eS eT heS heT
  letI : IsIso (pushforwardComparison E P F Q b f hb.1.w q) := hp.1
  let p := asIso (pushforwardComparison E P F Q b f hb.1.w q)
  let j₀ : (pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q :=
    EvenKeyBaseChange.squareBaseChange b (pushforwardLine E P) hJ p
  have hj₀ : EvaluationSquareCompatible E P F Q b eS eT j₀ :=
    EvenKeyBaseChange.squareBaseChange_section b (pushforwardLine E P) hJ p
      (evaluation E P eS) (evaluation F Q eT) hp.2
  refine ⟨⟨j₀, hj₀, ?_⟩, ?_⟩
  · intro j hj
    apply Iso.ext
    exact InverseCharacterMultiplier.hom_ext_of_frame _ hsp j.hom j₀.hom
      (hj.trans hj₀.symm)
  · intro j hj
    have ha := alpha_tensor_base_change k S σ E P z hz D hD L m hm
      T F Q b f hb hQ C hC K n hn B c hc v hv β γ hβ hγ
    apply InverseCharacterMultiplier.hom_ext_of_frame _ hsp
    change (productComparison E F b L K c v).hom.app ⊤
        (((pullback b).map κ.hom).app ⊤
          (pullbackGlobalSection b (inverseSquare E P) (evaluationSquare E P eS))) =
      κT.hom.app ⊤ (j.hom.app ⊤
        (pullbackGlobalSection b (inverseSquare E P) (evaluationSquare E P eS)))
    have hmap := MultiplierBaseChange.global_app b κ.hom (evaluationSquare E P eS)
    rw [hmap, show κ.hom.app ⊤ (evaluationSquare E P eS) = β from hκ,
      show j.hom.app ⊤ (pullbackGlobalSection b (inverseSquare E P)
        (evaluationSquare E P eS)) = evaluationSquare F Q eT from hj]
    exact ha.trans hκT.symm

#print axioms EvenKeyBaseChange.dualBaseChange_section
#print axioms EvenKeyBaseChange.squareBaseChange_section
#print axioms even_key_base_change
end ArithmeticThetaMultiplierKeyR0217
