module

public import PhaseFreeKeyR0219
public import PhaseFreeMultiplierBaseChangeR0219
public import PhaseFreeAlphaDescentR0219
public import EvenKeyBaseChangeR0217

@[expose] public section

/-! Naturality of the phase-free alpha tensor and key map on arbitrary Cartesian tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219.KeyNaturalityProof
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaPullback ArithmeticThetaSheafTensor
open ArithmeticThetaRelativeDiscriminantR0171
open AlphaTensorCoherence InverseCharacterMultiplier.Transport
open Scheme.Modules

/-- Tensor coherence specialized to a composite test, retaining both actual maps. -/
lemma tensor_composite {S T U : Scheme.{u}} (b : T ⟶ S) (a : U ⟶ T)
    (H L : S.Modules) (HT K : T.Modules) (HU : U.Modules)
    (c : (pullback b).obj H ≅ HT) (v : (pullback b).obj L ≅ K)
    (e : (pullback a).obj HT ≅ HU) (d : (pullback (a ≫ b)).obj H ≅ HU)
    (hc : (pullback a).map c.hom ≫ e.hom = ((pullbackComp a b).app H).hom ≫ d.hom) :
    let w := ((pullbackComp a b).app L).symm ≪≫ (pullback a).mapIso v
    (pullback a).map (pullback_sheafTensor_iso T S b H L ≪≫ sheafTensorCongr T c v).hom ≫
      (pullback_sheafTensor_iso U T a HT K ≪≫ sheafTensorCongr U e (Iso.refl _)).hom =
    ((pullbackComp a b).app (sheafTensor S H L)).hom ≫
      (pullback_sheafTensor_iso U S (a ≫ b) H L ≪≫
        sheafTensorCongr U d w).hom := by
  intro w
  have he : (pullback a).mapIso c ≪≫ e = (pullbackComp a b).app H ≪≫ d := by
    apply Iso.ext
    exact hc
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((pullback a).map (sheafTensorCongr T c v).hom), tensor_naturality]
  simp only [Category.assoc]
  rw [congr_comp]
  simp only [Iso.trans_refl]
  rw [← Category.assoc ((pullbackComp a b).app (sheafTensor S H L)).hom,
    tensor_comp]
  simp only [Category.assoc]
  rw [congr_comp, he]
  have hw : (pullbackComp a b).app L ≪≫ w = (pullback a).mapIso v := by
    simp [w]
  rw [hw]

variable {S T : Scheme.{u}} (E : Family S) (P : EvenPoint E)
  (F : Family T) (Q : EvenPoint F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hb : Cartesian E F b f) (hQ : Q.point.val ≫ f = b ≫ P.point.val)

include hQ in
/-- The transported alpha tensor satisfies its defining equality on every marked test. -/
lemma descends_base_change (L : S.Modules) (m : Frames E P L) (hm : IsMultiplier E P L m)
    (K : T.Modules) (n : Frames F Q K)
    (c : (pullback b).obj (Cotangent E) ≅ Cotangent F)
    (hc : CotangentCompatible E F b f hb.2.1 c)
    (v : (pullback b).obj L ≅ K) (hv : Compatible E P F Q b f L K m n v)
    (β : Γ(productLine E L, ⊤)) (hβ : Descends E P L m β) :
    Descends F Q K n ((productComparison E F b L K c v).hom.app ⊤
      (pullbackGlobalSection b _ β)) := by
  intro B
  let A := BaseChangeProof.compositeTest E P F Q b f hb hQ B
  obtain ⟨d, hd⟩ := (hβ A).1
  obtain ⟨α, hα⟩ := (hβ A).2.1
  refine ⟨⟨MultiplierProof.comparison F Q B, MultiplierProof.comparison_spec F Q B⟩,
    ⟨α, hα⟩, ?_⟩
  intro e he α' hα'
  let w := ((pullbackComp B.map b).app L).symm ≪≫ (pullback B.map).mapIso v
  have hw : w.hom.app ⊤ (m A) = n B :=
    ((BaseChangeProof.compatible_iff E P F Q b f hb hQ L m hm K n v).1 hv) B
  have hcot := scheme_cotangent_coherence.2 S T B.base E F B.family b B.map
    f B.comparison hb.2.1 B.cartesian.2.1 A.cartesian.2.1 c e d hc he hd
  have hmaps := tensor_composite b B.map (Cotangent E) L (Cotangent F) K
    (Cotangent B.family) c v e d hcot
  have hs := congrArg (fun g => g.app ⊤
    (pullbackGlobalSection B.map _ (pullbackGlobalSection b _ β))) hmaps
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Iso.trans_hom] at hs
  rw [MultiplierBaseChange.global_app] at hs
  erw [comp_global B.map b (productLine E L) β] at hs
  have hlocal := (hβ A).2.2 d hd α' hα'
  have ht : (sheafTensorCongr B.base d w).hom =
      (sheafTensorCongr B.base d (Iso.refl _)).hom ≫
        (sheafTensorCongr B.base (Iso.refl _) w).hom := by
    rw [congr_comp]
    simp only [Iso.trans_refl, Iso.refl_trans]
  rw [ht] at hs
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hs
  change (sheafTensorCongr B.base d (Iso.refl _)).hom.app ⊤
    ((pullback_sheafTensor_iso B.base S (B.map ≫ b) (Cotangent E) L).hom.app ⊤
      (pullbackGlobalSection (B.map ≫ b) _ β)) = _ at hlocal
  erw [hlocal, sheafTensorCongr_section, hw] at hs
  exact hs

end ArithmeticThetaPhaseFreeKeyR0219.KeyNaturalityProof

namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaPullback ArithmeticThetaSheafTensor
open ArithmeticThetaRelativeDiscriminantR0171
open Scheme.Modules

/-- Full section and key-morphism naturality under arbitrary pointed Cartesian base change.
The comparison on inverse squares is the dual tensor-square of the actual pushforward map. -/
theorem phase_free_key_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∀ (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 c → ∀ (v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K), ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaMultiplierKeyR0217.productLine F K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ArithmeticThetaPhaseFreeKeyR0219.Descends F Q K n γ → ArithmeticThetaMultiplierKeyR0217.AlphaNatural E F b L K c v β γ ∧ (∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine F Q)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P eS → ArithmeticThetaMultiplierKeyR0217.IsRigidification F Q eT → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)) (κT : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q) (ArithmeticThetaMultiplierKeyR0217.productLine F K)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L eS β κ → ArithmeticThetaMultiplierKeyR0217.IsKey F Q K eT γ κT → (∃! j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j) ∧ (∀ j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j → CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map κ.hom) (ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v).hom = CategoryTheory.CategoryStruct.comp j.hom κT.hom)) := by
  intro k _ _ S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ hβ hγ
  have htransport := KeyNaturalityProof.descends_base_change E P F Q b f hb hQ
    L m hm K n c hc v hv β hβ
  have ha : AlphaNatural E F b L K c v β γ :=
    (phase_free_alpha_descent k T (b ≫ σ) F Q K n hn).1.unique htransport hγ
  refine ⟨ha, ?_⟩
  intro eS eT heS heT κ κT hκ hκT
  have hE := even_point_theta_evaluation k S σ E P
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

#print axioms KeyNaturalityProof.tensor_composite
#print axioms KeyNaturalityProof.descends_base_change
#print axioms phase_free_key_naturality
end ArithmeticThetaPhaseFreeKeyR0219
