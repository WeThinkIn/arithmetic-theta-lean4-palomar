import SchemeThetaNaturalityDefinitionsR0262

/-! Evaluation commutes with the fixed Cartesian theta comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
namespace EvaluationNaturalityR0262
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

variable {S T X Y : Scheme.{u}}

/-- The pullback comparison of a specified commutative square. -/
def square (a : T ⟶ S) (z : S ⟶ X) (w : T ⟶ Y) (f : Y ⟶ X)
    (h : a ≫ z = w ≫ f) :=
  pullbackComp a z ≪≫ pullbackCongr h ≪≫ (pullbackComp w f).symm

/-- Pulling back along a section followed by its projection is the identity. -/
def collapse (z : S ⟶ X) (p : X ⟶ S) (h : z ≫ p = 𝟙 S) :=
  pullbackComp z p ≪≫ pullbackCongr h ≪≫ pullbackId S

lemma square_identity (b : T ⟶ S) (N : S.Modules) :
    (square b (𝟙 S) (𝟙 T) b (by simp)).hom.app N =
      (pullback b).map ((pullbackId S).hom.app N) ≫
        (pullbackId T).inv.app ((pullback b).obj N) := by
  have hr := ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.pullback_right_unit b N rfl
  have h₁ : (pullbackComp b (𝟙 S)).hom.app N =
      (pullback b).map ((pullbackId S).hom.app N) := by
    apply (cancel_epi ((pullback b).map ((pullbackId S).inv.app N))).mp
    simpa only [Functor.id_obj, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, eqToHom_refl] using hr
  have h₂ := ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.pullback_left_unit b N rfl
  have h₂' : (pullbackComp (𝟙 T) b).inv.app N =
      (pullbackId T).inv.app ((pullback b).obj N) := by
    apply (cancel_mono ((pullbackComp (𝟙 T) b).hom.app N)).mp
    rw [Iso.inv_hom_id_app]
    change 𝟙 ((pullback b).obj N) = _
    simpa only [eqToHom_refl] using h₂.symm
  change (pullbackComp b (𝟙 S)).hom.app N ≫ (pullbackComp (𝟙 T) b).inv.app N = _
  rw [h₁, h₂']

lemma section_paste (p : X ⟶ S) (z : S ⟶ X) (ez : z ≫ p = 𝟙 S)
    (q : Y ⟶ T) (w : T ⟶ Y) (ew : w ≫ q = 𝟙 T)
    (b : T ⟶ S) (f : Y ⟶ X) (hp : f ≫ p = q ≫ b)
    (hz : b ≫ z = w ≫ f) (N : S.Modules) :
    (square b z w f hz).hom.app ((pullback p).obj N) ≫
      (pullback w).map ((square f p q b hp).hom.app N) ≫
        (collapse w q ew).hom.app ((pullback b).obj N) =
      (pullback b).map ((collapse z p ez).hom.app N) := by
  have h := pullbackComp_pullbackCongr_pasteSquares_app
    z p (𝟙 S) ez b f b w q (𝟙 T) ew hz hp (by simp) N
  have hh := congrArg (fun a => a ≫ (pullbackId T).hom.app ((pullback b).obj N)) h
  simp only [Category.assoc] at hh
  change (square b z w f hz).hom.app ((pullback p).obj N) ≫
      (pullback w).map ((square f p q b hp).hom.app N) ≫
        (collapse w q ew).hom.app ((pullback b).obj N) =
    (pullback b).map ((pullbackComp z p ≪≫ pullbackCongr ez).hom.app N) ≫
      (square b (𝟙 S) (𝟙 T) b (by simp)).hom.app N ≫
        (pullbackId T).hom.app ((pullback b).obj N) at hh
  rw [square_identity] at hh
  simpa only [Functor.id_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    collapse, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] using hh

lemma square_reverse (a : T ⟶ S) (z : S ⟶ X) (w : T ⟶ Y) (f : Y ⟶ X)
    (h : a ≫ z = w ≫ f) :
    (square a z w f h).symm = square w f a z h.symm := by
  have hh : (pullbackCongr h).symm = pullbackCongr h.symm := rfl
  simpa only [square, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc] using
    congrArg (fun e => pullbackComp w f ≪≫ e ≪≫ (pullbackComp a z).symm) hh

lemma section_square (p : X ⟶ S) (z : S ⟶ X) (ez : z ≫ p = 𝟙 S)
    (q : Y ⟶ T) (w : T ⟶ Y) (ew : w ≫ q = 𝟙 T)
    (b : T ⟶ S) (f : Y ⟶ X) (hp : f ≫ p = q ≫ b)
    (hz : b ≫ z = w ≫ f) (N : S.Modules) :
    (pullback b).map ((collapse z p ez).inv.app N) ≫
      (square b z w f hz).hom.app ((pullback p).obj N) =
    (collapse w q ew).inv.app ((pullback b).obj N) ≫
      (pullback w).map ((square q b f p hp.symm).hom.app N) := by
  have h := section_paste p z ez q w ew b f hp hz N
  have hr : (square q b f p hp.symm).hom.app N =
      (square f p q b hp).inv.app N := by
    rw [← square_reverse]; rfl
  rw [hr]
  apply (cancel_mono ((pullback w).map ((square f p q b hp).hom.app N) ≫
    (collapse w q ew).hom.app ((pullback b).obj N))).mp
  simp only [Functor.comp_obj, Functor.id_obj, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.id_obj, CategoryTheory.Functor.map_id]

/-- Evaluation is the counit pulled back to the specified section. -/
def eval (p : X ⟶ S) (z : S ⟶ X) (ez : z ≫ p = 𝟙 S) (L : X.Modules) :
    (pushforward p).obj L ⟶ (pullback z).obj L :=
  (collapse z p ez).inv.app ((pushforward p).obj L) ≫
    (pullback z).map ((pullbackPushforwardAdjunction p).counit.app L)

/-- The actual adjoint of the transported counit, for any sheaf morphism. -/
def adjointMap (p : X ⟶ S) (q : Y ⟶ T) (b : T ⟶ S) (f : Y ⟶ X)
    (hp : f ≫ p = q ≫ b) (L : X.Modules) (K : Y.Modules)
    (φ : (pullback f).obj L ⟶ K) :
    (pullback b).obj ((pushforward p).obj L) ⟶ (pushforward q).obj K :=
  (pullbackPushforwardAdjunction q).homEquiv _ _
    ((square q b f p hp.symm).hom.app _ ≫
      (pullback f).map ((pullbackPushforwardAdjunction p).counit.app L) ≫ φ)

/-- Naturality of evaluation, with all dependent composition transports explicit. -/
lemma evaluation_square (p : X ⟶ S) (z : S ⟶ X) (ez : z ≫ p = 𝟙 S)
    (q : Y ⟶ T) (w : T ⟶ Y) (ew : w ≫ q = 𝟙 T)
    (b : T ⟶ S) (f : Y ⟶ X) (hp : f ≫ p = q ≫ b)
    (hz : b ≫ z = w ≫ f) (L : X.Modules) (K : Y.Modules)
    (φ : (pullback f).obj L ⟶ K) :
    (pullback b).map (eval p z ez L) ≫
      (square b z w f hz).hom.app L ≫ (pullback w).map φ =
    adjointMap p q b f hp L K φ ≫ eval q w ew K := by
  let A := adjointMap p q b f hp L K φ
  have ha : (pullback q).map A ≫ (pullbackPushforwardAdjunction q).counit.app K =
      (square q b f p hp.symm).hom.app _ ≫
        (pullback f).map ((pullbackPushforwardAdjunction p).counit.app L) ≫ φ := by
    exact (Equiv.symm_apply_apply (pullbackPushforwardAdjunction q |>.homEquiv _ _) _)
  have hn := (square b z w f hz).hom.naturality
    ((pullbackPushforwardAdjunction p).counit.app L)
  dsimp only [Functor.comp_map] at hn
  have hc := (collapse w q ew).inv.naturality A
  dsimp only [Functor.id_map, Functor.comp_map] at hc
  change (pullback b).map (eval p z ez L) ≫
      (square b z w f hz).hom.app L ≫ (pullback w).map φ = A ≫ eval q w ew K
  simp only [eval, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  erw [reassoc_of% (section_square p z ez q w ew b f hp hz ((pushforward p).obj L))]
  rw [reassoc_of% hc]
  conv_rhs => rw [← (pullback w).map_comp, ha]
  simp only [Functor.map_comp, Category.assoc]

end EvaluationNaturalityR0262

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaMarkingR0259

set_option linter.unusedVariables false in
/-- Identity evaluation commutes with the canonical Cartier/conormal comparison
and the adjoint pushforward map, in every degree. -/
theorem scheme_evaluation_naturality
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S)
    (T : Scheme.{u}) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :
    (Scheme.Modules.pullback b).map (evaluation E m) ≫
        (fiberComparison E F b f hc hz m).hom =
      pushforwardMap E F b f hc hz m ≫ evaluation F m := by
  exact EvaluationNaturalityR0262.evaluation_square E.p E.zero (E.law.one (𝟙 S)).property
    F.p F.zero (F.law.one (𝟙 T)).property b f hc.w hz.symm
    (thetaLine E m) (thetaLine F m) (thetaComparison E F b f hc hz m).hom

#print axioms scheme_evaluation_naturality
end ArithmeticThetaSchemeThetaNaturalityR0262
