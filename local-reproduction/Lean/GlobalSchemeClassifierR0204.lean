import SchemeFamilyBaseChangeR0204
import PointedCartesianGroupLawR0204
import SchemeLocalClassifierR0204
import SchemeClassifyingUniquenessR0204

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
namespace GlobalSchemeClassifier
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- The accepted quotient family, with precisely its existing geometry and law. -/
def universalFamily {k : Type u} [Field k] (L : ℕ)
    (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) :
    Family (Base A.quotient.ring) where
  curve := A.descent.family.curve
  p := A.descent.family.projection
  law :=
    { mul := A.descent.family.law.mul, one := A.descent.family.law.one
      inv := A.descent.family.law.inv
      mul_assoc := A.descent.family.law.mul_assoc
      one_mul := A.descent.family.law.one_mul
      mul_one := A.descent.family.law.mul_one
      inv_mul_cancel := A.descent.family.law.inv_mul_cancel
      mul_comm := A.descent.family.commutative
      mul_natural := A.descent.family.law.mul_natural }
  proper := A.descent.family.proper
  dimension := A.descent.family.smooth
  connected := A.descent.family.connected

variable {k : Type u} [Field k] [CharZero k] {L : ℕ}
  {A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L}
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C}
  {S : Scheme.{u}} {σ : S ⟶ Base k} {E : Family S} {M : FullLevel E L}

lemma universal_multiplicative {T : Scheme.{u}} (F : Family T)
    (b : T ⟶ Base A.quotient.ring) (f : F.curve ⟶ A.descent.family.curve)
    (h : IsPullback f F.p A.descent.family.projection b)
    (hz : F.zero ≫ f = b ≫ (A.descent.family.law.one (𝟙 _)).val) :
    UniversalMultiplicative k L A F b f :=
  pointed_cartesian_group_law k _ _
    (Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)))
    (universalFamily L A) F b f h hz

/-- Pull a local classifier to any marked Cartesian comparison into its chart.
All section equations are checked in the original Cartesian square. -/
lemma local_pull (D : LocalClassifier k L A B C Q σ E M)
    {T : Scheme.{u}} (F : Family T) (N : FullLevel F L)
    (c : T ⟶ S) (g : F.curve ⟶ E.curve)
    (h : IsPullback g F.p E.p c)
    (hz : F.zero ≫ g = c ≫ E.zero)
    (hx : N.x.val ≫ g = c ≫ M.x.val)
    (hy : N.y.val ≫ g = c ≫ M.y.val)
    (a : T ⟶ Base D.presentation.ring) (ha : a ≫ D.presentation.base = c) :
    ∃ m : F.curve ⟶ ArithmeticThetaRelativeKatoR0169.Curve
        D.presentation.ring D.presentation.equation,
      m ≫ D.presentation.comparison = g ∧
      m ≫ ArithmeticThetaRelativeKatoR0169.structureMap
        D.presentation.ring D.presentation.equation = F.p ≫ a ∧
      Classifies k L A B C Q (c ≫ σ) F N (a ≫ D.base) (m ≫ D.comparison) := by
  let P := D.presentation
  let m := P.cartesian.lift g (F.p ≫ a) (by rw [Category.assoc, ha]; exact h.w)
  have hmg : m ≫ P.comparison = g := P.cartesian.lift_fst _ _ _
  have hmp : m ≫ ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation =
      F.p ≫ a := P.cartesian.lift_snd _ _ _
  have hm : IsPullback m F.p
      (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation) a := by
    have hout : IsPullback (m ≫ P.comparison) F.p E.p (a ≫ P.base) := by
      rw [hmg, ha]; exact h
    exact hout.of_right hmp P.cartesian
  have sec (s : T ⟶ F.curve)
      (t : Base P.ring ⟶ ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
      (hs : s ≫ F.p = 𝟙 _)
      (ht : t ≫ ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation = 𝟙 _)
      (he : s ≫ g = a ≫ t ≫ P.comparison) : s ≫ m = a ≫ t := by
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hmg]; exact he
    · rw [Category.assoc, hmp, ← Category.assoc, hs, Category.id_comp,
        Category.assoc, ht, Category.comp_id]
  have hzero : F.zero ≫ m = a ≫ ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation := by
    apply sec _ _ (F.law.one (𝟙 _)).property
      (by simpa only [P.originLaw.1, Category.id_comp] using (P.law.one (𝟙 _)).property)
    rw [P.zero_eq, ← Category.assoc, ha]
    exact hz
  have hxx : N.x.val ≫ m = a ≫ D.level.x.val := by
    apply sec _ _ N.x.property D.level.x.property
    rw [D.x_eq, ← Category.assoc, ha, hx]
  have hyy : N.y.val ≫ m = a ≫ D.level.y.val := by
    apply sec _ _ N.y.property D.level.y.property
    rw [D.y_eq, ← Category.assoc, ha, hy]
  have hc : IsPullback (m ≫ D.comparison) F.p A.descent.family.projection
      ((a ≫ D.base) ≫ Q.inclusion) := by
    simpa only [Category.assoc] using hm.paste_horiz D.classifies.2.1
  have ho : F.zero ≫ (m ≫ D.comparison) =
      ((a ≫ D.base) ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val := by
    rw [← Category.assoc, hzero, Category.assoc, D.classifies.2.2.1]
    simp only [Category.assoc]
  refine ⟨m, hmg, hmp, ?_, hc, ho, ?_, ?_, universal_multiplicative F _ _ hc ho⟩
  · rw [Category.assoc, D.classifies.1, ← P.base_eq, ← Category.assoc, ha]
  · rw [← Category.assoc, hxx, Category.assoc, D.classifies.2.2.2.1]
    simp only [Category.assoc]
  · rw [← Category.assoc, hyy, Category.assoc, D.classifies.2.2.2.2]
    simp only [Category.assoc]

/-- Agreement on arbitrary scheme tests of two local presentations.
The common family is the actual base change of the original marked family. -/
lemma agreement (hL : 3 ≤ L) (heven : Even L)
    (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B)
    (D₁ D₂ : LocalClassifier k L A B C Q σ E M)
    (T : Scheme.{u}) (a₁ : T ⟶ Base D₁.presentation.ring)
    (a₂ : T ⟶ Base D₂.presentation.ring)
    (ha : a₁ ≫ D₁.presentation.base = a₂ ≫ D₂.presentation.base) :
    a₁ ≫ D₁.base = a₂ ≫ D₂.base ∧
    ∀ (z₁ : T ⟶ ArithmeticThetaRelativeKatoR0169.Curve
          D₁.presentation.ring D₁.presentation.equation)
      (z₂ : T ⟶ ArithmeticThetaRelativeKatoR0169.Curve
          D₂.presentation.ring D₂.presentation.equation),
      z₁ ≫ ArithmeticThetaRelativeKatoR0169.structureMap
        D₁.presentation.ring D₁.presentation.equation = a₁ →
      z₂ ≫ ArithmeticThetaRelativeKatoR0169.structureMap
        D₂.presentation.ring D₂.presentation.equation = a₂ →
      z₁ ≫ D₁.presentation.comparison = z₂ ≫ D₂.presentation.comparison →
      z₁ ≫ D₁.comparison = z₂ ≫ D₂.comparison := by
  let c := a₁ ≫ D₁.presentation.base
  obtain ⟨F, g, hg, hz, hm⟩ := scheme_family_base_change S T E c
  obtain ⟨N, hN, _⟩ := cartesian_full_marking S T E F c g hg hz hm L M
  obtain ⟨m₁, hm₁g, hm₁p, h₁⟩ := local_pull D₁ F N c g hg hz hN.1 hN.2 a₁ rfl
  obtain ⟨m₂, hm₂g, hm₂p, h₂⟩ := local_pull D₂ F N c g hg hz hN.1 hN.2 a₂ ha.symm
  obtain ⟨hb, hf⟩ := scheme_classifying_uniqueness k L hL heven A B hB C Q
    T (c ≫ σ) F N _ _ _ _ h₁ h₂
  refine ⟨hb, ?_⟩
  intro z₁ z₂ hz₁ hz₂ he
  let z := hg.lift (z₁ ≫ D₁.presentation.comparison) (𝟙 T) (by
    rw [Category.assoc, D₁.presentation.cartesian.w, ← Category.assoc, hz₁,
      Category.id_comp])
  have hzg : z ≫ g = z₁ ≫ D₁.presentation.comparison := hg.lift_fst _ _ _
  have hzp : z ≫ F.p = 𝟙 T := hg.lift_snd _ _ _
  have h₁z : z ≫ m₁ = z₁ := by
    apply D₁.presentation.cartesian.hom_ext
    · rw [Category.assoc, hm₁g, hzg]
    · rw [Category.assoc, hm₁p, ← Category.assoc, hzp, Category.id_comp, hz₁]
  have h₂z : z ≫ m₂ = z₂ := by
    apply D₂.presentation.cartesian.hom_ext
    · rw [Category.assoc, hm₂g, hzg, he]
    · rw [Category.assoc, hm₂p, ← Category.assoc, hzp, Category.id_comp, hz₂]
  rw [← h₁z, ← h₂z, Category.assoc, Category.assoc, hf]

end GlobalSchemeClassifier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 GlobalSchemeClassifier
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- The fixed full-level quotient classifies every general marked elliptic family.
Both maps are glued over the complete open cover, without any finiteness hypothesis. -/
theorem global_scheme_classifier :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A), ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B → ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E L), ∃ (b : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring)) (f : Quiver.Hom E.curve A.descent.family.curve), ArithmeticThetaSchemeLevelR0204.Classifies k L A B C Q σ E M b f := by
  intro k _ _ L hL heven A B hB C Q S σ E M
  classical
  choose D hD using scheme_local_classifier k L hL heven A B hB C Q S σ E M
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S
    (fun i => Base (D i).presentation.ring) (fun i => (D i).presentation.base)
    (fun i => ⟨i, hD i⟩) (fun i => (D i).presentation.openImmersion)
  let 𝒱 : E.curve.OpenCover := Scheme.Cover.copy (𝒰.pullback₁ E.p) S
    (fun i => ArithmeticThetaRelativeKatoR0169.Curve
      (D i).presentation.ring (D i).presentation.equation)
    (fun i => (D i).presentation.comparison) (Equiv.refl S)
    (fun i => (D i).presentation.cartesian.isoPullback)
    (fun i => (D i).presentation.cartesian.isoPullback_hom_fst.symm)
  have hbcompat (i j : S) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (D i).base =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (D j).base :=
    (agreement hL heven hB (D i) (D j) _ _ _ (pullback.condition)).1
  have hfcompat (i j : S) :
      pullback.fst (𝒱.f i) (𝒱.f j) ≫ (D i).comparison =
      pullback.snd (𝒱.f i) (𝒱.f j) ≫ (D j).comparison := by
    let z₁ := pullback.fst (𝒱.f i) (𝒱.f j)
    let z₂ := pullback.snd (𝒱.f i) (𝒱.f j)
    have he : z₁ ≫ (D i).presentation.comparison =
        z₂ ≫ (D j).presentation.comparison := pullback.condition
    have ha : (z₁ ≫ ArithmeticThetaRelativeKatoR0169.structureMap
        (D i).presentation.ring (D i).presentation.equation) ≫ (D i).presentation.base =
        (z₂ ≫ ArithmeticThetaRelativeKatoR0169.structureMap
        (D j).presentation.ring (D j).presentation.equation) ≫ (D j).presentation.base := by
      rw [Category.assoc, ← (D i).presentation.cartesian.w,
        ← Category.assoc, he, Category.assoc, (D j).presentation.cartesian.w,
        Category.assoc]
    exact (agreement hL heven hB (D i) (D j) _ _ _ ha).2 z₁ z₂ rfl rfl he
  let b := 𝒰.glueMorphisms (fun i => (D i).base) hbcompat
  let f := 𝒱.glueMorphisms (fun i => (D i).comparison) hfcompat
  have hb (i : S) : (D i).presentation.base ≫ b = (D i).base :=
    𝒰.ι_glueMorphisms _ _ i
  have hf (i : S) : (D i).presentation.comparison ≫ f = (D i).comparison :=
    𝒱.ι_glueMorphisms _ _ i
  have hcart : IsPullback f E.p A.descent.family.projection (b ≫ Q.inclusion) := by
    apply IsPullback.flip
    apply Scheme.isPullback_of_openCover E.p f (b ≫ Q.inclusion)
      A.descent.family.projection 𝒰
    intro i
    apply (D i).classifies.2.1.flip.of_iso
      (D i).presentation.cartesian.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · change ArithmeticThetaRelativeKatoR0169.structureMap
        (D i).presentation.ring (D i).presentation.equation ≫ 𝟙 _ =
        (D i).presentation.cartesian.isoPullback.hom ≫
          pullback.snd E.p (D i).presentation.base
      simpa only [Category.comp_id] using
        (D i).presentation.cartesian.isoPullback_hom_snd.symm
    · change (D i).comparison ≫ 𝟙 _ =
        (D i).presentation.cartesian.isoPullback.hom ≫
          (pullback.fst E.p (D i).presentation.base ≫ f)
      simpa only [Category.comp_id, ← Category.assoc,
        IsPullback.isoPullback_hom_fst] using (hf i).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      change (D i).base ≫ Q.inclusion = (D i).presentation.base ≫ (b ≫ Q.inclusion)
      exact (congrArg (fun a => a ≫ Q.inclusion) (hb i)).symm.trans
        (Category.assoc _ _ _)
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have section_eq (s : S ⟶ E.curve) (t : Base A.quotient.ring ⟶ A.descent.family.curve)
      (ss : ∀ i : S, Base (D i).presentation.ring ⟶
        ArithmeticThetaRelativeKatoR0169.Curve (D i).presentation.ring (D i).presentation.equation)
      (hs : ∀ i, ss i ≫ (D i).presentation.comparison = (D i).presentation.base ≫ s)
      (ht : ∀ i, ss i ≫ (D i).comparison = ((D i).base ≫ Q.inclusion) ≫ t) :
      s ≫ f = (b ≫ Q.inclusion) ≫ t := by
    apply 𝒰.hom_ext
    intro i
    change (D i).presentation.base ≫ (s ≫ f) =
      (D i).presentation.base ≫ ((b ≫ Q.inclusion) ≫ t)
    rw [← Category.assoc, ← hs i, Category.assoc, hf i, ht i]
    rw [← hb i]
    simp only [Category.assoc]
  have hz : E.zero ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val :=
    section_eq E.zero _
      (fun i => ArithmeticThetaRelativeKatoR0169.origin
        (D i).presentation.ring (D i).presentation.equation)
      (fun i => (D i).presentation.zero_eq) (fun i => (D i).classifies.2.2.1)
  refine ⟨b, f, ?_, hcart, hz, ?_, ?_, universal_multiplicative E _ _ hcart hz⟩
  · apply 𝒰.hom_ext
    intro i
    change (D i).presentation.base ≫ (b ≫ _) = (D i).presentation.base ≫ σ
    rw [← Category.assoc, hb i, (D i).classifies.1, (D i).presentation.base_eq]
  · exact section_eq M.x.val A.marking.x.val (fun i => (D i).level.x.val)
      (fun i => (D i).x_eq) (fun i => (D i).classifies.2.2.2.1)
  · exact section_eq M.y.val A.marking.y.val (fun i => (D i).level.y.val)
      (fun i => (D i).y_eq) (fun i => (D i).classifies.2.2.2.2)

#print axioms global_scheme_classifier
end ArithmeticThetaSchemeLevelR0204
