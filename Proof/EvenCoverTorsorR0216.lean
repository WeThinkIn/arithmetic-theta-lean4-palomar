module

public import EvenCoverRightActionR0216
public import LocallyConstantMarkingComparisonR0216

@[expose] public section

/-! Geometry and scheme-valued simple transitivity of the even marking cover. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216
namespace EvenCoverTorsor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaUniversalEvaluationR0213
open EvenMarkingSubcover EvenCoverRightAction

variable {S : Scheme.{u}} (E : Family S)

lemma coverMap_refl (D : Cover E) :
    CoverMap E D D (𝟙 D.space) (𝟙 D.family.curve) := by
  refine ⟨by simp, ⟨?_, by simp, ?_, by simp, by simp⟩, by simp⟩
  · exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T t x y x' y' hx hy
    have hx' : x' = x := Subtype.ext (by simpa using hx)
    have hy' : y' = y := Subtype.ext (by simpa using hy)
    subst x'; subst y'
    simp only [Category.comp_id]
    congr 2

lemma coverMap_comp (C D H : Cover E)
    (q : C.space ⟶ D.space) (f : C.family.curve ⟶ D.family.curve)
    (r : D.space ⟶ H.space) (g : D.family.curve ⟶ H.family.curve)
    (hq : CoverMap E C D q f) (hr : CoverMap E D H r g) :
    CoverMap E C H (q ≫ r) (f ≫ g) := by
  refine ⟨by rw [Category.assoc, hr.1, hq.1], ?_, ?_⟩
  · exact marked_comp H.family D.family C.family H.marking D.marking C.marking
      r g q f hr.2.1 hq.2.1
  · rw [Category.assoc, hr.2.2, hq.2.2]

lemma coverMap_unique (P : EvenPoint E) (z : Γ(S, ⊤)) (C D : Cover E)
    (hC : RepresentsEven E P z C) (hD : RepresentsEven E P z D)
    (q r : C.space ⟶ D.space)
    (f g : C.family.curve ⟶ D.family.curve)
    (hq : CoverMap E C D q f) (hr : CoverMap E C D r g) : q = r := by
  have hu := hD.2 C.space C.family C.marking C.projection C.comparison C.cartesian hC.1
  exact congrArg Subtype.val (hu.unique (y₁ := ⟨q, hq.1⟩) (y₂ := ⟨r, hr.1⟩)
    ⟨f, hq.2⟩ ⟨g, hr.2⟩)

/-- Representing the same exact marking functor gives an isomorphism over the base. -/
lemma representing_iso (P : EvenPoint E) (z : Γ(S, ⊤)) (C D : Cover E)
    (hC : RepresentsEven E P z C) (hD : RepresentsEven E P z D) :
    ∃ e : C.space ≅ D.space, e.hom ≫ D.projection = C.projection := by
  obtain ⟨q, ⟨f, hf, hfc⟩, _⟩ :=
    hD.2 C.space C.family C.marking C.projection C.comparison C.cartesian hC.1
  obtain ⟨r, ⟨g, hg, hgc⟩, _⟩ :=
    hC.2 D.space D.family D.marking D.projection D.comparison D.cartesian hD.1
  have hq : CoverMap E C D q.val f := ⟨q.property, hf, hfc⟩
  have hr : CoverMap E D C r.val g := ⟨r.property, hg, hgc⟩
  have hqr : q.val ≫ r.val = 𝟙 C.space :=
    coverMap_unique E P z C C hC hC _ _ _ _
      (coverMap_comp E C D C q.val f r.val g hq hr) (coverMap_refl E C)
  have hrq : r.val ≫ q.val = 𝟙 D.space :=
    coverMap_unique E P z D D hD hD _ _ _ _
      (coverMap_comp E D C D r.val g q.val f hr hq) (coverMap_refl E D)
  exact ⟨⟨q.val, r.val, hqr, hrq⟩, q.property⟩

lemma geometry (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1)
    (D : Cover E) (hD : RepresentsEven E P z D) : Geometry E D 16 := by
  obtain ⟨H, hH⟩ := scheme_four_cover k S σ E
  obtain ⟨C, j, h, _, _, _, hC, hgeom⟩ := even_marking_subcover k S σ E P z hz H hH
  obtain ⟨e, he⟩ := representing_iso E P z D C hD hC
  obtain ⟨hf, het, hs, hr⟩ := hgeom
  letI := hf
  letI := het
  letI := hs
  have hfinite : IsFinite D.projection := by rw [← he]; infer_instance
  have hetale : Etale D.projection := by rw [← he]; infer_instance
  have hsurj : Surjective D.projection := by rw [← he]; infer_instance
  refine ⟨hfinite, hetale, hsurj, ?_⟩
  intro s
  rw [← he, Scheme.Hom.finrank_comp_left_of_isIso]
  exact hr s

lemma changedX_over {T : Scheme.{u}} (F : Family T) (M : FullLevel F 4)
    (A : ArithmeticThetaFourTorsion.Mat4) : changedX F M A ≫ F.p = 𝟙 T :=
  (F.law.mul _ _ _).property

lemma changedY_over {T : Scheme.{u}} (F : Family T) (M : FullLevel F 4)
    (A : ArithmeticThetaFourTorsion.Mat4) : changedY F M A ≫ F.p = 𝟙 T :=
  (F.law.mul _ _ _).property

/-- Pullback cancellation recovers equality of actual local sections, including nilpotents. -/
lemma localChange_iff (D : Cover E) {T : Scheme.{u}} (F : Family T)
    (c : T ⟶ S) (f : F.curve ⟶ E.curve) (hF : Cartesian E F c f)
    (M N : FullLevel F 4) (a b : T ⟶ D.space)
    (h : F.curve ⟶ D.family.curve)
    (ha : MarkedCartesian D.family F D.marking M a h) (hf : h ≫ D.comparison = f)
    (hx : N.x.val ≫ f = b ≫ D.marking.x.val ≫ D.comparison)
    (hy : N.y.val ≫ f = b ≫ D.marking.y.val ≫ D.comparison)
    (g : LocallyConstant T EvenGroup) :
    LocalChange F M N g ↔ LocallyRelated E D a b g := by
  have hchange (A : ArithmeticThetaFourTorsion.Mat4) :=
    changed_comp D.family F D.marking M a h ha A
  have hcx (A) : changedX F M A ≫ f = a ≫ changedX D.family D.marking A ≫ D.comparison := by
    rw [← hf, ← Category.assoc, (hchange A).1, Category.assoc]
  have hcy (A) : changedY F M A ≫ f = a ≫ changedY D.family D.marking A ≫ D.comparison := by
    rw [← hf, ← Category.assoc, (hchange A).2, Category.assoc]
  constructor
  · intro hg t
    obtain ⟨U, ht, hU, hUx, hUy⟩ := hg t
    refine ⟨U, ht, hU, ?_, ?_⟩
    · have hh := congrArg (fun v => v ≫ f) hUx
      simpa only [Category.assoc, hx, hcx] using hh
    · have hh := congrArg (fun v => v ≫ f) hUy
      simpa only [Category.assoc, hy, hcy] using hh
  · intro hg t
    obtain ⟨U, ht, hU, hUx, hUy⟩ := hg t
    refine ⟨U, ht, hU, ?_, ?_⟩
    · apply hF.1.hom_ext
      · simpa only [Category.assoc, hx, hcx] using hUx
      · simp only [Category.assoc, N.x.property, changedX_over, Category.comp_id]
    · apply hF.1.hom_ext
      · simpa only [Category.assoc, hy, hcy] using hUy
      · simp only [Category.assoc, N.y.property, changedY_over, Category.comp_id]

/-- Both parameter maps give compatible markings on one actual Cartesian family. -/
lemma simple_transitivity (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E) (hD : RepresentsEven E P z D)
    (T : Scheme.{u}) (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) :
    ∃! g : LocallyConstant T EvenGroup, LocallyRelated E D a b g := by
  let c := a ≫ D.projection
  obtain ⟨F, f, hpb, hz, hm⟩ := scheme_family_base_change S T E c
  have hF : Cartesian E F c f := ⟨hpb, hz, hm⟩
  obtain ⟨M, h, hM, hf⟩ := marking_over_parameter E k σ D F c f hF a rfl
  obtain ⟨N, l, hN, lf⟩ := marking_over_parameter E k σ D F c f hF b hab.symm
  have hMM : Matches E P z F M c f := by
    have hh := matches_pullback E P z D.family F D.marking M D.projection D.comparison a h hM hD.1
    simpa only [hf] using hh
  have hNN : Matches E P z F N c f := by
    have hh := matches_pullback E P z D.family F D.marking N D.projection D.comparison b l hN hD.1
    simpa only [lf, ← hab] using hh
  have heven : evenPoint F M = evenPoint F N := by
    apply hF.1.hom_ext
    · exact hMM.1.trans hNN.1.symm
    · exact (F.law.mul _ _ _).property.trans (F.law.mul _ _ _).property.symm
  have hx : N.x.val ≫ f = b ≫ D.marking.x.val ≫ D.comparison := by
    rw [← lf, ← Category.assoc, hN.2.2.2.1, Category.assoc]
  have hy : N.y.val ≫ f = b ≫ D.marking.y.val ≫ D.comparison := by
    rw [← lf, ← Category.assoc, hN.2.2.2.2, Category.assoc]
  have heq := localChange_iff E D F c f hF M N a b h hM hf hx hy
  obtain ⟨g, hg, hu⟩ := locally_constant_marking_comparison k T (c ≫ σ) F M N
    (c.appTop z) hMM.2 hNN.2 heven
  exact ⟨g, (heq g).mp hg, fun g' hg' => hu g' ((heq g').mpr hg')⟩

end EvenCoverTorsor

/-- Finite étale degree sixteen and simple transitivity on every scheme-valued test. -/
theorem even_cover_torsor :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ArithmeticThetaEvenMarkingTorsorR0216.Geometry E D 16 ∧ (∀ (T : AlgebraicGeometry.Scheme.{u}) (a b : Quiver.Hom T D.space), CategoryTheory.CategoryStruct.comp a D.projection = CategoryTheory.CategoryStruct.comp b D.projection → ∃! g : LocallyConstant T ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup, ArithmeticThetaEvenMarkingTorsorR0216.LocallyRelated E D a b g) := by
  intro k _ _ S σ E P z hz D hD
  exact ⟨EvenCoverTorsor.geometry E k σ P z hz D hD,
    EvenCoverTorsor.simple_transitivity E k σ P z D hD⟩

#print axioms even_cover_torsor
end ArithmeticThetaEvenMarkingTorsorR0216
