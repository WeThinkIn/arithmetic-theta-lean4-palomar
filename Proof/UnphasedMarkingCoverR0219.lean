module

public import PhaseFreeKeyDefinitionsR0219
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaUniversalEvaluationR0213 ArithmeticThetaPhaseSwitchR0218
open SchemeFourCover EvenMarkingSubcover

namespace UnphasedCoverProof
variable {S : Scheme.{u}} (E : Family S)

/-- Pull back the specified nonzero two-torsion section along the actual family square. -/
def pullEven {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f) (P : EvenPoint E) : EvenPoint F where
  point := pullSection E F b f hc P.point
  killed := pullSection_killed E F b f hc P.point 2 P.killed
  avoids := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht⟩ ⟨v, hv⟩
    have h := congrArg (fun a : B ⟶ E.curve => a t) (pullSection_comp E F b f hc P.point)
    have hz := congrArg (fun a : B ⟶ E.curve => a v) hc.2.1
    exact Set.disjoint_left.mp P.avoids ⟨b t, by simpa only [Scheme.Hom.comp_apply, ht] using h.symm⟩
      ⟨b v, by simpa only [Scheme.Hom.comp_apply, hv] using hz.symm⟩

/-- Factor a pointed Cartesian family map through another such map. -/
lemma cartesian_factor (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    {B T : Scheme.{u}} (G : Family B) (F : Family T)
    (c : B ⟶ S) (g : G.curve ⟶ E.curve) (hG : Cartesian E G c g)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hF : Cartesian E F b f)
    (q : T ⟶ B) (hq : q ≫ c = b) :
    ∃ h : F.curve ⟶ G.curve, Cartesian G F q h ∧ h ≫ g = f := by
  let h := hG.1.lift f (F.p ≫ q) (by rw [Category.assoc, hq]; exact hF.1.w)
  have hg : h ≫ g = f := hG.1.lift_fst _ _ _
  have hp : h ≫ G.p = F.p ≫ q := hG.1.lift_snd _ _ _
  have hpb : IsPullback h F.p G.p q := by
    apply IsPullback.of_right (h₁₂ := g) (h₂₂ := c) _ hp hG.1
    rw [hg, hq]
    exact hF.1
  have hz : F.zero ≫ h = q ≫ G.zero := by
    apply hG.1.hom_ext
    · rw [Category.assoc, hg, hF.2.1, Category.assoc, hG.2.1, ← Category.assoc, hq]
    · rw [Category.assoc, hp, ← Category.assoc, Family.zero, Family.zero,
        (F.law.one (𝟙 T)).property, Category.id_comp,
        Category.assoc, (G.law.one (𝟙 B)).property, Category.comp_id]
  exact ⟨h, ⟨hpb, hz, pointed_cartesian_group_law k B T (c ≫ σ) G F q h hpb hz⟩, hg⟩

/-- Regard a cover of a Cartesian family as a cover of the original family. -/
def composite {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f) (C : Cover F) : Cover E where
  space := C.space
  projection := C.projection ≫ b
  family := C.family
  comparison := C.comparison ≫ f
  cartesian := cartesian_comp E F C.family b f hc C.projection C.comparison C.cartesian
  marking := C.marking

/-- The Miller phase of a marking supplies its unique map to the phase cover. -/
lemma composite_represents (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (F : Family (phaseSpace k S σ))
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F (phaseProjection k S σ) f)
    (C : Cover F)
    (hC : RepresentsEven F (pullEven E F (phaseProjection k S σ) f hc P)
      (phaseValue k S σ) C) :
    RepresentsUnphased E P (composite E F (phaseProjection k S σ) f hc C) := by
  let b := phaseProjection k S σ
  let z := phaseValue k S σ
  let Q := pullEven E F b f hc P
  have hQ : Q.point.val ≫ f = b ≫ P.point.val := pullSection_comp E F b f hc P.point
  dsimp only [RepresentsUnphased, composite]
  constructor
  · change evenPoint C.family C.marking ≫ (C.comparison ≫ f) =
      (C.projection ≫ b) ≫ P.point.val
    rw [← Category.assoc, hC.1.1, Category.assoc, hQ, Category.assoc]
  · intro A
    obtain ⟨w, hw, _⟩ := (scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).1
    have hw2 := ((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).2 w hw).2.1
    obtain ⟨q, hqb, hqz⟩ := (PhaseCoverProof.represents k S σ A.base A.map w hw2).exists
    obtain ⟨g, hg, hgf⟩ := cartesian_factor E k σ F A.family b f hc
      A.map A.comparison A.cartesian q hqb
    have hchar : evenPoint A.family A.marking ≫ g = q ≫ Q.point.val := by
      apply hc.1.hom_ext
      · rw [Category.assoc, hgf, A.characteristic, Category.assoc, hQ, ← Category.assoc, hqb]
      · rw [Category.assoc, hg.1.w, ← Category.assoc, SchemeThetaEvaluation.evenPoint_over,
          Category.id_comp, Category.assoc, Q.point.property, Category.comp_id]
    have hm : Matches F Q z A.family A.marking q g := ⟨hchar, by rw [hqz]; exact hw⟩
    obtain ⟨r, ⟨h, hh, hhg⟩, hu⟩ := hC.2 A.base A.family A.marking q g hg hm
    have hrb : r.val ≫ (C.projection ≫ b) = A.map := by rw [← Category.assoc, r.property, hqb]
    refine ⟨⟨r.val, hrb⟩, ⟨h, hh, ?_⟩, ?_⟩
    · change h ≫ (C.comparison ≫ f) = A.comparison
      rw [← Category.assoc, hhg, hgf]
    · rintro r' ⟨h', hh', hhf'⟩
      have hp : MillerPhase A.family A.marking ((r'.val ≫ C.projection).appTop z) := by
        simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
          SchemePhaseNaturality.pullback_phase C.family A.family C.marking A.marking
            r'.val h' hh' (C.projection.appTop z) hC.1.2
      have he : r'.val ≫ C.projection = q := by
        apply PhaseCoverProof.hom_ext k S σ
        · exact r'.property.trans hqb.symm
        · exact ((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).1.unique hp hw).trans hqz.symm
      have hhg' : h' ≫ C.comparison = g := by
        apply hc.1.hom_ext
        · exact hhf'.trans hgf.symm
        · rw [Category.assoc, C.cartesian.1.w, ← Category.assoc, hh'.1.w,
            Category.assoc, he, hg.1.w]
      apply Subtype.ext
      exact congrArg (fun a : {a : A.base ⟶ C.space // a ≫ C.projection = q} => a.val)
        (hu ⟨r'.val, he⟩ ⟨h', hh', hhg'⟩)

/-- Composition multiplies the accepted degrees sixteen and two. -/
lemma exists_cover (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) : ∃ D : Cover E, RepresentsUnphased E P D ∧ Geometry E D 32 := by
  let B := phaseSpace k S σ
  let b := phaseProjection k S σ
  let z := phaseValue k S σ
  let F := SchemeFamilyBaseChange.baseChangeFamily E b
  let f := pullback.fst E.p b
  have hc : Cartesian E F b f := ⟨IsPullback.of_hasPullback E.p b,
    SchemeFamilyBaseChange.baseChangeLaw_zero E b,
    SchemeFamilyBaseChange.baseChangeFamily_multiplicative E b⟩
  let Q := pullEven E F b f hc P
  obtain ⟨D, hD⟩ := scheme_four_cover k B (b ≫ σ) F
  obtain ⟨C, _, _, _, _, _, hC, hgeom⟩ := even_marking_subcover k B (b ≫ σ) F Q z
    (PhaseCoverProof.value_sq k S σ) D hD
  have hb := phase_cover k S σ
  letI : IsFinite b := hb.1
  letI : Etale b := hb.2.1
  letI : Surjective b := hb.2.2.1
  letI : IsFinite C.projection := hgeom.1
  letI : Etale C.projection := hgeom.2.1
  letI : Surjective C.projection := hgeom.2.2.1
  refine ⟨composite E F b f hc C, composite_represents E k σ P F f hc C hC,
    inferInstanceAs (IsFinite (C.projection ≫ b)),
    inferInstanceAs (Etale (C.projection ≫ b)),
    inferInstanceAs (Surjective (C.projection ≫ b)), ?_⟩
  intro s
  change (C.projection ≫ b).finrank s = 32
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const C.projection b 16 hgeom.2.2.2,
    hb.2.2.2.1]

/-- A representing cover classifies maps between covers uniquely. -/
lemma map_unique (P : EvenPoint E) (C D : Cover E)
    (hC : RepresentsUnphased E P C) (hD : RepresentsUnphased E P D)
    (q r : C.space ⟶ D.space) (f g : C.family.curve ⟶ D.family.curve)
    (hq : CoverMap E C D q f) (hr : CoverMap E C D r g) : q = r := by
  let A : MarkedTest E P := ⟨C.space, C.family, C.marking, C.projection,
    C.comparison, C.cartesian, hC.1⟩
  exact congrArg Subtype.val ((hD.2 A).unique (y₁ := ⟨q, hq.1⟩) (y₂ := ⟨r, hr.1⟩)
    ⟨f, hq.2⟩ ⟨g, hr.2⟩)

lemma representing_iso (P : EvenPoint E) (C D : Cover E)
    (hC : RepresentsUnphased E P C) (hD : RepresentsUnphased E P D) :
    ∃ e : C.space ≅ D.space, e.hom ≫ D.projection = C.projection := by
  obtain ⟨q, ⟨f, hf, hfc⟩, _⟩ := hD.2
    ⟨C.space, C.family, C.marking, C.projection, C.comparison, C.cartesian, hC.1⟩
  obtain ⟨r, ⟨g, hg, hgc⟩, _⟩ := hC.2
    ⟨D.space, D.family, D.marking, D.projection, D.comparison, D.cartesian, hD.1⟩
  have hq : CoverMap E C D q.val f := ⟨q.property, hf, hfc⟩
  have hr : CoverMap E D C r.val g := ⟨r.property, hg, hgc⟩
  have hqr : q.val ≫ r.val = 𝟙 C.space := map_unique E P C C hC hC _ _ _ _
    (EvenCoverTorsor.coverMap_comp E C D C q.val f r.val g hq hr)
    (EvenCoverTorsor.coverMap_refl E C)
  have hrq : r.val ≫ q.val = 𝟙 D.space := map_unique E P D D hD hD _ _ _ _
    (EvenCoverTorsor.coverMap_comp E D C D r.val g q.val f hr hq)
    (EvenCoverTorsor.coverMap_refl E D)
  exact ⟨⟨q.val, r.val, hqr, hrq⟩, q.property⟩

lemma geometry_transfer (P : EvenPoint E) (C D : Cover E)
    (hC : RepresentsUnphased E P C) (hD : RepresentsUnphased E P D)
    (hgeom : Geometry E C 32) : Geometry E D 32 := by
  obtain ⟨e, he⟩ := representing_iso E P D C hD hC
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← he]; infer_instance
  · rw [← he]; infer_instance
  · rw [← he]; infer_instance
  · intro s
    rw [← he, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hgeom.2.2.2 s
end UnphasedCoverProof

/-- The unphased even marking functor has a finite étale surjective degree-32
representative, and every representative has precisely that geometry. -/
theorem unphased_marking_cover :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
      (E : Family S) (P : EvenPoint E),
      (∃ D : Cover E, RepresentsUnphased E P D ∧ Geometry E D 32) ∧
      (∀ D : Cover E, RepresentsUnphased E P D → Geometry E D 32) := by
  intro k _ _ S σ E P
  obtain ⟨C, hC, hg⟩ := UnphasedCoverProof.exists_cover E k σ P
  exact ⟨⟨C, hC, hg⟩, fun D hD => UnphasedCoverProof.geometry_transfer E P C D hC hD hg⟩

#print axioms unphased_marking_cover
end ArithmeticThetaPhaseFreeKeyR0219
