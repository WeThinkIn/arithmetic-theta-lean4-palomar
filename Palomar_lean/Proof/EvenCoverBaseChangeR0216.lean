module

public import EvenMarkingSubcoverR0216

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaUniversalEvaluationR0213
open SchemeFourCover EvenMarkingSubcover

variable {S : Scheme.{u}} (E : Family S)

lemma evenPoint_over {X : Scheme.{u}} (G : Family X) (N : FullLevel G 4) :
    evenPoint G N ≫ G.p = 𝟙 X :=
  (G.law.mul (𝟙 X) (multiple G (𝟙 X) 2 N.x)
    (multiple G (𝟙 X) 2 N.y)).property

lemma matches_comp_iff (P : EvenPoint E) (z : Γ(S, ⊤))
    {T X : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : Cartesian E F b f) (Q : EvenPoint F)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val)
    (G : Family X) (N : FullLevel G 4) (a : X ⟶ T) (g : G.curve ⟶ F.curve)
    (hG : Cartesian F G a g) :
    Matches F Q (b.appTop z) G N a g ↔ Matches E P z G N (a ≫ b) (g ≫ f) := by
  have he : evenPoint G N ≫ g = a ≫ Q.point.val ↔
      evenPoint G N ≫ (g ≫ f) = (a ≫ b) ≫ P.point.val := by
    constructor
    · intro h
      rw [← Category.assoc, h, Category.assoc, hQ, Category.assoc]
    · intro h
      apply hc.1.hom_ext
      · simpa only [Category.assoc, hQ] using h
      · rw [Category.assoc, hG.1.w, ← Category.assoc, evenPoint_over,
          Category.id_comp, Category.assoc, Q.point.property, Category.comp_id]
  exact and_congr he (by simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply])

lemma parameter_ext (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E) (hD : RepresentsEven E P z D)
    {X : Scheme.{u}} (q r : X ⟶ D.space)
    (hp : q ≫ D.projection = r ≫ D.projection)
    (hx : q ≫ D.marking.x.val ≫ D.comparison = r ≫ D.marking.x.val ≫ D.comparison)
    (hy : q ≫ D.marking.y.val ≫ D.comparison = r ≫ D.marking.y.val ≫ D.comparison) :
    q = r := by
  let a := q ≫ D.projection
  let G := SchemeFamilyBaseChange.baseChangeFamily E a
  let g := pullback.fst E.p a
  have hG : Cartesian E G a g :=
    ⟨IsPullback.of_hasPullback E.p a, SchemeFamilyBaseChange.baseChangeLaw_zero E a,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative E a⟩
  obtain ⟨N, h, hh, hf⟩ := marking_over_parameter E k σ D G a g hG q rfl
  have hm : Matches E P z G N a g := by
    have H := matches_pullback E P z D.family G D.marking N D.projection D.comparison q h hh hD.1
    simpa only [hf] using H
  obtain ⟨h', hh', hf'⟩ := marked_factor E k σ D.family G
    D.projection D.comparison D.cartesian a g hG r hp.symm D.marking N
    (by rw [← hf, ← Category.assoc, hh.2.2.2.1, Category.assoc]; exact hx)
    (by rw [← hf, ← Category.assoc, hh.2.2.2.2, Category.assoc]; exact hy)
  exact congrArg Subtype.val ((hD.2 X G N a g hG hm).unique
    (y₁ := ⟨q, rfl⟩) (y₂ := ⟨r, hp.symm⟩) ⟨h, hh, hf⟩ ⟨h', hh', hf'⟩)

lemma comparison_pullback (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E) (hD : RepresentsEven E P z D)
    {T : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : Cartesian E F b f) (Q : EvenPoint F)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val)
    (C : Cover F) (hC : RepresentsEven F Q (b.appTop z) C)
    (q : C.space ⟶ D.space) (hq : q ≫ D.projection = C.projection ≫ b)
    (h : C.family.curve ⟶ D.family.curve)
    (hh : MarkedCartesian D.family C.family D.marking C.marking q h)
    (hf : h ≫ D.comparison = C.comparison ≫ f) :
    IsPullback q C.projection D.projection b := by
  have lift_exists (s : PullbackCone D.projection b) :
      ∃ r : s.pt ⟶ C.space, r ≫ q = s.fst ∧ r ≫ C.projection = s.snd := by
    let G := SchemeFamilyBaseChange.baseChangeFamily F s.snd
    let g := pullback.fst F.p s.snd
    have hG : Cartesian F G s.snd g :=
      ⟨IsPullback.of_hasPullback F.p s.snd,
        SchemeFamilyBaseChange.baseChangeLaw_zero F s.snd,
        SchemeFamilyBaseChange.baseChangeFamily_multiplicative F s.snd⟩
    have hGE := cartesian_comp E F G b f hc s.snd g hG
    obtain ⟨N, d, hd, hdf⟩ := marking_over_parameter E k σ D G
      (s.snd ≫ b) (g ≫ f) hGE s.fst s.condition
    have hmE : Matches E P z G N (s.snd ≫ b) (g ≫ f) := by
      have H := matches_pullback E P z D.family G D.marking N
        D.projection D.comparison s.fst d hd hD.1
      simpa only [s.condition, hdf] using H
    have hmF := (matches_comp_iff E P z F b f hc Q hQ G N s.snd g hG).mpr hmE
    obtain ⟨r, ⟨c, hcc, hcf⟩, _⟩ := hC.2 s.pt G N s.snd g hG hmF
    have hr : (r.val ≫ q) ≫ D.projection = s.snd ≫ b := by
      rw [Category.assoc, hq, ← Category.assoc, r.property]
    have he := (hD.2 s.pt G N (s.snd ≫ b) (g ≫ f) hGE hmE).unique
      (y₁ := ⟨r.val ≫ q, hr⟩) (y₂ := ⟨s.fst, s.condition⟩)
      ⟨c ≫ h, marked_comp D.family C.family G D.marking C.marking N q h r.val c hh hcc,
        by rw [Category.assoc, hf, ← Category.assoc, hcf]⟩ ⟨d, hd, hdf⟩
    exact ⟨r.val, congrArg Subtype.val he, r.property⟩
  have cx : C.marking.x.val ≫ C.comparison ≫ F.p = C.projection := by
    rw [C.cartesian.1.w, ← Category.assoc, C.marking.x.property, Category.id_comp]
  have cy : C.marking.y.val ≫ C.comparison ≫ F.p = C.projection := by
    rw [C.cartesian.1.w, ← Category.assoc, C.marking.y.property, Category.id_comp]
  have hx : C.marking.x.val ≫ C.comparison ≫ f = q ≫ D.marking.x.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.1, Category.assoc]
  have hy : C.marking.y.val ≫ C.comparison ≫ f = q ≫ D.marking.y.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.2, Category.assoc]
  classical
  let l (s : PullbackCone D.projection b) := (lift_exists s).choose
  have hl (s : PullbackCone D.projection b) := (lift_exists s).choose_spec
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hq l
    (fun s => (hl s).1) (fun s => (hl s).2) ?_)
  intro s m hm hp
  apply parameter_ext F k (b ≫ σ) Q (b.appTop z) C hC m (l s)
  · exact hp.trans (hl s).2.symm
  · apply hc.1.hom_ext
    · simp only [Category.assoc]
      rw [hx, ← Category.assoc m q, hm, ← Category.assoc (l s) q, (hl s).1]
    · simpa only [Category.assoc, cx] using hp.trans (hl s).2.symm
  · apply hc.1.hom_ext
    · simp only [Category.assoc]
      rw [hy, ← Category.assoc m q, hm, ← Category.assoc (l s) q, (hl s).1]
    · simpa only [Category.assoc, cy] using hp.trans (hl s).2.symm

end ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverBaseChange

namespace ArithmeticThetaEvenMarkingTorsorR0216
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open SchemeFourCover EvenMarkingSubcover EvenCoverBaseChange

/-- The actual even marking cover commutes with every pointed Cartesian base change. -/
theorem even_cover_base_change :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve), ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f → ∀ (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover F), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven F Q (b.appTop z) C → ∃! q : {q : Quiver.Hom C.space D.space // CategoryTheory.CategoryStruct.comp q D.projection = CategoryTheory.CategoryStruct.comp C.projection b}, CategoryTheory.IsPullback q.val C.projection D.projection b ∧ ∃ h : Quiver.Hom C.family.curve D.family.curve, ArithmeticThetaSchemeLevelR0204.MarkedCartesian D.family C.family D.marking C.marking q.val h ∧ CategoryTheory.CategoryStruct.comp h D.comparison = CategoryTheory.CategoryStruct.comp C.comparison f := by
  intro k _ _ S σ E P z _hz D hD T F b f hc Q hQ C hC
  have hCE := cartesian_comp E F C.family b f hc
    C.projection C.comparison C.cartesian
  have hm := (matches_comp_iff E P z F b f hc Q hQ
    C.family C.marking C.projection C.comparison C.cartesian).mp hC.1
  obtain ⟨q, ⟨h, hh, hf⟩, hu⟩ := hD.2 C.space C.family C.marking
    (C.projection ≫ b) (C.comparison ≫ f) hCE hm
  refine ⟨q, ⟨comparison_pullback E k σ P z D hD F b f hc Q hQ C hC
    q.val q.property h hh hf, h, hh, hf⟩, ?_⟩
  intro r hr
  exact hu r hr.2

#print axioms even_cover_base_change
end ArithmeticThetaEvenMarkingTorsorR0216
