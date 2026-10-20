module

public import EvenMarkingSubcoverR0216

@[expose] public section

/-! The right even-stabilizer action on the actual representing scheme. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216
namespace EvenCoverRightAction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaFourTorsion
open SchemeFourCover

variable {S : Scheme.{u}} (E : Family S)

/-- The equations of the action, before invertibility has been proved. -/
def Maps (D : Cover E) (A : Mat4) (q : D.space ⟶ D.space) : Prop :=
  q ≫ D.projection = D.projection ∧
  q ≫ D.marking.x.val ≫ D.comparison = changedX D.family D.marking A ≫ D.comparison ∧
  q ≫ D.marking.y.val ≫ D.comparison = changedY D.family D.marking A ≫ D.comparison

lemma changed_x {T : Scheme.{u}} (F : Family T) (M N : FullLevel F 4)
    (A : Mat4) (h : Changes F M N A) : N.x.val = changedX F M A :=
  congrArg Subtype.val h.1

lemma changed_y {T : Scheme.{u}} (F : Family T) (M N : FullLevel F 4)
    (A : Mat4) (h : Changes F M N A) : N.y.val = changedY F M A :=
  congrArg Subtype.val h.2

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

include k σ in
lemma matches_change (P : EvenPoint E) (z : Γ(S, ⊤))
    {T : Scheme.{u}} (F : Family T) (M N : FullLevel F 4)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (A : EvenGroup)
    (hN : Changes F M N A.val) (hm : Matches E P z F M b f) :
    Matches E P z F N b f := by
  constructor
  · rw [(scheme_four_marking_action k T (b ≫ σ) F M).2.2.2 N A.val A.property hN]
    exact hm.1
  · obtain ⟨w, hw, _⟩ := (scheme_miller_phase k T (b ≫ σ) F N).1
    have he := scheme_phase_marking_invariance k T (b ≫ σ) F M N A.val
      A.property.1 hN (b.appTop z) w hm.2 hw
    exact he ▸ hw

include k σ in
lemma maps_exists (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E)
    (hD : RepresentsEven E P z D) (A : EvenGroup) :
    ∃ q : D.space ⟶ D.space, Maps E D A.val q := by
  obtain ⟨N, hN, _⟩ := (scheme_four_marking_action k D.space
    (D.projection ≫ σ) D.family D.marking).1 A.val A.property.1
  have hm := matches_change E k σ P z D.family D.marking N D.projection
    D.comparison A hN hD.1
  obtain ⟨q, ⟨h, hh, hf⟩, _⟩ := hD.2 D.space D.family N
    D.projection D.comparison D.cartesian hm
  refine ⟨q.val, q.property, ?_, ?_⟩
  · rw [← Category.assoc, ← hh.2.2.2.1, Category.assoc, hf, changed_x _ _ _ _ hN]
  · rw [← Category.assoc, ← hh.2.2.2.2, Category.assoc, hf, changed_y _ _ _ _ hN]

include k σ in
lemma maps_unique (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E)
    (hD : RepresentsEven E P z D) (A : Mat4)
    (q r : D.space ⟶ D.space) (hq : Maps E D A q) (hr : Maps E D A r) : q = r := by
  obtain ⟨N, h, hh, hf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D
    D.family D.projection D.comparison D.cartesian q hq.1
  have hm : Matches E P z D.family N D.projection D.comparison := by
    have H := EvenMarkingSubcover.matches_pullback E P z D.family D.family D.marking N
      D.projection D.comparison q h hh hD.1
    simpa only [hq.1, hf] using H
  have hx : N.x.val ≫ D.comparison = q ≫ D.marking.x.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.1, Category.assoc, hf]
  have hy : N.y.val ≫ D.comparison = q ≫ D.marking.y.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.2, Category.assoc, hf]
  have hr' := marked_factor E k σ D.family D.family D.projection D.comparison D.cartesian
    D.projection D.comparison D.cartesian r hr.1 D.marking N
    (hx.trans (hq.2.1.trans hr.2.1.symm)) (hy.trans (hq.2.2.trans hr.2.2.symm))
  obtain ⟨a, _, hu⟩ := hD.2 D.space D.family N D.projection D.comparison D.cartesian hm
  exact congrArg Subtype.val ((hu ⟨q, hq.1⟩ ⟨h, hh, hf⟩).trans (hu ⟨r, hr.1⟩ hr').symm)

include k σ in
lemma maps_one (D : Cover E) : Maps E D 1 (𝟙 D.space) := by
  have h := (scheme_four_marking_action k D.space (D.projection ≫ σ) D.family D.marking).2.1
  refine ⟨Category.id_comp _, ?_, ?_⟩
  · simpa only [Category.id_comp] using congrArg (fun f => f ≫ D.comparison) (changed_x _ _ _ _ h)
  · simpa only [Category.id_comp] using congrArg (fun f => f ≫ D.comparison) (changed_y _ _ _ _ h)

/-- Changed coordinates commute with a marked Cartesian comparison. -/
lemma changed_comp {T : Scheme.{u}} (F : Family T) (M : FullLevel E 4)
    (N : FullLevel F 4) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hf : MarkedCartesian E F M N b f) (A : Mat4) :
    changedX F N A ≫ f = b ≫ changedX E M A ∧
    changedY F N A ≫ f = b ≫ changedY E M A := by
  have hn := CartesianFullMarking.multiple_comp E F b f hf.2.1 hf.2.2.1
  constructor
  · exact CartesianFullMarking.mul_comp E F b f hf.2.2.1 _ _ _ _
      (hn N.x M.x hf.2.2.2.1 _) (hn N.y M.y hf.2.2.2.2 _)
  · exact CartesianFullMarking.mul_comp E F b f hf.2.2.1 _ _ _ _
      (hn N.x M.x hf.2.2.2.1 _) (hn N.y M.y hf.2.2.2.2 _)

include k σ in
lemma maps_mul (D : Cover E) (A B : Mat4) (hA : A.det = 1) (hB : B.det = 1)
    (q r : D.space ⟶ D.space) (hq : Maps E D A q) (hr : Maps E D B r) :
    Maps E D (A * B) (q ≫ r) := by
  obtain ⟨N, hN, _⟩ := (scheme_four_marking_action k D.space
    (D.projection ≫ σ) D.family D.marking).1 A hA
  obtain ⟨L, hL, _⟩ := (scheme_four_marking_action k D.space
    (D.projection ≫ σ) D.family N).1 B hB
  have hNL := (scheme_four_marking_action k D.space (D.projection ≫ σ)
    D.family D.marking).2.2.1 N L A B hA hB hN hL
  obtain ⟨h, hh, hf⟩ := marked_factor E k σ D.family D.family
    D.projection D.comparison D.cartesian D.projection D.comparison D.cartesian
    q hq.1 D.marking N
    (by rw [changed_x _ _ _ _ hN]; exact hq.2.1.symm)
    (by rw [changed_y _ _ _ _ hN]; exact hq.2.2.symm)
  have hc := changed_comp D.family D.family D.marking N q h hh B
  refine ⟨by rw [Category.assoc, hr.1, hq.1], ?_, ?_⟩
  · calc
      (q ≫ r) ≫ D.marking.x.val ≫ D.comparison =
          q ≫ changedX D.family D.marking B ≫ D.comparison := by rw [Category.assoc, hr.2.1]
      _ = changedX D.family N B ≫ D.comparison := by rw [← Category.assoc, ← hc.1, Category.assoc, hf]
      _ = changedX D.family D.marking (A * B) ≫ D.comparison := by
        rw [← changed_x _ _ _ _ hL, changed_x _ _ _ _ hNL]
  · calc
      (q ≫ r) ≫ D.marking.y.val ≫ D.comparison =
          q ≫ changedY D.family D.marking B ≫ D.comparison := by rw [Category.assoc, hr.2.2]
      _ = changedY D.family N B ≫ D.comparison := by rw [← Category.assoc, ← hc.2, Category.assoc, hf]
      _ = changedY D.family D.marking (A * B) ≫ D.comparison := by
        rw [← changed_y _ _ _ _ hL, changed_y _ _ _ _ hNL]

set_option maxRecDepth 10000 in
/-- The finite stabilizer is closed under the determinant-one inverse. -/
lemma inverse_even : ∀ A : Mat4, PreservesEven A → PreservesEven A.adjugate := by
  decide

lemma one_even : PreservesEven (1 : Mat4) := by decide

include k σ in
lemma iso_exists (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E)
    (hD : RepresentsEven E P z D) (A : EvenGroup) :
    ∃! q : D.space ≅ D.space, Acts E D A.val q := by
  let B : EvenGroup := ⟨A.val.adjugate, inverse_even A.val A.property⟩
  have hab : A.val * B.val = 1 := by
    change A.val * A.val.adjugate = 1
    rw [Matrix.mul_adjugate, A.property.1, one_smul]
  have hba : B.val * A.val = 1 := by
    change A.val.adjugate * A.val = 1
    rw [Matrix.adjugate_mul, A.property.1, one_smul]
  obtain ⟨q, hq⟩ := maps_exists E k σ P z D hD A
  obtain ⟨r, hr⟩ := maps_exists E k σ P z D hD B
  have hqr : q ≫ r = 𝟙 D.space := by
    apply maps_unique E k σ P z D hD 1 _ _ _ (maps_one E k σ D)
    simpa only [hab] using maps_mul E k σ D A.val B.val A.property.1 B.property.1 q r hq hr
  have hrq : r ≫ q = 𝟙 D.space := by
    apply maps_unique E k σ P z D hD 1 _ _ _ (maps_one E k σ D)
    simpa only [hba] using maps_mul E k σ D B.val A.val B.property.1 A.property.1 r q hr hq
  let e : D.space ≅ D.space := ⟨q, r, hqr, hrq⟩
  refine ⟨e, hq, ?_⟩
  intro e' he'
  apply CategoryTheory.Iso.ext
  exact maps_unique E k σ P z D hD A.val e'.hom q he' hq

end EvenCoverRightAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 EvenCoverRightAction

/-- The unique actual right action, with identity and ordered composition. -/
theorem even_cover_right_action :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → (∀ A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup, ∃! q : CategoryTheory.Iso D.space D.space, ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q) ∧ (∀ q : CategoryTheory.Iso D.space D.space, ArithmeticThetaEvenMarkingTorsorR0216.Acts E D (1 : ArithmeticThetaFourTorsion.Mat4) q → q.hom = CategoryTheory.CategoryStruct.id D.space) ∧ (∀ (A B : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup) (q r s : CategoryTheory.Iso D.space D.space), ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q → ArithmeticThetaEvenMarkingTorsorR0216.Acts E D B.val r → ArithmeticThetaEvenMarkingTorsorR0216.Acts E D (A.val * B.val) s → CategoryTheory.CategoryStruct.comp q.hom r.hom = s.hom) := by
  intro k _ _ S σ E P z hz D hD
  refine ⟨?_, ?_, ?_⟩
  · exact iso_exists E k σ P z D hD
  · intro q hq
    exact maps_unique E k σ P z D hD 1 q.hom (𝟙 D.space) hq (maps_one E k σ D)
  · intro A B q r s hq hr hs
    exact maps_unique E k σ P z D hD (A.val * B.val) (q.hom ≫ r.hom) s.hom
      (maps_mul E k σ D A.val B.val A.property.1 B.property.1 q.hom r.hom hq hr) hs

#print axioms even_cover_right_action
end ArithmeticThetaEvenMarkingTorsorR0216
