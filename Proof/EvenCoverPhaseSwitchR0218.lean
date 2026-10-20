module

public import ReversalCharacterR0218
public import SchemePairingReversalR0218

@[expose] public section

/-! The unique comparison of the two actual representing even-marking covers. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
namespace EvenCoverPhaseSwitch
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaFourTorsion
open ArithmeticThetaEvenMarkingTorsorR0216.SchemeFourCover
open ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction

variable {S : Scheme.{u}} (E : Family S)

def Maps (D C : Cover E) (A : Mat4) (q : D.space ⟶ C.space) : Prop :=
  q ≫ C.projection = D.projection ∧
  q ≫ C.marking.x.val ≫ C.comparison = changedX D.family D.marking A ≫ D.comparison ∧
  q ≫ C.marking.y.val ≫ C.comparison = changedY D.family D.marking A ≫ D.comparison

/-- Composition of column changes does not require determinant one. -/
lemma changed_after {T : Scheme.{u}} (F : Family T) (M N : FullLevel F 4)
    (A B : Mat4) (hN : Changes F M N A) :
    changedX F N B = changedX F M (A * B) ∧
    changedY F N B = changedY F M (A * B) := by
  letI := SchemeFourMarkingActionR0215.pointGroup F (𝟙 T)
  let basis (L : FullLevel F 4) := ![L.x, L.y]
  have hk : ∀ i, basis M i ^ 4 = 1 := by
    intro i
    fin_cases i
    · exact (SchemeFourMarkingActionR0215.multiple_pow F (𝟙 T) 4 M.x).symm.trans M.killed_x
    · exact (SchemeFourMarkingActionR0215.multiple_pow F (𝟙 T) 4 M.y).symm.trans M.killed_y
  have hn : basis N = ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211.act
      (basis M) A := by
    simp only [Changes, SchemeFourMarkingActionR0215.multiple_pow] at hN
    funext i
    fin_cases i
    · exact hN.1
    · exact hN.2
  have h := ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211.act_mul
    (basis M) hk A B
  rw [← hn] at h
  simp only [changedX, changedY, SchemeFourMarkingActionR0215.multiple_pow]
  constructor
  · exact congrArg Subtype.val (congrFun h 0)
  · exact congrArg Subtype.val (congrFun h 1)

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

include k σ in
lemma maps_unique (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hC : RepresentsEven E P z C) (A : Mat4)
    (q r : D.space ⟶ C.space) (hq : Maps E D C A q) (hr : Maps E D C A r) : q = r := by
  obtain ⟨N, h, hh, hf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ C
    D.family D.projection D.comparison D.cartesian q hq.1
  have hm : Matches E P z D.family N D.projection D.comparison := by
    have H := EvenMarkingSubcover.matches_pullback E P z C.family D.family C.marking N
      C.projection C.comparison q h hh hC.1
    simpa only [hq.1, hf] using H
  have hx : N.x.val ≫ D.comparison = q ≫ C.marking.x.val ≫ C.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.1, Category.assoc]
  have hy : N.y.val ≫ D.comparison = q ≫ C.marking.y.val ≫ C.comparison := by
    rw [← hf, ← Category.assoc, hh.2.2.2.2, Category.assoc]
  have hr' := marked_factor E k σ C.family D.family C.projection C.comparison C.cartesian
    D.projection D.comparison D.cartesian r hr.1 C.marking N
    (hx.trans (hq.2.1.trans hr.2.1.symm)) (hy.trans (hq.2.2.trans hr.2.2.symm))
  obtain ⟨a, _, hu⟩ := hC.2 D.space D.family N D.projection D.comparison D.cartesian hm
  exact congrArg Subtype.val ((hu ⟨q, hq.1⟩ ⟨h, hh, hf⟩).trans (hu ⟨r, hr.1⟩ hr').symm)

include k σ in
lemma maps_comp (D C B : Cover E) (A H : Mat4)
    (N : FullLevel D.family 4) (hN : Changes D.family D.marking N A)
    (q : D.space ⟶ C.space) (r : C.space ⟶ B.space)
    (hq : Maps E D C A q) (hr : Maps E C B H r) : Maps E D B (A * H) (q ≫ r) := by
  obtain ⟨h, hh, hf⟩ := marked_factor E k σ C.family D.family
    C.projection C.comparison C.cartesian D.projection D.comparison D.cartesian
    q hq.1 C.marking N
    (by rw [changed_x _ _ _ _ hN]; exact hq.2.1.symm)
    (by rw [changed_y _ _ _ _ hN]; exact hq.2.2.symm)
  have hc := changed_comp C.family D.family C.marking N q h hh H
  have ha := changed_after D.family D.marking N A H hN
  refine ⟨by rw [Category.assoc, hr.1, hq.1], ?_, ?_⟩
  · calc
      (q ≫ r) ≫ B.marking.x.val ≫ B.comparison =
          q ≫ changedX C.family C.marking H ≫ C.comparison := by rw [Category.assoc, hr.2.1]
      _ = changedX D.family N H ≫ D.comparison := by rw [← Category.assoc, ← hc.1, Category.assoc, hf]
      _ = changedX D.family D.marking (A * H) ≫ D.comparison := by rw [ha.1]
  · calc
      (q ≫ r) ≫ B.marking.y.val ≫ B.comparison =
          q ≫ changedY C.family C.marking H ≫ C.comparison := by rw [Category.assoc, hr.2.2]
      _ = changedY D.family N H ≫ D.comparison := by rw [← Category.assoc, ← hc.2, Category.assoc, hf]
      _ = changedY D.family D.marking (A * H) ≫ D.comparison := by rw [ha.2]

include k σ in
lemma maps_exists (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hD : RepresentsEven E P z D) (hC : RepresentsEven E P (-z) C) :
    ∃ q : D.space ⟶ C.space, Maps E D C reversal q := by
  obtain ⟨N, hN, _⟩ := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).1
  have hrev := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).2 N hN
  have hm : Matches E P (-z) D.family N D.projection D.comparison := by
    constructor
    · rw [hrev.2.1]; exact hD.1.1
    · simpa only [map_neg] using hrev.2.2.1 (D.projection.appTop z) hD.1.2
  obtain ⟨q, ⟨h, hh, hf⟩, _⟩ := hC.2 D.space D.family N
    D.projection D.comparison D.cartesian hm
  refine ⟨q.val, q.property, ?_, ?_⟩
  · rw [← Category.assoc, ← hh.2.2.2.1, Category.assoc, hf, changed_x _ _ _ _ hN]
  · rw [← Category.assoc, ← hh.2.2.2.2, Category.assoc, hf, changed_y _ _ _ _ hN]

include k σ in
lemma maps_inverse (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hD : RepresentsEven E P z D)
    (q : D.space ⟶ C.space) (r : C.space ⟶ D.space)
    (hq : Maps E D C reversal q) (hr : Maps E C D reversal r) :
    q ≫ r = 𝟙 D.space := by
  obtain ⟨N, hN, _⟩ := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).1
  apply maps_unique E k σ P z D D hD 1 _ _ _ (EvenCoverRightAction.maps_one E k σ D)
  simpa only [reversal_character.1] using maps_comp E k σ D C D reversal reversal N hN q r hq hr

include k σ in
lemma switch_exists (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hD : RepresentsEven E P z D) (hC : RepresentsEven E P (-z) C) :
    ∃! q : D.space ≅ C.space, Switches E D C q := by
  obtain ⟨q, hq⟩ := maps_exists E k σ P z D C hD hC
  obtain ⟨r, hr⟩ := maps_exists E k σ P (-z) C D hC (by simpa only [neg_neg] using hD)
  let e : D.space ≅ C.space :=
    ⟨q, r, maps_inverse E k σ P z D C hD q r hq hr,
      maps_inverse E k σ P (-z) C D hC r q hr hq⟩
  refine ⟨e, hq, ?_⟩
  intro e' he'
  apply Iso.ext
  exact maps_unique E k σ P (-z) D C hC reversal e'.hom q he' hq

include k σ in
lemma switch_inverse (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hD : RepresentsEven E P z D) (hC : RepresentsEven E P (-z) C)
    (q : D.space ≅ C.space) (hq : Switches E D C q) : Switches E C D q.symm := by
  obtain ⟨r, hr⟩ := maps_exists E k σ P (-z) C D hC (by simpa only [neg_neg] using hD)
  have hqr := maps_inverse E k σ P z D C hD q.hom r hq hr
  have he : r = q.inv := by
    calc
      r = q.inv ≫ (q.hom ≫ r) := by simp
      _ = q.inv := by rw [hqr, Category.comp_id]
  change Maps E C D reversal q.inv
  rw [← he]
  exact hr

include k σ in
lemma switch_equivariant (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E)
    (hC : RepresentsEven E P (-z) C) (q : D.space ≅ C.space)
    (hq : Switches E D C q) (A : Mat4) (hA : PreservesEven A)
    (a : D.space ≅ D.space) (b : C.space ≅ C.space)
    (ha : Acts E D A a) (hb : Acts E C (conjugate A) b) :
    a.hom ≫ q.hom = q.hom ≫ b.hom := by
  obtain ⟨N, hN, _⟩ := (scheme_four_marking_action k D.space
    (D.projection ≫ σ) D.family D.marking).1 A hA.1
  obtain ⟨L, hL, _⟩ := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).1
  have he : reversal * conjugate A = A * reversal := by
    simp only [conjugate, ← mul_assoc, reversal_character.1, one_mul]
  apply maps_unique E k σ P (-z) D C hC (A * reversal)
  · exact maps_comp E k σ D D C A reversal N hN a.hom q.hom ha hq
  · simpa only [he] using maps_comp E k σ D C C reversal (conjugate A) L hL q.hom b.hom hq hb

end EvenCoverPhaseSwitch
open EvenCoverPhaseSwitch

/-- Opposite pairing covers are uniquely isomorphic by first-half reversal. -/
theorem even_cover_phase_switch :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D C : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P (-z) C → (∃! q : CategoryTheory.Iso (D.space) (C.space), ArithmeticThetaPhaseSwitchR0218.Switches E D C q) ∧ (∀ (q : CategoryTheory.Iso (D.space) (C.space)) (h : ArithmeticThetaPhaseSwitchR0218.Switches E D C q), ArithmeticThetaPhaseSwitchR0218.Switches E C D q.symm ∧ (∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∀ (a : CategoryTheory.Iso (D.space) (D.space)) (b : CategoryTheory.Iso (C.space) (C.space)), ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A a → ArithmeticThetaEvenMarkingTorsorR0216.Acts E C (ArithmeticThetaPhaseSwitchR0218.conjugate A) b → CategoryTheory.CategoryStruct.comp (a.hom) (q.hom) = CategoryTheory.CategoryStruct.comp (q.hom) (b.hom))) := by
  intro k _ _ S σ E P z _ D C hD hC
  refine ⟨switch_exists E k σ P z D C hD hC, ?_⟩
  intro q hq
  exact ⟨switch_inverse E k σ P z D C hD hC q hq,
    switch_equivariant E k σ P z D C hC q hq⟩

#print axioms even_cover_phase_switch
end ArithmeticThetaPhaseSwitchR0218
