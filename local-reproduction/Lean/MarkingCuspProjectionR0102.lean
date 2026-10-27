import CongruenceMarkingQuotientR0102
import RationalCuspClassificationR0102
import SignedTranslationFiberR0102

noncomputable section

namespace ArithmeticThetaMarkingCuspsR0102
open ArithmeticThetaIntegralCuspsR0102

private lemma finiteLabel_cases (L : ℕ) (A B : FiniteMarking L)
    (h : finiteLabel L A = finiteLabel L B) :
    (B 0 0, B 1 0) = (A 0 0, A 1 0) ∨
    (B 0 0, B 1 0) = -(A 0 0, A 1 0) := by
  suffices ∀ a b : ArithmeticThetaLevelCount.PrimitivePair L,
      Relation.EqvGen (fun a b => b.val = -a.val) a b →
      b.val = a.val ∨ b.val = -a.val by
    exact this _ _ (Quot.eqvGen_exact h)
  intro a b he
  induction he with
  | rel a b h => exact Or.inr h
  | refl a => exact Or.inl rfl
  | symm a b h ih =>
    rcases ih with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  | trans a b c h k ih ik =>
    rcases ih with h | h <;> rcases ik with k | k
    · exact Or.inl (k.trans h)
    · exact Or.inr (by rw [k, h])
    · exact Or.inr (k.trans h)
    · exact Or.inl (by rw [k, h, neg_neg])

/-- Left multiplication preserves equality of signed first-column labels. -/
lemma finiteLabel_mul_congr (L : ℕ) (C A B : FiniteMarking L)
    (h : finiteLabel L A = finiteLabel L B) :
    finiteLabel L (C * A) = finiteLabel L (C * B) := by
  rcases finiteLabel_cases L A B h with hp | hn
  · have h0 : B 0 0 = A 0 0 := congrArg Prod.fst hp
    have h1 : B 1 0 = A 1 0 := congrArg Prod.snd hp
    unfold finiteLabel
    congr 1
    apply Subtype.ext
    apply Prod.ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  · have h0 : B 0 0 = -(A 0 0) := congrArg Prod.fst hn
    have h1 : B 1 0 = -(A 1 0) := congrArg Prod.snd hn
    apply Quot.sound
    apply Prod.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1, mul_neg, add_comm]

/-- Translate the identity-label fiber to the label fiber of any finite marking. -/
def finiteLabelFiberEquiv (L : ℕ) (A : FiniteMarking L) :
    BaseFiber L ≃ {B : FiniteMarking L // finiteLabel L B = finiteLabel L A} where
  toFun B := ⟨A * B.val, by
    simpa using finiteLabel_mul_congr L A B.val 1 B.property⟩
  invFun B := ⟨A⁻¹ * B.val, by
    simpa using finiteLabel_mul_congr L A⁻¹ B.val A B.property⟩
  left_inv B := by apply Subtype.ext; simp
  right_inv B := by apply Subtype.ext; simp

/-- The unique finite-marking projection and its explicitly parameterized fibers. -/
theorem finite_marking_cusp_projection :
    ∀ L : ℕ, 3 ≤ L →
      ∃! π : FiniteMarking L → RationalCusps L,
        (∀ A : IntegralMarking, π (reduction L A) = cusp L (boundary A)) ∧
        (∀ A : IntegralMarking,
          ∃ e : (Bool × ZMod L) ≃
              {B : FiniteMarking L // π B = cusp L (boundary A)},
            ∀ s : Bool × ZMod L,
              (e s).val = reduction L A * signedTranslation L s) := by
  intro L hL
  obtain ⟨c, hc, _, _⟩ := rational_cusp_classification L hL
  obtain ⟨t, ht⟩ := signed_translation_fiber L hL
  have hs := (congruence_marking_quotient L hL).1
  let π : FiniteMarking L → RationalCusps L := fun B => c.symm (finiteLabel L B)
  have hπ (A : IntegralMarking) : π (reduction L A) = cusp L (boundary A) := by
    apply c.injective
    change c (c.symm (finiteLabel L (reduction L A))) = _
    rw [c.apply_symm_apply, hc]
    rfl
  refine ⟨π, ⟨hπ, ?_⟩, ?_⟩
  · intro A
    have hf (B : FiniteMarking L) :
        finiteLabel L B = finiteLabel L (reduction L A) ↔
          π B = cusp L (boundary A) := by
      rw [← hπ A]
      exact c.symm.injective.eq_iff.symm
    let u : {B : FiniteMarking L // finiteLabel L B = finiteLabel L (reduction L A)} ≃
        {B : FiniteMarking L // π B = cusp L (boundary A)} :=
      { toFun := fun B => ⟨B.val, (hf B.val).mp B.property⟩
        invFun := fun B => ⟨B.val, (hf B.val).mpr B.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨(t.trans (finiteLabelFiberEquiv L (reduction L A))).trans u, ?_⟩
    intro s
    change reduction L A * (t s).val = _
    rw [ht]
  · intro π' hπ'
    funext B
    obtain ⟨A, rfl⟩ := hs B
    exact (hπ'.1 A).trans (hπ A).symm

end ArithmeticThetaMarkingCuspsR0102
