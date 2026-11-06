import ScopedCuspDefinitionsR0102

noncomputable section

namespace ArithmeticThetaMarkingCuspsR0102

private lemma det_entries {R : Type*} [CommRing R]
    (A : Matrix.SpecialLinearGroup (Fin 2) R) :
    A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using A.det_coe

private lemma label_cases (L : ℕ) (B : FiniteMarking L)
    (h : finiteLabel L B = finiteLabel L 1) :
    (B 0 0, B 1 0) = (1, 0) ∨ (B 0 0, B 1 0) = -(1, 0) := by
  suffices ∀ a b : ArithmeticThetaLevelCount.PrimitivePair L,
      Relation.EqvGen (fun a b => b.val = -a.val) a b →
      b.val = a.val ∨ b.val = -a.val by
    rcases this _ _ (Quot.eqvGen_exact h) with he | he
    · exact Or.inl he.symm
    · exact Or.inr (by simpa using (congrArg Neg.neg he).symm)
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

private lemma reduction_T_entry (L : ℕ) (n : ℤ) :
    reduction L (ModularGroup.T ^ n) =
      ⟨!![1, (n : ZMod L); 0, 1], by simp⟩ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    change (((ModularGroup.T ^ n) _ _ : ℤ) : ZMod L) = _
    rw [ModularGroup.coe_T_zpow]
    simp

private lemma neg_val (L : ℕ) (B : FiniteMarking L) :
    (-B).val = -B.val := by
  exact Matrix.SpecialLinearGroup.coe_neg B

private lemma signedTranslation_mem (L : ℕ) (s : Bool × ZMod L) :
    finiteLabel L (signedTranslation L s) = finiteLabel L 1 := by
  rcases s with ⟨sgn, i⟩
  dsimp [signedTranslation]
  split_ifs with h
  · unfold finiteLabel
    apply Quot.sound
    dsimp only
    rw [neg_val, reduction_T_entry]
    change (1, (0 : ZMod L)) = -(-1, -0)
    simp

  · rw [reduction_T_entry]
    unfold finiteLabel
    congr 1

private lemma translation_matrix (L : ℕ) [NeZero L] (i : ZMod L) :
    (signedTranslation L (false, i)).val = !![1, i; 0, 1] := by
  dsimp [signedTranslation]
  rw [reduction_T_entry]
  simp

private lemma negative_translation_matrix (L : ℕ) [NeZero L] (i : ZMod L) :
    (signedTranslation L (true, i)).val = !![-1, -i; 0, -1] := by
  dsimp [signedTranslation]
  rw [reduction_T_entry]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

private lemma one_ne_neg_one (L : ℕ) (hL : 3 ≤ L) :
    (1 : ZMod L) ≠ -1 := by
  intro h
  have htwo : (2 : ZMod L) = 0 := by linear_combination h
  have hd : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp htwo
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem signed_translation_fiber :
    ∀ L : ℕ, 3 ≤ L →
      ∃ e : (Bool × ZMod L) ≃ BaseFiber L,
        ∀ s : Bool × ZMod L, (e s).val = signedTranslation L s := by
  intro L hL
  have : NeZero L := ⟨by omega⟩
  let f : Bool × ZMod L → BaseFiber L := fun s =>
    ⟨signedTranslation L s, signedTranslation_mem L s⟩
  have hinj : Function.Injective f := by
    rintro ⟨b, i⟩ ⟨c, j⟩ h
    have hm : (signedTranslation L (b, i)).val =
        (signedTranslation L (c, j)).val := congrArg (fun x => x.val.val) h
    cases b <;> cases c
    · rw [translation_matrix, translation_matrix] at hm
      have hi := congrArg (fun A => A 0 1) hm
      simpa using hi
    · rw [translation_matrix, negative_translation_matrix] at hm
      have hs := congrArg (fun A => A 0 0) hm
      exact False.elim (one_ne_neg_one L hL (by simpa using hs))
    · rw [negative_translation_matrix, translation_matrix] at hm
      have hs := congrArg (fun A => A 0 0) hm
      exact False.elim (one_ne_neg_one L hL (by simpa using hs.symm))
    · rw [negative_translation_matrix, negative_translation_matrix] at hm
      have hi := congrArg (fun A => A 0 1) hm
      simpa using hi
  have hsurj : Function.Surjective f := by
    intro B
    rcases label_cases L B.val B.property with hp | hn
    · have ha : B.val 0 0 = 1 := congrArg Prod.fst hp
      have hc : B.val 1 0 = 0 := congrArg Prod.snd hp
      have hd : B.val 1 1 = 1 := by
        simpa [ha, hc] using det_entries B.val
      refine ⟨(false, B.val 0 1), ?_⟩
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      change (signedTranslation L (false, B.val 0 1)).val a b = B.val a b
      rw [translation_matrix]
      fin_cases a <;> fin_cases b <;> simp [ha, hc, hd]
    · have ha : B.val 0 0 = -1 := congrArg Prod.fst hn
      have hc : B.val 1 0 = 0 := by simpa using congrArg Prod.snd hn
      have hd : B.val 1 1 = -1 := by
        have hd' := det_entries B.val
        simp only [ha, hc, mul_zero, sub_zero, neg_one_mul] at hd'
        exact neg_eq_iff_eq_neg.mp hd'
      refine ⟨(true, -(B.val 0 1)), ?_⟩
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      change (signedTranslation L (true, -(B.val 0 1))).val a b = B.val a b
      rw [negative_translation_matrix]
      fin_cases a <;> fin_cases b <;> simp [ha, hc, hd]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

end ArithmeticThetaMarkingCuspsR0102
