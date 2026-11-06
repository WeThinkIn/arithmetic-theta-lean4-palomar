module

public import ScopedCuspDefinitionsR0102

@[expose] public section

noncomputable section
namespace ArithmeticThetaIntegralCuspsR0102
open Matrix Matrix.SpecialLinearGroup

private lemma entry_mul (A B : Marking) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma det_entries {R : Type*} [CommRing R]
    (A : SpecialLinearGroup (Fin 2) R) :
    A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using A.det_coe

private lemma label_cases (L : ℕ) (A B : Marking)
    (h : signedLabel L A = signedLabel L B) :
    (primitiveLabel L B).val = (primitiveLabel L A).val ∨
    (primitiveLabel L B).val = -(primitiveLabel L A).val := by
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

private lemma unsigned_fiber (L : ℕ) (A B : Marking)
    (h : (primitiveLabel L B).val = (primitiveLabel L A).val) : MarkingRel L A B := by
  let ρ := SpecialLinearGroup.map (Int.castRingHom (ZMod L)) (n := Fin 2)
  let C := ρ (A⁻¹ * B)
  have ha : (B 0 0 : ZMod L) = (A 0 0 : ZMod L) := congrArg Prod.fst h
  have hc : (B 1 0 : ZMod L) = (A 1 0 : ZMod L) := congrArg Prod.snd h
  have c00 : C 0 0 = 1 := by
    change (((A⁻¹ * B) 0 0 : ℤ) : ZMod L) = 1
    rw [entry_mul, Int.cast_add, Int.cast_mul, Int.cast_mul, ha, hc]
    have hh := congrArg (fun X : Marking => (X 0 0 : ZMod L)) (inv_mul_cancel A)
    simpa only [entry_mul, Int.cast_add, Int.cast_mul, coe_one, Matrix.one_apply,
      if_pos, if_neg, ite_false, Fin.zero_ne_one, one_ne_zero, Int.cast_one, Int.cast_zero] using hh
  have c10 : C 1 0 = 0 := by
    change (((A⁻¹ * B) 1 0 : ℤ) : ZMod L) = 0
    rw [entry_mul, Int.cast_add, Int.cast_mul, Int.cast_mul, ha, hc]
    have hh := congrArg (fun X : Marking => (X 1 0 : ZMod L)) (inv_mul_cancel A)
    simpa only [entry_mul, Int.cast_add, Int.cast_mul, coe_one, Matrix.one_apply,
      if_pos, if_neg, ite_false, Fin.zero_ne_one, one_ne_zero, Int.cast_one, Int.cast_zero] using hh
  have c11 : C 1 1 = 1 := by simpa [c00, c10] using det_entries C
  obtain ⟨t, ht⟩ := ZMod.intCast_surjective (C 0 1)
  let p : Marking := ⟨!![1, t; 0, 1], by simp⟩
  have hp : Parabolic p := by rfl
  have hρ : ρ p = C := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · change ((1 : ℤ) : ZMod L) = C 0 0
      simpa only [Int.cast_one] using c00.symm
    · exact ht
    · change ((0 : ℤ) : ZMod L) = C 1 0
      simpa only [Int.cast_zero] using c10.symm
    · change ((1 : ℤ) : ZMod L) = C 1 1
      simpa only [Int.cast_one] using c11.symm
  refine ⟨B * p⁻¹ * A⁻¹, ?_, p, hp, ?_⟩
  · rw [CongruenceSubgroup.Gamma_mem']
    change ρ (B * p⁻¹ * A⁻¹) = 1
    rw [map_mul, map_mul, map_inv, map_inv, hρ]
    dsimp [C]
    simp [map_mul, map_inv]
  · simp [mul_assoc]

private lemma label_gamma (L : ℕ) (γ A : Marking)
    (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    primitiveLabel L (γ * A) = primitiveLabel L A := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  apply Subtype.ext
  apply Prod.ext <;>
    simp [primitiveLabel, entry_mul, h00, h01, h10, h11]

private lemma label_parabolic (L : ℕ) (A p : Marking) (hp : Parabolic p) :
    signedLabel L (A * p) = signedLabel L A := by
  have hp0 : p 1 0 = 0 := hp
  have hd : p 0 0 * p 1 1 = 1 := by simpa [hp0] using det_entries p
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with hs | hs
  · have hh : primitiveLabel L (A * p) = primitiveLabel L A := by
      apply Subtype.ext
      apply Prod.ext <;> simp [primitiveLabel, entry_mul, hp0, hs]
    exact congrArg (Quot.mk _) hh
  · apply Eq.symm
    apply Quot.sound
    apply Prod.ext <;> simp [primitiveLabel, entry_mul, hp0, hs]

/-- Exact fibers of the canonical signed first-column residue label. -/
theorem congruence_label_fibers : ∀ L : ℕ, 3 ≤ L → ∀ A B : Marking,
    signedLabel L A = signedLabel L B ↔ MarkingRel L A B := by
  intro L _hL A B
  constructor
  · intro h
    rcases label_cases L A B h with h | h
    · exact unsigned_fiber L A B h
    · have hn : (primitiveLabel L (-B)).val = (primitiveLabel L A).val := by
        have hh : (primitiveLabel L (-B)).val = -(primitiveLabel L B).val := by
          apply Prod.ext <;> simp [primitiveLabel]
        rw [hh, h, neg_neg]
      obtain ⟨γ, hγ, p, hp, he⟩ := unsigned_fiber L A (-B) hn
      refine ⟨γ, hγ, -p, ?_, ?_⟩
      · change -p 1 0 = 0
        rw [show p 1 0 = 0 from hp, neg_zero]
      · have hh := congrArg Neg.neg he
        simpa only [neg_neg, mul_neg] using hh
  · rintro ⟨γ, hγ, p, hp, rfl⟩
    rw [label_parabolic L (γ * A) p hp]
    exact (congrArg (Quot.mk _) (label_gamma L γ A hγ)).symm

end ArithmeticThetaIntegralCuspsR0102
