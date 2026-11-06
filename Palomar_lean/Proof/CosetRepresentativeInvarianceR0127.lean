module

public import OrthogonalConsumerDefinitionsR0127

@[expose] public section

/-! Representative independence by an exact integral translation of every shell. -/
set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaOrthogonalConsumerR0127

/-- Integral translation preserves the complete series, even for degenerate weights. -/
lemma cosetSeries_integral_translation (n : ℕ) (m : Fin n → ℕ)
    (t v : Fin n → ℚ) (z : Fin n → ℤ)
    (hz : ∀ j, t j - v j = (z j : ℚ)) :
    cosetSeries m t = cosetSeries m v := by
  apply PowerSeries.ext
  intro a
  simp only [cosetSeries, PowerSeries.coeff_mk]
  congr 1
  let e : (Fin n → ℤ) ≃ (Fin n → ℤ) :=
    { toFun := fun x => x + z
      invFun := fun y => y - z
      left_inv := fun x => add_sub_cancel_right x z
      right_inv := fun y => sub_add_cancel y z }
  have he (x : Fin n → ℤ) :
      (∑ j, (m j : ℚ) / 2 * (t j + (x j : ℚ)) ^ 2) =
      (∑ j, (m j : ℚ) / 2 * (v j + ((e x) j : ℚ)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : t j + (x j : ℚ) = v j + ((e x) j : ℚ) := by
      change t j + (x j : ℚ) = v j + ((x j + z j : ℤ) : ℚ)
      rw [Int.cast_add, ← hz j]
      ring
    rw [hj]
  exact Nat.card_congr (e.subtypeEquiv (fun x => by rw [he x]))

/-- The rational-coordinate coset series depends only on the actual quotient class. -/
theorem coset_representative_invariance : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ) (t v : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B), ArithmeticThetaOrthogonalConsumerR0127.cosetClass B t = ArithmeticThetaOrthogonalConsumerR0127.cosetClass B v → ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m t.val = ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m v.val := by
  intro n B m t v h
  have hp : t - v ∈ periods B := QuotientAddGroup.eq_iff_sub_mem.mp h
  change (t.val - v.val) ∈ (castVec n).range at hp
  obtain ⟨z, hz⟩ := hp
  apply cosetSeries_integral_translation n m t.val v.val z
  intro j
  exact (congrFun hz j).symm

end ArithmeticThetaOrthogonalConsumerR0127
