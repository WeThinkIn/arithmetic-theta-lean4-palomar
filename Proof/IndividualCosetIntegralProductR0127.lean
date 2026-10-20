module

public import OrthogonalConsumerDefinitionsR0127

@[expose] public section

/-! Complete integral-exponent factorization for one actual rational coset. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaCosets

theorem individual_coset_integral_product : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ (t : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B) (ν : Fin n → ℤ), (∀ j, (ν j : ℚ) = (m j : ℚ) * t.val j) → (∀ r : Fin n → ℤ, (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) → ∃ a : ℕ, (∑ j : Fin n, (r j : ℚ)^2 / (2 * (m j : ℚ))) = (a : ℚ)) ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m t.val) = ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν j)) := by
  intro n A B m hA hB t ν hν
  classical
  obtain ⟨hsym, heven, hpos⟩ := hA
  obtain ⟨hdet, hm, hgram⟩ := hB
  have ht : ∃ x : Fin n → ℤ,
      (fun j => (x j : ℚ)) = (B.map (Int.castRingHom ℚ)).mulVec t.val := t.property
  obtain ⟨x, hx⟩ := ht
  have hunit : IsUnit (B.map (Int.castRingHom ℚ)).det := by
    apply isUnit_iff_ne_zero.mpr
    change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    change (B.det : ℚ) ≠ 0
    exact_mod_cast hdet
  have hinv : ((B.map (Int.castRingHom ℚ))⁻¹).mulVec (fun j => (x j : ℚ)) = t.val := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have hνx : ν = (B.transpose * A).mulVec x := by
    funext j
    apply Int.cast_injective (α := ℚ)
    rw [hν j, (orthogonal_residue_formula n A B m hsym hdet
      (fun j => (hm j).1) hgram x 0).1 j, hinv]
  have hint : ∀ r : Fin n → ℤ, (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) →
      ∃ a : ℕ, (∑ j, (r j : ℚ)^2 / (2 * (m j : ℚ))) = (a : ℚ) := by
    intro r hr
    apply total_exponent_integrality n A B m hsym heven hpos hdet hm hgram x r
    simpa only [← hνx] using hr
  refine ⟨hint, ?_⟩
  intro D hD hd
  let w : Fin n → ℕ := fun j => D / (2 * m j)
  have hw : ∀ j, 0 < w j := fun j => denominator_weight_pos D (m j) hD (hm j).1 (hd j)
  let q : (Fin n → ℤ) → ℚ := fun k => ∑ j, (m j : ℚ) / 2 * (t.val j + (k j : ℚ))^2
  have hq : ∀ k, q k = ∑ j, ((ν j + (m j : ℤ) * k j : ℤ) : ℚ)^2 /
      (2 * (m j : ℚ)) := by
    intro k
    apply Finset.sum_congr rfl
    intro j _
    have hmj : (m j : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hm j).1)
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hν j]
    field_simp [hmj]
  change PowerSeries.expand D hD (PowerSeries.mk (fun a =>
    (Nat.card {k : Fin n → ℤ // q k = (a : ℚ)} : ℤ))) =
    ∏ j, (PowerSeries.mk (fun a => (Nat.card (UnaryShell (m j) (w j) (ν j) a) : ℤ)))
  rw [← unary_product_coefficients n m w ν hw]
  apply PowerSeries.ext
  intro a
  rw [PowerSeries.coeff_mk]
  by_cases ha : D ∣ a
  · obtain ⟨b, rfl⟩ := ha
    rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
    exact_mod_cast Nat.card_congr (cosetShellEquiv n m ν (fun j => (hm j).1)
      D hD hd q hq b)
  · rw [PowerSeries.coeff_expand_of_not_dvd D hD _ ha]
    have hempty : IsEmpty (TupleShell n m w ν a) := by
      constructor
      intro r
      obtain ⟨b, hb⟩ := hint r.val r.property.1
      have he := scaled_energy n m D (fun j => (hm j).1) hd r.val
      rw [hb] at he
      have hr : (∑ j, (w j : ℤ) * r.val j ^ 2) = (a : ℤ) := r.property.2
      change ((∑ j, (w j : ℤ) * r.val j ^ 2 : ℤ) : ℚ) = (D : ℚ) * b at he
      rw [hr] at he
      have hab : a = D * b := by exact_mod_cast he
      exact ha ⟨b, hab⟩
    let := hempty
    simp only [Nat.card_of_isEmpty, Nat.cast_zero]

end ArithmeticThetaOrthogonalConsumerR0127
