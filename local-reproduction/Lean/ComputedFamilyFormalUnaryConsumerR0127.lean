import SourceOrthogonalFactorizationR0127
import UnaryParameterIdentificationR0127

/-! The computed arithmetic family consumes the literal formal unary series. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaOrthogonalAlgorithm

private lemma normalized_residue (m : ℕ) (hm : 0 < m) (r : ℤ) :
    ∃ a : Fin m, Int.ModEq (m : ℤ) r (a.val : ℤ) ∧
      ∃ z : ℤ, (r : ℚ) = (a.val : ℚ) + (m : ℚ) * (z : ℚ) := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hnon := Int.emod_nonneg r (ne_of_gt hmZ)
  have hlt := Int.emod_lt_of_pos r hmZ
  let a : Fin m := ⟨(r % (m : ℤ)).toNat, by omega⟩
  have ha : (a.val : ℤ) = r % (m : ℤ) := Int.toNat_of_nonneg hnon
  refine ⟨a, ?_, r / (m : ℤ), ?_⟩
  · simp only [Int.ModEq, ha, Int.emod_emod]
  · have he : r = (a.val : ℤ) + (m : ℤ) * (r / (m : ℤ)) := by
      rw [ha]
      exact (Int.emod_add_mul_ediv r (m : ℤ)).symm
    exact_mod_cast he

private lemma thetaZ_complex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (thetaZ A) = ArithmeticThetaComputed.theta A := by
  ext a
  simp [thetaZ, ArithmeticThetaComputed.theta, castVec]

/-- Complete common-parameter identity for every complex coefficient family. -/
theorem computed_family_formal_unary_consumer : ∀ (n h : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (D : ℕ) (hD : D ≠ 0), (∀ (i : Fin h) (j : Fin n), 2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) ∣ D) → ∃ (t : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i))) (ν : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → (j : Fin n) → Fin (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) (hw : ∀ (i : Fin h) (j : Fin n), D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) ≠ 0), (∀ i, ArithmeticThetaOrthogonalConsumerR0127.Representatives (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)) (t i)) ∧ (∀ (i : Fin h) (a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs) (j : Fin n), ∃ z : ℤ, ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (t i a).val j = ((ν i a j).val : ℚ) + ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (z : ℚ)) ∧ (∀ c : Fin h → ℂ, PowerSeries.expand D hD (ArithmeticThetaComputed.thetaMap A c) = ∑ i : Fin h, c i • (∑ a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs, ∏ j : Fin n, PowerSeries.expand (D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j))) (hw i j) (ArithmeticThetaSchrodingerR0119.unary ℂ (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) (ν i a j)))) := by
  intro n h A hA D hD hd
  classical
  have hc i := computed_orthogonalization n (A i) (hA i).1 (hA i).2.1 (hA i).2.2
  have hn i := computed_natural_data n (A i) (hA i).1 (hA i).2.1 (hA i).2.2
  have hB (i : Fin h) : OrthogonalData (A i) (basisMatrix (A i)) (naturalNorms (A i)) := by
    refine ⟨ne_of_gt (hc i).1, fun j => ⟨(hn i).1 j |>.1, (hn i).1 j |>.2.1⟩, ?_⟩
    simpa only [(hn i).1 _ |>.2.2] using (hc i).2.2
  have ht_exists (i : Fin h) :=
    (rational_preimage_cosets n (basisMatrix (A i)) (hB i).1).choose_spec.2.2.2
  choose t ht using ht_exists
  choose r hr htheta hprod using fun i =>
    source_orthogonal_factorization n (A i) (basisMatrix (A i))
      (naturalNorms (A i)) (hA i) (hB i) (t i) (ht i)
  have hres (i : Fin h) (a : Fin (basisMatrix (A i)).det.natAbs) (j : Fin n) :=
    normalized_residue (naturalNorms (A i) j) ((hB i).2.1 j).1 (r i a j)
  choose ν hν hz using hres
  have hw (i : Fin h) (j : Fin n) : D / (2 * naturalNorms (A i) j) ≠ 0 := by
    exact ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (hd i j))
      (by have := ((hB i).2.1 j).1; omega))
  refine ⟨t, ν, hw, ht, ?_, ?_⟩
  · intro i a j
    rw [← hr i a j]
    exact hz i a j
  · intro c
    have hi (i : Fin h) :
        PowerSeries.expand D hD (ArithmeticThetaComputed.theta (A i)) =
          ∑ a, ∏ j, PowerSeries.expand (D / (2 * naturalNorms (A i) j)) (hw i j)
            (ArithmeticThetaSchrodingerR0119.unary ℂ (naturalNorms (A i) j) (ν i a j)) := by
      rw [← thetaZ_complex, ← PowerSeries.map_expand, hprod i D hD (hd i), map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro j _
      let : NeZero (naturalNorms (A i) j) := ⟨ne_of_gt ((hB i).2.1 j).1⟩
      exact unary_parameter_identification ℂ _ _ (hw i j) _ _ (hν i a j)
    simp only [ArithmeticThetaComputed.thetaMap, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, PowerSeries.expand_smul, hi]

end ArithmeticThetaOrthogonalConsumerR0127
