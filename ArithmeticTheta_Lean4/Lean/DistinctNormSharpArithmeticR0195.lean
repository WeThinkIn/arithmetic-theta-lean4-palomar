import SharpKernelDefinitionsR0195

/-! Exact norm-only indexing and the rational floor of the sharp cutoff. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaSharpKernelR0195
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaOrthogonalAlgorithm (naturalNorms computed_natural_data)

namespace DistinctNormSharpArithmetic

private lemma exact_norm_index {n h : ℕ} (A : Matrices n h) :
    ∃ I : NormIndex A, IndexesNorms A I := by
  classical
  let e : Fin (normCount A) ≃ ↥(norms A) :=
    (Fintype.equivFinOfCardEq (by simp [normCount])).symm
  let g : Fin h × Fin n → ↥(norms A) := fun ij =>
    ⟨naturalNorms (A ij.1) ij.2, Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩⟩
  let I : NormIndex A :=
    { norm := fun z => (e z).val
      index := fun ij => e.symm (g ij) }
  refine ⟨I, Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · intro z
    obtain ⟨ij, _, hij⟩ := Finset.mem_image.mp (e z).property
    refine ⟨ij, ?_⟩
    change e.symm (g ij) = z
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext hij
  · intro ij
    exact congrArg Subtype.val (e.apply_symm_apply (g ij))

private lemma eight_dvd_level (N m : ℕ) (hd : m ∣ N) : 8*m ∣ level N := by
  obtain ⟨v, hv⟩ := hd
  refine ⟨3*v*N, ?_⟩
  dsimp [level]
  rw [hv]
  ring

private lemma rational_floor (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℚ) ≤ (a : ℚ) / b ∧
      (a : ℚ) / b < ((a / b : ℕ) : ℚ) + 1 := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  constructor
  · apply (le_div_iff₀ hbq).mpr
    exact_mod_cast Nat.div_mul_le_self a b
  · apply (div_lt_iff₀ hbq).mpr
    exact_mod_cast (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self (a / b))

private lemma cutoff_floor {n h : ℕ} (A : Matrices n h) (hN : 0 < commonN A) :
    (cutoff A : ℚ) ≤ (n : ℚ) * 2^(normCount A-1) *
      ArithmeticThetaLevelCount.levelIndex (level (commonN A)) /
        (48*(level (commonN A) : ℚ)) ∧
    (n : ℚ) * 2^(normCount A-1) *
      ArithmeticThetaLevelCount.levelIndex (level (commonN A)) /
        (48*(level (commonN A) : ℚ)) < (cutoff A : ℚ)+1 := by
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have hcard := (ArithmeticThetaGlobalization.finite_full_level_count _ hL).1
  have hfloor := rational_floor
    (n * 2^(normCount A-1) *
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))))
    (48 * level (commonN A)) (by omega)
  simpa only [cutoff, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hcard] using hfloor

end DistinctNormSharpArithmetic

/-- Distinct diagonal norms have the same lcm and full level as the accepted
unary factorization; natural division gives exactly the sharp rational floor. -/
theorem distinct_norm_sharp_arithmetic :
    ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : Matrices n h),
    (∀ i, ArithmeticThetaComputed.validGram (A i)) →
    0 < normCount A ∧ ∃ I : NormIndex A, IndexesNorms A I ∧
      (∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ commonN A ∧
        8*I.norm i ∣ level (commonN A)) ∧
      ((cutoff A : ℕ) : ℚ) ≤ (n : ℚ) * 2^(normCount A-1) *
        ArithmeticThetaLevelCount.levelIndex (level (commonN A)) /
          (48*(level (commonN A) : ℚ)) ∧
      (n : ℚ) * 2^(normCount A-1) *
        ArithmeticThetaLevelCount.levelIndex (level (commonN A)) /
          (48*(level (commonN A) : ℚ)) < (cutoff A : ℚ)+1 := by
  intro n h hn hh A hA
  classical
  obtain ⟨hN, _, hd, _⟩ := indexed_full_unary_factorization n h hn hh A hA
  have hr : 0 < normCount A := by
    apply Finset.card_pos.mpr
    exact ⟨naturalNorms (A ⟨0, hh⟩) ⟨0, hn⟩,
      Finset.mem_image.mpr ⟨(⟨0, hh⟩, ⟨0, hn⟩), Finset.mem_univ _, rfl⟩⟩
  obtain ⟨I, hI⟩ := DistinctNormSharpArithmetic.exact_norm_index A
  refine ⟨hr, I, hI, ?_, DistinctNormSharpArithmetic.cutoff_floor A hN⟩
  intro z
  obtain ⟨ij, rfl⟩ := hI.2.1 z
  rw [hI.2.2]
  have hm := (computed_natural_data n (A ij.1)
    (hA ij.1).1 (hA ij.1).2.1 (hA ij.1).2.2).1 ij.2
  exact ⟨hm.1, hm.2.1, hd ij.1 ij.2,
    DistinctNormSharpArithmetic.eight_dvd_level _ _ (hd ij.1 ij.2)⟩

end ArithmeticThetaSharpKernelR0195

#print axioms ArithmeticThetaSharpKernelR0195.distinct_norm_sharp_arithmetic
