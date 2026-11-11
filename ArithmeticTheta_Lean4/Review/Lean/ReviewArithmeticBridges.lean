import ReviewArithmeticDefinitions
import ComputedSharpCutoffR0230

/-!
# Equality bridges for the arithmetic review interface

These lemmas identify the public parameters with their original counterparts.
No original definition is replaced. In particular, the two cutoffs of the paper
remain distinct: only the *sharp* cutoff is compared with the executable bound.
-/
set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaReview.Arithmetic

/-- Both historical norm-set APIs enumerate exactly the same values. -/
theorem norms_agree :
    ∀ (n h : ℕ) (A : Matrices n h),
      norms A = ArithmeticThetaOrthogonalAlgorithm.normSet A ∧
      norms A = ArithmeticThetaSharpKernelR0195.norms A := by
  intro n h A
  exact ⟨rfl, rfl⟩

/-- Consequently, both historical counts are the same cardinality. -/
theorem normCount_agree :
    ∀ (n h : ℕ) (A : Matrices n h),
      normCount A = ArithmeticThetaOrthogonalAlgorithm.distinctNormCount A ∧
      normCount A = ArithmeticThetaSharpKernelR0195.normCount A := by
  intro n h A
  exact ⟨rfl, rfl⟩

/-- Taking the LCM after removing duplicates gives the indexed LCM as well. -/
theorem commonNorm_agree :
    ∀ (n h : ℕ) (A : Matrices n h),
      commonNorm A = ArithmeticThetaOrthogonalAlgorithm.commonModulus A ∧
      commonNorm A = ArithmeticThetaLatticeSectionsR0188.commonN A := by
  intro n h A
  refine ⟨rfl, ?_⟩
  simp only [commonNorm, norms, ArithmeticThetaLatticeSectionsR0188.commonN,
    Finset.lcm_image, Function.comp_def, id_eq]

/-- The algorithm and the geometry therefore use the same level. -/
theorem level_agree :
    ∀ (n h : ℕ) (A : Matrices n h),
      level A = ArithmeticThetaOrthogonalAlgorithm.level A ∧
      level A = ArithmeticThetaCompactUnaryR0183.level
        (ArithmeticThetaLatticeSectionsR0188.commonN A) := by
  intro n h A
  refine ⟨rfl, ?_⟩
  unfold level ArithmeticThetaCompactUnaryR0183.level
  rw [(commonNorm_agree n h A).2]

/-- Agreement of the exponent does not identify the two different cutoffs. -/
theorem exponent_agree :
    ∀ (n h : ℕ) (A : Matrices n h),
      exponent A = ArithmeticThetaOrthogonalAlgorithm.normExponent A ∧
      exponent A = ArithmeticThetaCompactUnaryR0183.exponent
        (ArithmeticThetaLatticeSectionsR0188.commonN A) := by
  intro n h A
  refine ⟨rfl, ?_⟩
  unfold exponent ArithmeticThetaCompactUnaryR0183.exponent
  rw [(commonNorm_agree n h A).2]

/-- The geometric index formula and its executable version coincide. -/
theorem index_agree :
    ∀ (L : ℕ),
      index L = ArithmeticThetaLevelCount.levelIndex L ∧
      index L = ArithmeticThetaAdaptiveSolverR0230.indexValue L := by
  intro L
  exact ⟨rfl, rfl⟩

/-- The same formula counts determinant-one full level markings. -/
theorem index_eq_card :
    ∀ (L : ℕ), 3 ≤ L →
      index L = (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℚ) := by
  intro L hL
  exact (ArithmeticThetaGlobalization.finite_full_level_count L hL).1.symm

/-- Exact agreement with the original sharp cutoff, for all matrix families. -/
theorem sharpCutoff_eq :
    ∀ (n h : ℕ) (A : Matrices n h),
      sharpCutoff A = ArithmeticThetaSharpKernelR0195.cutoff A := by
  intro n h A
  unfold sharpCutoff ArithmeticThetaSharpKernelR0195.cutoff
  rw [(level_agree n h A).2, (normCount_agree n h A).2]

/-- For valid Gram families the natural quotient is also the executable
rational floor. Empty families and rank zero are included. -/
theorem sharpCutoff_computed :
    ∀ (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      sharpCutoff A = ArithmeticThetaAdaptiveSolverR0230.bound A ∧
      sharpCutoff A = Int.toNat
        ⌊(n : ℚ) * 2 ^ (normCount A - 1) * index (level A) /
          (48 * (level A : ℚ))⌋ := by
  intro n h A hA
  have hcomputed : sharpCutoff A = ArithmeticThetaAdaptiveSolverR0230.bound A :=
    (sharpCutoff_eq n h A).trans
      (ArithmeticThetaAdaptiveSolverR0230.computed_sharp_cutoff n h A hA).1.symm
  refine ⟨hcomputed, ?_⟩
  rw [hcomputed]
  rfl

end ArithmeticThetaReview.Arithmetic
