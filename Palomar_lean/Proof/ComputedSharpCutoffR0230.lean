module

public import AdaptiveSolverDefinitionsR0230
public import ComputedBoundParameters
public import SharpKernelDefinitionsR0195
public import FiniteFullLevelCount

@[expose] public section

/-! Identification of the executable sharp cutoff with the accepted exact cutoff. -/
set_option autoImplicit false
namespace ArithmeticThetaAdaptiveSolverR0230

private theorem commonModulus_eq_commonN {n h : ℕ} (A : Matrices n h) :
    ArithmeticThetaOrthogonalAlgorithm.commonModulus A =
      ArithmeticThetaLatticeSectionsR0188.commonN A := by
  classical
  simp only [ArithmeticThetaOrthogonalAlgorithm.commonModulus,
    ArithmeticThetaOrthogonalAlgorithm.normSet,
    ArithmeticThetaLatticeSectionsR0188.commonN, Finset.lcm_image, Function.comp_def, id_eq]

/-- Both the executable floor and the executable index use the actual computed
norms. The argument also covers empty families and zero-dimensional lattices. -/
theorem computed_sharp_cutoff :
    ∀ (n h : ℕ) (A : Matrices n h),
    (∀ i, ArithmeticThetaComputed.validGram (A i)) →
    bound A = ArithmeticThetaSharpKernelR0195.cutoff A ∧
      (indexValue (ArithmeticThetaOrthogonalAlgorithm.level A) =
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod (ArithmeticThetaOrthogonalAlgorithm.level A))) : ℚ)) := by
  intro n h A hA
  have hN := (ArithmeticThetaOrthogonalAlgorithm.computed_bound_parameters n h A
    (fun i => (hA i).1) (fun i => (hA i).2.1) (fun i => (hA i).2.2)).2.2.1
  have hL : 3 ≤ ArithmeticThetaOrthogonalAlgorithm.level A := by
    have hp := pow_pos hN 2
    unfold ArithmeticThetaOrthogonalAlgorithm.level
    omega
  have hi : indexValue (ArithmeticThetaOrthogonalAlgorithm.level A) =
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (ArithmeticThetaOrthogonalAlgorithm.level A))) : ℚ) :=
    (ArithmeticThetaGlobalization.finite_full_level_count _ hL).1.symm
  refine ⟨?_, hi⟩
  have hl : ArithmeticThetaOrthogonalAlgorithm.level A =
      ArithmeticThetaCompactUnaryR0183.level
        (ArithmeticThetaLatticeSectionsR0188.commonN A) := by
    simp only [ArithmeticThetaOrthogonalAlgorithm.level, commonModulus_eq_commonN]
  have hc : ArithmeticThetaOrthogonalAlgorithm.distinctNormCount A =
      ArithmeticThetaSharpKernelR0195.normCount A := rfl
  unfold bound ArithmeticThetaSharpKernelR0195.cutoff
  rw [hi, hl, hc]
  rw [← Nat.cast_ofNat (R := ℚ) (n := 48), ← Nat.cast_mul,
    ← Nat.cast_ofNat (R := ℚ) (n := 2), ← Nat.cast_pow,
    ← Nat.cast_mul, ← Nat.cast_mul, Rat.floor_natCast_div_natCast]
  rw [Int.ofNat_ediv_ofNat]
  exact Int.toNat_natCast _

end ArithmeticThetaAdaptiveSolverR0230

#print axioms ArithmeticThetaAdaptiveSolverR0230.computed_sharp_cutoff
