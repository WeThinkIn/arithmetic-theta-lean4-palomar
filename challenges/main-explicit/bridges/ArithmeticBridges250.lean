module
public import ReadyBridges198
public import ComputedBoundParameters
public import FiniteFullLevelCount
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarMain172.Bridges250
open ArithmeticThetaPalomarMain172
variable {n h : ℕ} (A : Matrices n h)

lemma commonN_computed : commonN A = ArithmeticThetaOrthogonalAlgorithm.commonModulus A := by
  exact Finset.lcm_eq_lcm_image

lemma level_computed : level (commonN A) = ArithmeticThetaOrthogonalAlgorithm.level A := by
  unfold level ArithmeticThetaOrthogonalAlgorithm.level
  rw [commonN_computed]

lemma exponent_computed : exponent (commonN A) = ArithmeticThetaOrthogonalAlgorithm.normExponent A := by
  unfold exponent ArithmeticThetaOrthogonalAlgorithm.normExponent
  rw [commonN_computed]

lemma commonN_pos (hA : ∀ i, validGram (A i)) : 0 < commonN A := by
  rw [commonN_computed]
  exact (ArithmeticThetaOrthogonalAlgorithm.computed_bound_parameters n h A
    (fun i => (hA i).1) (fun i => (hA i).2.1) (fun i => (hA i).2.2)).2.2.1

/-- The integer division in the Challenge equals its rational product formula,
with no geometric existence premise and no assumption on padded pair counts. -/
lemma cutoff_rational (U : Indexing A) (hN : 0 < commonN A) :
    (cutoff A U : ℚ) = (n : ℚ) * (exponent (commonN A) : ℚ)^U.count *
      levelIndex (level (commonN A)) / 48 := by
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  obtain ⟨hcard, hsigned⟩ := ArithmeticThetaGlobalization.finite_full_level_count _ hL
  have hnat : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) =
      2 * level (commonN A) *
        Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair (level (commonN A))) := by
    exact_mod_cast hcard.trans hsigned.symm
  have hd : 48 ∣ n * exponent (commonN A) ^ U.count *
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) := by
    rw [hnat]
    refine ⟨n * exponent (commonN A) ^ U.count * (commonN A)^2 *
      Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair (level (commonN A))), ?_⟩
    dsimp [level]
    ring
  unfold cutoff
  rw [Nat.cast_div hd (by decide : (48 : ℚ) ≠ 0)]
  push_cast
  rw [hcard]
  rfl

lemma prefix_map_eq (hA : ∀ i, validGram (A i)) (B : ℕ) :
    (ArithmeticThetaComputed.prefixMap B).comp (thetaMap A) =
      ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  rw [Bridges198.coefficientMatrix_complex_eq A hA B]
  exact ArithmeticThetaComputed.computed_prefix_map n h B A hA

lemma matrix_zero_iff_coefficients (hA : ∀ i, validGram (A i)) (B : ℕ) (c : Fin h → ℂ) :
    ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin c = 0 ↔
      ∀ a : ℕ, a ≤ B → PowerSeries.coeff a (thetaMap A c) = 0 := by
  rw [← prefix_map_eq A hA B]
  constructor
  · intro hc a ha
    exact congrFun hc (⟨a, by omega⟩ : Fin (B+1))
  · intro hc
    funext a
    exact hc a.val (by omega)

/-- This transports a previously proved kernel equality; it does not assume
or assert that such an equality exists at the explicit conservative bound. -/
lemma coefficients_iff_of_kernel (hA : ∀ i, validGram (A i)) (B : ℕ)
    (hk : LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin))
    (c : Fin h → ℂ) :
    thetaMap A c = 0 ↔ ∀ a : ℕ, a ≤ B → PowerSeries.coeff a (thetaMap A c) = 0 := by
  rw [← LinearMap.mem_ker, hk, LinearMap.mem_ker]
  exact matrix_zero_iff_coefficients A hA B c

end ArithmeticThetaPalomarMain172.Bridges250
#print axioms ArithmeticThetaPalomarMain172.Bridges250.commonN_computed
#print axioms ArithmeticThetaPalomarMain172.Bridges250.level_computed
#print axioms ArithmeticThetaPalomarMain172.Bridges250.exponent_computed
#print axioms ArithmeticThetaPalomarMain172.Bridges250.commonN_pos
#print axioms ArithmeticThetaPalomarMain172.Bridges250.cutoff_rational
#print axioms ArithmeticThetaPalomarMain172.Bridges250.prefix_map_eq
#print axioms ArithmeticThetaPalomarMain172.Bridges250.matrix_zero_iff_coefficients
#print axioms ArithmeticThetaPalomarMain172.Bridges250.coefficients_iff_of_kernel
