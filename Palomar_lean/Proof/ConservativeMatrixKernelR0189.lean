module

public import ArithmeticGeometricFamilyExistenceR0189
public import GeometricFamilyConservativeCutoffR0189
public import FiniteFullLevelCount
public import RankZero
public import ComputedCoefficientMatrix

@[expose] public section

/-! The exact conservative computed matrix kernel, including rank zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConservativeKernelR0189
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComputed ArithmeticThetaSectionOrder

namespace ConservativeMatrixKernel

private lemma cutoff_rational {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    (hN : 0 < commonN A) :
    (cutoff A U : ℚ) = (n : ℚ) * (exponent (commonN A) : ℚ)^U.count *
      ArithmeticThetaLevelCount.levelIndex (level (commonN A)) / 48 := by
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

private lemma rank_zero_theta (A : Matrix (Fin 0) (Fin 0) ℤ) : theta A = 1 := by
  ext m
  rw [theta, PowerSeries.coeff_mk]
  let e : {x : Fin 0 → ℤ //
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ)} ≃
      {x : Fin 0 → ℤ // (0 : ℕ) = m} :=
    Equiv.subtypeEquivRight fun x => by
      have hz : (fun i => (x i : ℚ)) = (0 : Fin 0 → ℚ) := Subsingleton.elim _ _
      rw [hz, QuadraticMap.map_zero]
      exact_mod_cast (Iff.rfl : (0 : ℕ) = m ↔ 0 = m)
  rw [Nat.card_congr e, ArithmeticThetaElementary.rank_zero_coefficients (fun _ => 0) rfl m]
  by_cases hm : m = 0 <;> simp [hm]

private lemma rank_zero_formula {h : ℕ} (A : Matrices 0 h) (c : Fin h → ℂ) :
    thetaMap A c = PowerSeries.C (∑ i : Fin h, c i) := by
  simp only [thetaMap, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, rank_zero_theta]
  exact ArithmeticThetaElementary.sum_smul_one h c

private lemma kernel_of_vanishing {n h : ℕ} (A : Matrices n h)
    (hA : ∀ i, validGram (A i)) (B : ℕ)
    (hvan : ∀ c : Fin h → ℂ, VanishesThrough (thetaMap A c) B → thetaMap A c = 0) :
    ∀ B' : ℕ, B ≤ B' → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin) := by
  intro B' hBB
  rw [← computed_prefix_map n h B' A hA]
  ext c
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hc
    rw [hc, map_zero]
  · intro hc
    apply hvan c
    intro m hm
    have hx := congrFun hc (⟨m, by omega⟩ : Fin (B' + 1))
    exact hx

end ConservativeMatrixKernel

/-- The full complex kernel equals every computed prefix kernel at and above
its exact integral conservative bound. -/
theorem conservative_matrix_kernel :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ B : ℕ, (if n = 0 then B = 0 else ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ B = ArithmeticThetaConservativeKernelR0189.cutoff A U ∧ (B : ℚ) = (n : ℚ) * ((ArithmeticThetaCompactUnaryR0183.exponent (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℕ) : ℚ)^U.count * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / 48) ∧ (∀ B' : ℕ, B ≤ B' → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro n h hh A hA
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0, by simp, ?_, ?_⟩
    · apply ConservativeMatrixKernel.kernel_of_vanishing A hA 0
      intro c hc
      rw [ConservativeMatrixKernel.rank_zero_formula] at hc ⊢
      have hz := hc 0 (by omega)
      simpa using congrArg PowerSeries.C (by simpa using hz : (∑ i : Fin h, c i) = 0)
    · intro _ c
      exact ConservativeMatrixKernel.rank_zero_formula A c
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨U, hU, hformal, D, X, H, hH, V, hfamily⟩ :=
      arithmetic_geometric_family_existence n h hn' hh A hA
    refine ⟨cutoff A U, ?_, ?_, ?_⟩
    · rw [if_neg hn]
      exact ⟨U, hU, hformal, rfl, ConservativeMatrixKernel.cutoff_rational A U
        (indexed_full_unary_factorization n h hn' hh A hA).1⟩
    · exact ConservativeMatrixKernel.kernel_of_vanishing A hA (cutoff A U)
        (geometric_family_conservative_cutoff n h hn' hh A hA U hU D X H V hfamily)
    · exact fun hzero => (hn hzero).elim

#print axioms conservative_matrix_kernel
end ArithmeticThetaConservativeKernelR0189
