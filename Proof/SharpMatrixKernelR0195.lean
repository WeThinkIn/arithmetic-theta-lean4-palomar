module

public import SharpMatrixGeometricFamilyR0195
public import SharpGeometricCutoffR0195

@[expose] public section

/-! The unconditional sharp computed matrix kernel, including rank zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSharpKernelR0195
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaComputed

/-- Complete complex theta relations are determined at the exact sharp cutoff
and at every larger prefix. Rank zero has cutoff zero and constant theta sum. -/
theorem sharp_matrix_kernel :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧ ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro n h hh A hA
  classical
  by_cases hn : n = 0
  · subst n
    have hcut : cutoff A = 0 := by simp [cutoff]
    obtain ⟨B, hB, hker, hzero⟩ :=
      ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel 0 h hh A hA
    have hB0 : B = 0 := by simpa using hB
    subst B
    exact ⟨fun B hB => hker B (by omega), fun _ => ⟨hcut, hzero rfl⟩⟩
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨U, hU, _hformal, D, X, H, V, _hH, hfamily⟩ :=
      sharp_matrix_geometric_family n h hn' hh A hA
    refine ⟨?_, fun hzero => (hn hzero).elim⟩
    intro B hB
    rw [← computed_prefix_map n h B A hA]
    ext c
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hc
      rw [hc, map_zero]
    · intro hc
      apply sharp_geometric_cutoff n h hn' hh A hA U hU D X H V hfamily c
      intro m hm
      exact congrFun hc (⟨m, by omega⟩ : Fin (B + 1))

#print axioms sharp_matrix_kernel
end ArithmeticThetaSharpKernelR0195
