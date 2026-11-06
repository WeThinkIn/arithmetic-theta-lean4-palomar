module

public import ComputedThetaColumns
public import ComputedComplexKernelBasis
public import TruncationCertificates

@[expose] public section

namespace ArithmeticThetaDegreeAssembly

open ArithmeticThetaComputed

/-- The actual computed prefix certificate identifies the full theta kernel. -/
theorem actual_early_certificate :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ W : Submodule ℂ (Fin h → ℂ),
        W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) →
        Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank →
        W = LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ∧
          LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
            LinearMap.ker ((ArithmeticThetaComputed.coefficientMatrix A B).map
              (algebraMap ℚ ℂ)).mulVecLin := by
  intro n h B A hv W hW hdim
  let M := ArithmeticThetaComputed.coefficientMatrix A B
  let Kθ := LinearMap.ker (ArithmeticThetaComputed.thetaMap A)
  let KM := LinearMap.ker (M.map (algebraMap ℚ ℂ)).mulVecLin
  have hkm : Module.finrank ℂ KM = h - M.rank := by
    exact ArithmeticThetaLinearAlgebra.rational_matrix_nullity (B + 1) h M
  have hinc : Kθ ≤ KM := by
    intro c hc
    change ((M.map (algebraMap ℚ ℂ)).mulVecLin) c = 0
    have hmap := ArithmeticThetaComputed.computed_prefix_map n h B A hv
    rw [← hmap]
    change ArithmeticThetaComputed.prefixMap B (ArithmeticThetaComputed.thetaMap A c) = 0
    rw [hc, map_zero]
  have hWK : W ≤ KM := hW.trans hinc
  have hWK_eq : W = KM := by
    apply Submodule.eq_of_le_of_finrank_eq hWK
    simpa [M, KM] using hdim.trans hkm.symm
  have hKθ : Kθ = KM := by
    apply le_antisymm hinc
    rw [← hWK_eq]
    exact hW
  exact ⟨by exact hWK_eq.trans hKθ.symm, by simpa [Kθ, KM, M] using hKθ⟩


/-- Computed null and pivot data describe the entire formal theta map. -/
theorem certified_theta_image_data :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ W : Submodule ℂ (Fin h → ℂ),
        W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) →
        Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank →
        (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run
          (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j =>
          ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧
          Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns
          (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j =>
          ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) =
          LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin
          (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length =>
          ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ
          (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A
          B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) =
          LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j)
          = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A
          B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates
          (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A
          (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run
          (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) =
          ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) →
          c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j := by
  intro n h B A hv W hW hdim
  have heq := actual_early_certificate n h B A hv W hW hdim
  have hnull := ArithmeticThetaComputed.computed_complex_kernel_basis (B + 1) h (ArithmeticThetaComputed.coefficientMatrix A B)
  have hpiv := ArithmeticThetaComputed.computed_independent_theta_columns n h B A hv
  have hcoord := ArithmeticThetaComputed.computed_prefix_coordinates n h B A hv
  let pidx : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length →
    Fin h := ArithmeticThetaComputed.selectedIndex A B
  let q : Fin h → Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℂ := fun j t =>
    ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ)
  have htheta (j : Fin h) : ArithmeticThetaComputed.theta (A j) =
      ∑ t, q j t • ArithmeticThetaComputed.theta (A (pidx t)) := by
    let v : Fin h → ℂ := Pi.single j 1 - ∑ t, q j t • Pi.single (pidx t) 1
    have hvM : v ∈ LinearMap.ker ((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
      change (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin) v = 0
      have hmap := ArithmeticThetaComputed.computed_prefix_map n h B A hv
      rw [← hmap]
      change ArithmeticThetaComputed.prefixMap B (ArithmeticThetaComputed.thetaMap A v) = 0
      ext a
      simp only [ArithmeticThetaComputed.prefixMap, LinearMap.pi_apply]
      change PowerSeries.coeff a.val (ArithmeticThetaComputed.thetaMap A v) = 0
      simp only [v, map_sub, map_sum, map_smul]
      simp [ArithmeticThetaComputed.thetaMap, smul_eq_mul]
      rw [hcoord j a]
      simp [q, pidx]
    have hvK : v ∈ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) := by
      rw [heq.2]
      exact hvM
    have hz := hvK
    change ArithmeticThetaComputed.thetaMap A v = 0 at hz
    have hcollapse :
        (∑ x : Fin h, (∑ t, q j t *
          ((Pi.single (pidx t) (1 : ℂ) : Fin h → ℂ) x)) •
            ArithmeticThetaComputed.theta (A x)) =
          ∑ t, q j t • ArithmeticThetaComputed.theta (A (pidx t)) := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_eq_single (pidx t)]
      · simp
      · intro b hb hne
        simp [hne]
      · simp
    have hz' : ArithmeticThetaComputed.theta (A j) -
        ∑ t, q j t • ArithmeticThetaComputed.theta (A (pidx t)) = 0 := by
      have hz2 : ArithmeticThetaComputed.theta (A j) -
          (∑ x : Fin h, (∑ t, q j t *
            ((Pi.single (pidx t) (1 : ℂ) : Fin h → ℂ) x)) •
              ArithmeticThetaComputed.theta (A x)) = 0 := by
        simpa [v, q, pidx, ArithmeticThetaComputed.thetaMap, Finset.sum_sub_distrib,
          sub_smul, Pi.single_apply] using hz
      rw [hcollapse] at hz2
      exact hz2
    exact sub_eq_zero.mp hz'
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hnull.1, ?_⟩
    exact hnull.2.1.trans heq.2.symm
  · refine ⟨hpiv, le_antisymm ?_ ?_⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      apply LinearMap.mem_range.mpr
      refine ⟨Pi.single (pidx t) 1, ?_⟩
      simp [pidx, ArithmeticThetaComputed.thetaMap]
    · intro x hx
      rcases hx with ⟨c, rfl⟩
      rw [show c = ∑ j, c j • Pi.single j 1 by ext j; simp [Finset.sum_apply, Pi.single_apply]]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro j hj
      have hs := htheta j
      simp [ArithmeticThetaComputed.thetaMap]
      rw [hs]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro t ht
      show q j t • ArithmeticThetaComputed.theta (A (pidx t)) ∈ _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨t, rfl⟩
  · intro j
    constructor
    · simpa [q, pidx] using htheta j
    · intro c hc
      have hdiff : ∑ t, (((c t : ℚ) : ℂ) - q j t) • ArithmeticThetaComputed.theta (A (pidx t)) = 0 := by
        have he : (∑ t, (((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (pidx t)))) =
            ∑ t, q j t • ArithmeticThetaComputed.theta (A (pidx t)) :=
          hc.symm.trans (by simpa [q, pidx] using htheta j)
        exact (sub_eq_zero.mpr he) ▸ by simp [Finset.sum_sub_distrib, sub_smul]
      have hli := hpiv
      rw [Fintype.linearIndependent_iff] at hli
      exact funext (fun t => by
        apply sub_eq_zero.mp
        have ht := hli (fun t => (((c t : ℚ) : ℂ) - q j t)) hdiff t
        change ((c t : ℚ) : ℂ) -
          ((ArithmeticThetaElimination.columnCoordinates
            (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) = 0 at ht
        exact_mod_cast ht)

end ArithmeticThetaDegreeAssembly
