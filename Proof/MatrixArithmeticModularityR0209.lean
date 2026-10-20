module

public import CompactActualMetaplecticLevelR0209
public import CompactThetaSectionImageR0209

@[expose] public section

/-! Arithmetic modularity and exact image data for the same sharp matrix family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaCompactModularityR0209
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195

/-- Construct all geometric data from the input matrices, then use the actual
finite-level and section-image bridges on precisely those witnesses. -/
theorem matrix_arithmetic_modularity :
    ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∃ G : MatrixData A, ArithmeticModularFamily G := by
  intro n h hn hh A hA
  obtain ⟨U, hU, hformal, D, X, H, V, hH, hgeom⟩ :=
    sharp_matrix_geometric_family n h hn hh A hA
  obtain ⟨J, C, hC, hone, hdegree, F, t, σ, ht, hσ, hexp⟩ := hgeom
  let G : MatrixData A :=
    { indexing := U
      indexed := hU
      formal := hformal
      data := D
      compact := X
      hodge := H
      canonical := hH
      test := V
      half := J
      cover := C
      etale := hC
      oneNorm := hone
      degree := hdegree
      frame := F
      unary := t
      sections := σ
      unary_expansion := ht
      coset_eq := hσ
      expansion := hexp }
  have hN : 0 < commonN A :=
    (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [level]
    omega
  refine ⟨G, ?_, ?_⟩
  · exact compact_actual_metaplectic_level ℂ (level (commonN A))
      (2^(normCount A-1)) G.root hL heven G.etale
  · intro B hB
    exact ⟨compact_theta_section_image n h hn hh A hA G B hB,
      sharp_exact_image_data n h hh A hA B hB⟩

end ArithmeticThetaCompactModularityR0209

#print axioms ArithmeticThetaCompactModularityR0209.matrix_arithmetic_modularity
