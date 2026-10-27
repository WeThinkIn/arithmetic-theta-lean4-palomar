import FullSourceDefinitionsR0268
import SourceOrthogonalFactorizationR0127

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaFullSourceR0268
open ArithmeticThetaOrthogonalConsumerR0127
namespace BinaryOrthogonalExample

lemma determinant : binaryBasis.det = 2 := by
  rw [Matrix.det_fin_two]
  norm_num [binaryBasis]

lemma gram_valid : ArithmeticThetaComputed.validGram binaryGram := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro i; fin_cases i <;> norm_num [binaryGram]
  · intro x hx
    have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i; fin_cases i <;> simp [h]
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.map, binaryGram]
    rcases hn with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

lemma orthogonal : OrthogonalData binaryGram binaryBasis binaryNorms := by
  refine ⟨by rw [determinant]; norm_num, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num [binaryNorms]
  · decide

def representatives (i : Fin 2) : preimageLattice binaryBasis :=
  ⟨binaryRepresentatives i, by
    change ∃ x : Fin 2 → ℤ, castVec 2 x = _
    refine ⟨![0, (i.val : ℤ)], ?_⟩
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [binaryRepresentatives, binaryBasis, castVec, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.map_apply] <;> norm_num [Matrix.map]⟩

lemma residues (i j : Fin 2) :
    ((binaryResidues i j : ℤ) : ℚ) = (binaryNorms j : ℚ) * (representatives i).val j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryResidues, binaryNorms, representatives, binaryRepresentatives]

lemma distinct : cosetClass binaryBasis (representatives 0) ≠
    cosetClass binaryBasis (representatives 1) := by
  intro h
  have hp := QuotientAddGroup.eq_iff_sub_mem.mp h
  change ∃ z : Fin 2 → ℤ, castVec 2 z =
    (representatives 0).val - (representatives 1).val at hp
  obtain ⟨z, hz⟩ := hp
  have hh := congrFun hz 0
  norm_num [castVec, representatives, binaryRepresentatives] at hh
  have hh' : (2 : ℚ) * (z 0 : ℚ) = -1 := by linarith
  have hh'' : (2 : ℤ) * z 0 = -1 := by exact_mod_cast hh'
  omega

lemma bijective : Function.Bijective (fun i => cosetClass binaryBasis (representatives i)) := by
  obtain ⟨E, hE, hf, hc, ht⟩ := rational_preimage_cosets 2 binaryBasis
    (by rw [determinant]; norm_num)
  let := hf
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (distinct h)
    · exact False.elim (distinct h.symm)
    · rfl
  · rw [hc, determinant]; simp

end BinaryOrthogonalExample

/-- The specified binary lattice, its two actual cosets, and its complete theta factorization. -/
theorem binary_orthogonal_example : ArithmeticThetaComputed.validGram ArithmeticThetaFullSourceR0268.binaryGram ∧ ArithmeticThetaFullSourceR0268.binaryBasis.det = 2 ∧ ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData ArithmeticThetaFullSourceR0268.binaryGram ArithmeticThetaFullSourceR0268.binaryBasis ArithmeticThetaFullSourceR0268.binaryNorms ∧ ∃ t : Fin 2 → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice ArithmeticThetaFullSourceR0268.binaryBasis, (∀ i, (t i).val = ArithmeticThetaFullSourceR0268.binaryRepresentatives i) ∧ Function.Bijective (fun i => ArithmeticThetaOrthogonalConsumerR0127.cosetClass ArithmeticThetaFullSourceR0268.binaryBasis (t i)) ∧ (∀ i j, ((ArithmeticThetaFullSourceR0268.binaryResidues i j : ℤ) : ℚ) = (ArithmeticThetaFullSourceR0268.binaryNorms j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram = ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 0) + ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 1) ∧ (∀ (D : ℕ) (hD : D ≠ 0), 92 ∣ D → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram) = ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 0 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 0 + ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 1 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 23) := by
  refine ⟨BinaryOrthogonalExample.gram_valid, BinaryOrthogonalExample.determinant,
    BinaryOrthogonalExample.orthogonal, BinaryOrthogonalExample.representatives,
    (fun _ => rfl), BinaryOrthogonalExample.bijective, BinaryOrthogonalExample.residues, ?_⟩
  have H := source_orthogonal_factorization 2 binaryGram binaryBasis binaryNorms
    BinaryOrthogonalExample.gram_valid BinaryOrthogonalExample.orthogonal
  unfold Representatives at H
  rw [BinaryOrthogonalExample.determinant] at H
  obtain ⟨ν, hν, hs, he⟩ := H BinaryOrthogonalExample.representatives
    BinaryOrthogonalExample.bijective
  have hn : ν = binaryResidues := by
    funext i j
    apply Int.cast_injective (α := ℚ)
    exact (hν i j).trans (BinaryOrthogonalExample.residues i j).symm
  subst ν
  constructor
  · simpa [Fin.sum_univ_two, BinaryOrthogonalExample.representatives] using hs
  · intro D hD hd
    have hd' : ∀ j, 2 * binaryNorms j ∣ D := by
      intro j
      fin_cases j
      · exact dvd_trans (by norm_num : 4 ∣ 92) hd
      · exact hd
    simpa [Fin.sum_univ_two, Fin.prod_univ_two, binaryNorms, binaryResidues] using he D hD hd'

#print axioms binary_orthogonal_example
end ArithmeticThetaFullSourceR0268
