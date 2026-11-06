import Mathlib
import NormQuotientDefinitionsR0062

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormQuotientsR0062

/-! The residues of multiplication by a number coprime to `d` are a
permutation of the canonical representatives modulo `d`. -/
theorem residue_permutation :
    ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d →
      Finset.image (fun i : ℕ => residue c d i) (Finset.range d) = Finset.range d := by
  intro c d hc hd hcop
  have hmaps : Finset.image (fun i : ℕ => residue c d i) (Finset.range d) ⊆
      Finset.range d := by
    rw [Finset.image_subset_iff]
    intro i hi
    simpa [Finset.mem_range, residue] using (Nat.mod_lt (c * i) hd)
  have hinj : Set.InjOn (fun i : ℕ => residue c d i) (Finset.range d : Set ℕ) := by
    intro i hi j hj hij
    have hi_lt : i < d := Finset.mem_range.mp hi
    have hj_lt : j < d := Finset.mem_range.mp hj
    by_cases hle : i ≤ j
    · have hmod : c * i ≡ c * j [MOD d] := by
        change c * i % d = c * j % d
        simpa [residue] using hij
      have hdvd : d ∣ c * (j - i) := by
        have h : d ∣ c * j - c * i := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left c hle)).mp hmod
        simpa [Nat.mul_sub_left_distrib] using h
      have hdvd' : d ∣ j - i := hcop.symm.dvd_of_dvd_mul_left hdvd
      have hzero : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
    · have hle' : j ≤ i := by omega
      have hmod : c * j ≡ c * i [MOD d] := by
        change c * j % d = c * i % d
        simpa [residue] using hij.symm
      have hdvd : d ∣ c * (i - j) := by
        have h : d ∣ c * i - c * j := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left c hle')).mp hmod
        simpa [Nat.mul_sub_left_distrib] using h
      have hdvd' : d ∣ i - j := hcop.symm.dvd_of_dvd_mul_left hdvd
      have hzero : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
  apply Finset.eq_of_subset_of_card_le hmaps
  have hcard : (Finset.image (fun i : ℕ => residue c d i) (Finset.range d)).card = d := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  simpa [Finset.card_range] using hcard.symm.le

end ArithmeticThetaNormQuotientsR0062
