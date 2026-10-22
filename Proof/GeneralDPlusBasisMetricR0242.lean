module

public import Rank16Basis
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArithmeticThetaGeneralDPlusR0242
namespace BasisMetric
open ArithmeticThetaRank16

private lemma column (n : ℕ) (hn : 1 < n) (j : Fin n) :
    (fun k => latticeBasis n k j) =
      if j.val = 0 then (fun _ => (1/2 : ℚ))
      else if j.val = n-1 then Pi.single (⟨n-1, by omega⟩ : Fin n) 2
      else Pi.single j 1 - Pi.single (⟨n-1, by omega⟩ : Fin n) 1 := by
  ext k
  simp only [latticeBasis]
  have hk : k = (⟨n-1, by omega⟩ : Fin n) ↔ k.val = n-1 := Fin.ext_iff
  split_ifs <;> simp_all

private lemma det (n : ℕ) (hn : 1 < n) : (latticeBasis n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (lattice_basis_lower n)]
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hol : o ≠ l := by simp only [o, l, ne_eq, Fin.mk.injEq]; omega
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ o)]
  rw [← Finset.mul_prod_erase _ _ (show l ∈ Finset.univ.erase o by simp [hol.symm])]
  have hrest : (∏ i ∈ (Finset.univ.erase o).erase l, latticeBasis n i i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    have hi0 : i.val ≠ 0 := by intro h; apply hi.2; exact Fin.ext h
    have hil : i.val ≠ n-1 := by intro h; apply hi.1; exact Fin.ext h
    simp [latticeBasis, hi0, hil]
  rw [hrest]
  norm_num [latticeBasis, o, l, show n-1 ≠ 0 by omega]

private lemma gram (n : ℕ) (hn : 1 < n) (h4 : 4 ∣ n) :
    (latticeBasis n).transpose * latticeBasis n = (latticeGram n).map (Int.castRingHom ℚ) := by
  let l : Fin n := ⟨n-1, by omega⟩
  have hdiv : ((n/4 : ℕ) : ℚ) = (n : ℚ)/4 := by
    exact Nat.cast_div h4 (by norm_num)
  have hconst : (fun _ : Fin n => (1/2 : ℚ)) ⬝ᵥ (fun _ => (1/2 : ℚ)) = (n : ℚ)/4 := by
    simp [dotProduct]; ring
  have hlast : n-1 ≠ 0 := by omega
  ext i j
  change (fun k => latticeBasis n k i) ⬝ᵥ (fun k => latticeBasis n k j) = _
  rw [column n hn i, column n hn j]
  change _ = (latticeGram n i j : ℚ)
  have hil : i = l ↔ i.val = n-1 := Fin.ext_iff
  have hjl : j = l ↔ j.val = n-1 := Fin.ext_iff
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
  · simp only [hi0, hj0, ↓reduceIte, latticeGram]
    change (fun _ : Fin n => (1/2 : ℚ)) ⬝ᵥ (fun _ => (1/2 : ℚ)) = ((n/4 : ℕ) : ℚ)
    rw [hconst]
    exact hdiv.symm
  all_goals
    by_cases hi : i.val = n-1 <;> by_cases hj : j.val = n-1 <;>
      by_cases hij : i = j <;>
      simp_all [latticeGram, dotProduct_sub, sub_dotProduct, dotProduct_single,
        single_dotProduct, l, eq_comm] <;> norm_num


end BasisMetric

theorem general_dplus_basis_metric : ∀ n : ℕ, 8 ∣ n →
    (ArithmeticThetaRank16.latticeBasis n).det = 1 ∧
    (ArithmeticThetaRank16.latticeBasis n).transpose * ArithmeticThetaRank16.latticeBasis n =
      (ArithmeticThetaRank16.latticeGram n).map (Int.castRingHom ℚ) := by
  intro n hn
  by_cases hz : n = 0
  · subst n
    constructor
    · simp
    · ext i; exact Fin.elim0 i
  have hn8 : 8 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hn
  exact ⟨BasisMetric.det n (by omega),
    BasisMetric.gram n (by omega) (dvd_trans (by norm_num : 4 ∣ 8) hn)⟩

end ArithmeticThetaGeneralDPlusR0242

#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_basis_metric
