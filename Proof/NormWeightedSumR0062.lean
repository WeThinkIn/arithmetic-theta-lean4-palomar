module

public import Mathlib
public import NormResiduePermutationR0062
public import NormWeightedPointwiseR0062

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormQuotientsR0062

private theorem sum_range_id_rat (d : ℕ) :
    (∑ i ∈ Finset.range d, (i : ℚ)) = (d : ℚ) * ((d : ℚ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_range_sq_rat (d : ℕ) :
    (∑ i ∈ Finset.range d, (i : ℚ) ^ 2) =
      (d : ℚ) * ((d : ℚ) - 1) * (2 * (d : ℚ) - 1) / 6 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_residue (c d : ℕ) (hc : 1 < c) (hd : 0 < d)
    (hcop : Nat.Coprime c d) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range d, f (residue c d i)) = ∑ i ∈ Finset.range d, f i := by
  have hp := residue_permutation c d hc hd hcop
  have hinj : Set.InjOn (residue c d) (Finset.range d : Set ℕ) := by
    apply Finset.injOn_of_card_image_eq
    rw [hp]
  calc
    (∑ i ∈ Finset.range d, f (residue c d i)) =
        ∑ i ∈ Finset.image (residue c d) (Finset.range d), f i := by
      rw [Finset.sum_image hinj]
    _ = ∑ i ∈ Finset.range d, f i := by rw [hp]

theorem quotient_sum :
    ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d →
      quotientSum c d = ((c : ℚ) - 1) * ((d : ℚ) - 1) / 2 := by
  intro c d hc hd hcop
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hterm (i : ℕ) :
      (quotient c d i : ℚ) =
        ((c : ℚ) * (i : ℚ) - (residue c d i : ℚ)) / (d : ℚ) := by
    have hdiv : c * i = d * (c * i / d) + c * i % d :=
      (Nat.div_add_mod (c * i) d).symm
    have hdivQ : (c : ℚ) * (i : ℚ) =
        (d : ℚ) * (quotient c d i : ℚ) + (residue c d i : ℚ) := by
      simpa [quotient, residue] using congrArg (fun n : ℕ => (n : ℚ)) hdiv
    field_simp [hdq]
    linear_combination -hdivQ
  have hres := sum_residue c d hc hd hcop (fun i => (i : ℚ))
  have hid := sum_range_id_rat d
  unfold quotientSum
  simp_rw [hterm, sub_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  simp_rw [← Finset.mul_sum]
  rw [hres, hid]
  field_simp [hdq]

theorem weighted_sum :
    ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d →
      weightedSum c d =
        (((c : ℚ) ^ 2 - 1) * ((d : ℚ) - 1) * (2 * (d : ℚ) - 1)) / 12 -
          (d : ℚ) * ((c : ℚ) - 1) * ((d : ℚ) - 1) / 4 := by
  intro c d hc hd hcop
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hpoint : ∀ i ∈ Finset.range d,
      weightedTerm c d i =
        (((c : ℚ) * (i : ℚ)) ^ 2 - (residue c d i : ℚ) ^ 2) /
            (2 * (d : ℚ)) -
          ((c : ℚ) * (i : ℚ) - (residue c d i : ℚ)) / 2 := by
    intro i _
    exact weighted_pointwise c d i hd
  rw [weightedSum, Finset.sum_congr rfl hpoint]
  have hsum1 := sum_range_id_rat d
  have hsum2 := sum_range_sq_rat d
  have hres1 := sum_residue c d hc hd hcop (fun i => (i : ℚ))
  have hres2 := sum_residue c d hc hd hcop (fun i => (i : ℚ) ^ 2)
  have hsum :
      (∑ i ∈ Finset.range d,
        (
        (((c : ℚ) * (i : ℚ)) ^ 2 - (residue c d i : ℚ) ^ 2) /
            (2 * (d : ℚ)) -
          ((c : ℚ) * (i : ℚ) - (residue c d i : ℚ)) / 2)) =
        (((c : ℚ) ^ 2 - 1) / (2 * (d : ℚ))) *
            (∑ i ∈ Finset.range d, (i : ℚ) ^ 2) -
          (((c : ℚ) - 1) / 2) * (∑ i ∈ Finset.range d, (i : ℚ)) := by
    have hterm : ∀ i : ℕ,
        (((c : ℚ) * (i : ℚ)) ^ 2 - (residue c d i : ℚ) ^ 2) /
            (2 * (d : ℚ)) -
          ((c : ℚ) * (i : ℚ) - (residue c d i : ℚ)) / 2 =
          ((c : ℚ) ^ 2 / (2 * (d : ℚ))) * (i : ℚ) ^ 2 -
            ((residue c d i : ℚ) ^ 2 / (2 * (d : ℚ))) -
            ((c : ℚ) / 2) * (i : ℚ) + (residue c d i : ℚ) / 2 := by
      intro i
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_div]
    rw [hres1, hres2]
    ring
  rw [hsum, hsum1, hsum2]
  field_simp [hdq]
  ring

end ArithmeticThetaNormQuotientsR0062
