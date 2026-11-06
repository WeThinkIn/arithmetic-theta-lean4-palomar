import Mathlib

/-! Positive weighted residue shells and their complete generating series. -/
namespace ArithmeticThetaCosets
open scoped BigOperators

/-- A product supplies a common positive denominator, including the empty family. -/
theorem common_exponent_denominator (n : ℕ) (m : Fin n → ℕ)
    (hm : ∀ j, 0 < m j) :
    ∃ D : ℕ, 0 < D ∧ ∀ j : Fin n, 2 * m j ∣ D := by
  refine ⟨∏ j, 2 * m j, Finset.prod_pos (fun j _ => Nat.mul_pos (by decide) (hm j)), ?_⟩
  intro j
  exact Finset.dvd_prod_of_mem (fun j => 2 * m j) (Finset.mem_univ j)

lemma coordinate_bound (w : ℕ) (hw : 0 < w) (r : ℤ) (C : ℕ)
    (h : (w : ℤ) * r ^ 2 ≤ (C : ℤ)) :
    -(C : ℤ) - 1 ≤ r ∧ r ≤ (C : ℤ) + 1 := by
  have hw' : (1 : ℤ) ≤ w := by exact_mod_cast hw
  have hs := sq_nonneg r
  have : r ^ 2 ≤ (C : ℤ) := by nlinarith
  constructor <;> nlinarith [sq_nonneg (r + 1), sq_nonneg (r - 1)]

/-- Every bounded residue set lies in a finite integer box. -/
theorem weighted_residue_local_finite (n : ℕ) (m w : Fin n → ℕ)
    (ν : Fin n → ℤ) (hw : ∀ j, 0 < w j) (C : ℕ) :
    Set.Finite {r : (Fin n → ℤ) |
      (∀ j : Fin n, Int.ModEq (m j : ℤ) (r j) (ν j)) ∧
      (∑ j : Fin n, (w j : ℤ) * (r j) ^ 2) ≤ (C : ℤ)} := by
  classical
  have hbox : Set.Finite {r : Fin n → ℤ |
      ∀ j, r j ∈ Set.Icc (-(C : ℤ) - 1) ((C : ℤ) + 1)} :=
    Set.Finite.pi' fun _ => Set.finite_Icc _ _
  apply hbox.subset
  intro r hr j
  apply coordinate_bound (w j) (hw j) (r j) C
  exact le_trans (Finset.single_le_sum
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Finset.mem_univ j)) hr.2

/-- Unary exact shells are finite, with no restriction on the modulus. -/
lemma unary_shell_finite (m w : ℕ) (ν : ℤ) (hw : 0 < w) (a : ℕ) :
    Set.Finite {r : ℤ | Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r ^ 2 = (a : ℤ)} := by
  have h := weighted_residue_local_finite 1 (fun _ => m) (fun _ => w)
    (fun _ => ν) (fun _ => hw) a
  apply (h.image (fun r => r 0)).subset
  intro r hr
  refine ⟨fun _ => r, ?_, rfl⟩
  exact ⟨fun _ => hr.1, by simpa using hr.2.le⟩

/-- Tuple exact shells inherit finiteness from bounded shells. -/
lemma tuple_shell_finite (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ)
    (hw : ∀ j, 0 < w j) (a : ℕ) :
    Set.Finite {r : Fin n → ℤ | (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) ∧
      (∑ j, (w j : ℤ) * (r j) ^ 2) = (a : ℤ)} := by
  exact (weighted_residue_local_finite n m w ν hw a).subset
    (fun _ hr => ⟨hr.1, hr.2.le⟩)

/-- The natural number energy has exactly the original integer value. -/
lemma energy_cast (w : ℕ) (r : ℤ) :
    ((w * r.natAbs ^ 2 : ℕ) : ℤ) = (w : ℤ) * r ^ 2 := by
  simp [sq_abs]


/-- Actual integer solutions of one exponent equation. -/
abbrev UnaryShell (m w : ℕ) (ν : ℤ) (a : ℕ) :=
  {r : ℤ // Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r ^ 2 = (a : ℤ)}

/-- Actual integer tuples of a prescribed total exponent. -/
abbrev TupleShell (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ) (a : ℕ) :=
  {r : Fin n → ℤ // (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) ∧
    (∑ j, (w j : ℤ) * (r j) ^ 2) = (a : ℤ)}

/-- All natural exponent allocations with total `a`. -/
abbrev Allocations (n a : ℕ) :=
  ↥(Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) a)

/-- Combining unary solutions gives a tuple of the same total energy. -/
def assemble (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ) (a : ℕ)
    (s : Σ l : Allocations n a, ∀ j, UnaryShell (m j) (w j) (ν j) (l.val j)) :
    TupleShell n m w ν a := by
  refine ⟨fun j => (s.2 j).val, (fun j => (s.2 j).property.1), ?_⟩
  calc
    (∑ j, (w j : ℤ) * ((s.2 j).val) ^ 2) = ∑ j, ((s.1.val j : ℕ) : ℤ) :=
      Finset.sum_congr rfl (fun j _ => (s.2 j).property.2)
    _ = (a : ℤ) := by
      rw [← Nat.cast_sum, (Finset.mem_finsuppAntidiag.mp s.1.property).1]

lemma assemble_bijective (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ) (a : ℕ) :
    Function.Bijective (assemble n m w ν a) := by
  classical
  constructor
  · rintro ⟨l, x⟩ ⟨k, y⟩ h
    have hxy : ∀ j, (x j).val = (y j).val :=
      fun j => congrFun (congrArg Subtype.val h) j
    have hlk : l = k := by
      apply Subtype.ext
      apply Finsupp.ext
      intro j
      apply Int.ofNat_inj.mp
      rw [← (x j).property.2, ← (y j).property.2, hxy j]
    subst k
    congr 1
    funext j
    exact Subtype.ext (hxy j)
  · intro r
    let l : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun j => w j * (r.val j).natAbs ^ 2)
    have hl : l ∈ Finset.finsuppAntidiag Finset.univ a := by
      apply Finset.mem_finsuppAntidiag.mpr
      refine ⟨?_, Finset.subset_univ _⟩
      apply Int.ofNat_inj.mp
      rw [Nat.cast_sum]
      change (∑ j, ((w j * (r.val j).natAbs ^ 2 : ℕ) : ℤ)) = (a : ℤ)
      simpa only [energy_cast] using r.property.2
    refine ⟨⟨⟨l, hl⟩, fun j => ⟨r.val j, r.property.1 j, ?_⟩⟩, ?_⟩
    · exact (energy_cast (w j) (r.val j)).symm
    · rfl

/-- The coefficient bijection is valid also for no coordinates and exponent zero. -/
noncomputable def shellEquiv (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ) (a : ℕ) :
    (Σ l : Allocations n a, ∀ j, UnaryShell (m j) (w j) (ν j) (l.val j)) ≃
      TupleShell n m w ν a :=
  Equiv.ofBijective (assemble n m w ν a) (assemble_bijective n m w ν a)

/-- Finite convolution counts all tuples, coefficient by coefficient. -/
theorem unary_product_coefficients (n : ℕ) (m w : Fin n → ℕ) (ν : Fin n → ℤ)
    (hw : ∀ j, 0 < w j) :
    (PowerSeries.mk (fun a : ℕ => (Nat.card {r : (Fin n → ℤ) //
      (∀ j : Fin n, Int.ModEq (m j : ℤ) (r j) (ν j)) ∧
      (∑ j : Fin n, (w j : ℤ) * (r j) ^ 2) = (a : ℤ)} : ℤ)) : PowerSeries ℤ) =
    ∏ j : Fin n, (PowerSeries.mk (fun a : ℕ => (Nat.card {r : ℤ //
      Int.ModEq (m j : ℤ) r (ν j) ∧ (w j : ℤ) * r ^ 2 = (a : ℤ)} : ℤ)) :
      PowerSeries ℤ) := by
  classical
  apply PowerSeries.ext
  intro a
  let (j : Fin n) (b : ℕ) : Finite (UnaryShell (m j) (w j) (ν j) b) :=
    (unary_shell_finite (m j) (w j) (ν j) (hw j) b).to_subtype
  have hc := Nat.card_congr (shellEquiv n m w ν a).symm
  rw [Nat.card_sigma] at hc
  simp only [Nat.card_pi] at hc
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk]
  change (Nat.card (TupleShell n m w ν a) : ℤ) = _
  rw [hc, Nat.cast_sum]
  simp only [Nat.cast_prod]
  exact Finset.sum_coe_sort (Finset.finsuppAntidiag Finset.univ a)
    (fun l => ∏ j : Fin n, (Nat.card (UnaryShell (m j) (w j) (ν j) (l j)) : ℤ))

end ArithmeticThetaCosets
