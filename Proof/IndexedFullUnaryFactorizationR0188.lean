module

public import LatticeGlobalSectionsDefinitionsR0188
public import ComputedFamilyFormalUnaryConsumerR0127

@[expose] public section

/-! Exact distinct unary indexing and the literal full-series factorization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaOrthogonalAlgorithm ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaSimultaneousUnaryR0187

private lemma centered_bounds (m : ℕ) (a : Fin m) :
    -(m : ℤ) ≤ 2 * centered m a ∧ 2 * centered m a < (m : ℤ) := by
  unfold centered
  split_ifs <;> omega

private lemma centered_modEq (m : ℕ) (a : Fin m) :
    Int.ModEq (m : ℤ) (centered m a) (a.val : ℤ) := by
  unfold centered
  split_ifs
  · exact Int.ModEq.refl _
  · rw [Int.modEq_iff_dvd]
    exact ⟨1, by omega⟩

private lemma cleared_eq_scaled (m : ℕ) (hm : 0 < m) (a : Fin m) :
    ArithmeticThetaUnaryProduct.clearedUnaryTheta m (centered m a) =
      scaledUnary m 12 (centered m a) := by
  ext b
  rw [ArithmeticThetaUnaryProduct.clearedUnaryTheta_residue_coefficient
    m b (centered m a) hm (centered_bounds m a)]
  simp only [scaledUnary, PowerSeries.coeff_mk]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun r => by
    rw [Int.modEq_iff_dvd, dvd_sub_comm]
    norm_num)

private lemma unary_bridge (N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hd : m ∣ N) (a : Fin m)
    (hw : 24 * N^2 / (2*m) ≠ 0) :
    PowerSeries.expand (24 * N^2 / (2*m)) hw
      (ArithmeticThetaSchrodingerR0119.unary ℂ m a) =
      unarySeries ℂ N m (centered m a) := by
  let : NeZero m := ⟨ne_of_gt hm⟩
  have hd2 : m ∣ N^2 := dvd_trans hd (by exact ⟨N, by ring⟩)
  have hq : N^2 / m ≠ 0 := ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd (pow_pos hN 2) hd2) hm)
  have he : 24 * N^2 / (2*m) = (N^2 / m) * 12 := by
    apply Nat.div_eq_of_eq_mul_right (by omega : 0 < 2*m)
    have hmul := Nat.div_mul_cancel hd2
    nlinarith
  unfold unarySeries
  rw [← PowerSeries.expand_apply _ hq, cleared_eq_scaled m hm a,
    PowerSeries.map_expand]
  rw [unary_parameter_identification ℂ m 12 (by decide) (centered m a) a
    (centered_modEq m a)]
  rw [← PowerSeries.expand_mul]
  simp only [he]

private lemma exact_indexing {n h : ℕ} (A : Matrices n h)
    (t : (i : Fin h) → Cosets A i → preimageLattice (basisMatrix (A i)))
    (ν : (i : Fin h) → Cosets A i → (j : Fin n) → Fin (naturalNorms (A i) j))
    (ht : ∀ i, Representatives (basisMatrix (A i)) (t i))
    (hν : ∀ i a j, ∃ z : ℤ, (naturalNorms (A i) j : ℚ) * (t i a).val j =
      ((ν i a j).val : ℚ) + (naturalNorms (A i) j : ℚ) * (z : ℚ)) :
    ∃ U : Indexing A, Indexed A U ∧ U.residue = ν := by
  classical
  -- Keep the representatives and residues from the accepted full consumer.
  let T := (i : Fin h) × (Cosets A i × Fin n)
  let f : T → ℕ × ℤ := fun x =>
    (naturalNorms (A x.1) x.2.2, centered _ (ν x.1 x.2.1 x.2.2))
  let s : Finset (ℕ × ℤ) := Finset.univ.image f
  let e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm
  let g : T → ↥s := fun x => ⟨f x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  let U : Indexing A :=
    { representatives := t, residue := ν, count := Fintype.card ↥s
      pair := fun z => (e z).val
      index := fun i a j => e.symm (g ⟨i, a, j⟩) }
  have hpair i a j : U.pair (U.index i a j) =
      (naturalNorms (A i) j, centered _ (ν i a j)) :=
    congrArg Subtype.val (e.apply_symm_apply (g ⟨i, a, j⟩))
  have hsurj (z : Fin U.count) : ∃ i a j, U.index i a j = z := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (e z).property
    refine ⟨x.1, x.2.1, x.2.2, ?_⟩
    change e.symm (g x) = z
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext hx
  exact ⟨U, ⟨ht, hν, Subtype.val_injective.comp e.injective, hpair, hsurj⟩, rfl⟩


private lemma finite_lcm_data {I : Type} [Fintype I] (f : I → ℕ)
    (i₀ : I) (hf : ∀ i, 0 < f i ∧ Even (f i)) :
    0 < Finset.univ.lcm f ∧ Even (Finset.univ.lcm f) ∧
      ∀ i, f i ∣ Finset.univ.lcm f := by
  classical
  have hd (i : I) : f i ∣ Finset.univ.lcm f := Finset.dvd_lcm (Finset.mem_univ i)
  refine ⟨Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun i _ => ne_of_gt (hf i).1)), ?_, hd⟩
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp (hf i₀).2).trans (hd i₀))

private lemma common_parameter {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) :
    0 < commonN A ∧ Even (commonN A) ∧
    (∀ i j, naturalNorms (A i) j ∣ commonN A) := by
  classical
  have hm (i : Fin h) (j : Fin n) :
      0 < naturalNorms (A i) j ∧ Even (naturalNorms (A i) j) := by
    have hp := (computed_natural_data n (A i) (hA i).1 (hA i).2.1 (hA i).2.2).1 j
    exact ⟨hp.1, hp.2.1⟩
  obtain ⟨hp, he, hd⟩ := finite_lcm_data
    (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
    (⟨0, hh⟩, ⟨0, hn⟩) (fun ij => hm ij.1 ij.2)
  exact ⟨hp, he, fun i j => hd (i, j)⟩

private lemma twice_dvd_level (N m : ℕ) (hd : m ∣ N) : 2*m ∣ 24*N^2 := by
  obtain ⟨v, hv⟩ := hd
  refine ⟨12*v*N, ?_⟩
  rw [hv]
  ring

/-- The common parameter is the exact lcm and the enumeration contains exactly
the occurring centered pairs; the factorization holds for every coefficient family. -/
theorem indexed_full_unary_factorization :
    ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : Matrices n h),
    (∀ i, ArithmeticThetaComputed.validGram (A i)) →
    0 < commonN A ∧ Even (commonN A) ∧
    (∀ (i : Fin h) (j : Fin n), naturalNorms (A i) j ∣ commonN A) ∧
    ∃ U : Indexing A, Indexed A U ∧
      (∀ j : Fin U.count, 0 < (U.pair j).1 ∧ Even (U.pair j).1 ∧
        (U.pair j).1 ∣ commonN A ∧
        (-((U.pair j).1 : ℤ) ≤ 2*(U.pair j).2 ∧
          2*(U.pair j).2 < ((U.pair j).1 : ℤ))) ∧ FormalIdentity A U := by
  intro n h hn hh A hA
  classical
  have hm i := (computed_natural_data n (A i) (hA i).1 (hA i).2.1 (hA i).2.2).1
  obtain ⟨hN, hEven, hd⟩ := common_parameter hn hh A hA
  have hD : 24 * (commonN A)^2 ≠ 0 := ne_of_gt (by positivity)
  have hdD (i : Fin h) (j : Fin n) :
      2 * naturalNorms (A i) j ∣ 24 * (commonN A)^2 :=
    twice_dvd_level _ _ (hd i j)
  obtain ⟨t, ν, hw, ht, hν, hf⟩ :=
    computed_family_formal_unary_consumer n h A hA (24 * (commonN A)^2) hD hdD
  obtain ⟨U, hU, hres⟩ := exact_indexing A t ν ht hν
  have hpair i a j : U.pair (U.index i a j) =
      (naturalNorms (A i) j, centered _ (ν i a j)) := by
    rw [hU.2.2.2.1, hres]
  have hsurj := hU.2.2.2.2
  refine ⟨hN, hEven, hd, U, hU, ?_, ?_⟩
  · intro z
    obtain ⟨i, a, j, rfl⟩ := hsurj z
    rw [hpair]
    exact ⟨(hm i j).1, (hm i j).2.1, hd i j, centered_bounds _ _⟩
  · intro c
    unfold expanded
    rw [← PowerSeries.expand_apply _ hD, hf c]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.prod_congr rfl
    intro j _
    rw [hpair]
    exact unary_bridge _ _ hN (hm i j).1 (hd i j) (ν i a j) (hw i j)

end ArithmeticThetaLatticeSectionsR0188

#print axioms ArithmeticThetaLatticeSectionsR0188.indexed_full_unary_factorization
