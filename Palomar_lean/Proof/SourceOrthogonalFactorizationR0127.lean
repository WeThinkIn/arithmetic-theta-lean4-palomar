module

public import RationalPreimageCosetsR0127
public import CosetRepresentativeInvarianceR0127
public import IndividualCosetIntegralProductR0127

@[expose] public section

/-! Full source factorization for any representatives of the rational quotient. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaCosets

private lemma integral_residues (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℕ) (hA : ArithmeticThetaComputed.validGram A)
    (hB : OrthogonalData A B m) (t : preimageLattice B) :
    ∃ ν : Fin n → ℤ, ∀ j, (ν j : ℚ) = (m j : ℚ) * t.val j := by
  obtain ⟨x, hx⟩ := t.property
  have hunit : IsUnit (B.map (Int.castRingHom ℚ)).det := by
    apply isUnit_iff_ne_zero.mpr
    change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    change (B.det : ℚ) ≠ 0
    exact_mod_cast hB.1
  change (fun j => (x j : ℚ)) = (B.map (Int.castRingHom ℚ)).mulVec t.val at hx
  have hinv : ((B.map (Int.castRingHom ℚ))⁻¹).mulVec (fun j => (x j : ℚ)) = t.val := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  refine ⟨(B.transpose * A).mulVec x, ?_⟩
  intro j
  rw [(orthogonal_residue_formula n A B m hA.1 hB.1
    (fun j => (hB.2.1 j).1) hB.2.2 x 0).1 j, hinv]

/-- The complete source theta identity and every common-denominator expansion. -/
theorem source_orthogonal_factorization : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ t : Fin B.det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B, ArithmeticThetaOrthogonalConsumerR0127.Representatives B t → ∃ ν : Fin B.det.natAbs → Fin n → ℤ, (∀ i j, (ν i j : ℚ) = (m j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ A = ∑ i : Fin B.det.natAbs, ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m (t i).val ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ A) = ∑ i : Fin B.det.natAbs, ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν i j)) := by
  intro n A B m hA hB t ht
  classical
  choose ν hν using fun i => integral_residues n A B m hA hB (t i)
  refine ⟨ν, hν, ?_⟩
  have hind (i : Fin B.det.natAbs) :=
    (individual_coset_integral_product n A B m hA hB (t i) (ν i) (hν i)).2
  have hsum : thetaZ A = ∑ i, cosetSeries m (t i).val := by
    obtain ⟨D, hDpos, hd⟩ := common_exponent_denominator n m (fun j => (hB.2.1 j).1)
    have hD : D ≠ 0 := ne_of_gt hDpos
    obtain ⟨e, ρ, hρ, hfull⟩ := full_theta_factorization n A B m hA.1 hA.2.1
      hA.2.2 hB.1 hB.2.1 hB.2.2 D hD hd
    obtain ⟨E, hE, _⟩ := rational_preimage_cosets n B hB.1
    let T : Fin B.det.natAbs ≃ RationalCosets B := Equiv.ofBijective _ ht
    let p : Fin B.det.natAbs ≃ Fin B.det.natAbs :=
      (e.trans E.symm.toEquiv).trans T.symm
    let C := B.map (Int.castRingHom ℚ)
    have hunit : IsUnit C.det := by
      apply isUnit_iff_ne_zero.mpr
      change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
      rw [← RingHom.map_det]
      change (B.det : ℚ) ≠ 0
      exact_mod_cast hB.1
    have hv (i : Fin B.det.natAbs) :
        C.mulVec (C⁻¹.mulVec (castVec n (ρ i))) = castVec n (ρ i) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    let v : Fin B.det.natAbs → preimageLattice B := fun i =>
      ⟨C⁻¹.mulVec (castVec n (ρ i)), ⟨ρ i, (hv i).symm⟩⟩
    have hclass (i : Fin B.det.natAbs) : cosetClass B (v i) = cosetClass B (t (p i)) := by
      apply E.injective
      rw [hE (v i) (ρ i) (hv i), hρ.1 i]
      change e i = E (T (T.symm (E.symm (e i))))
      simp only [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have hseries (i : Fin B.det.natAbs) :
        cosetSeries m (v i).val = cosetSeries m (t (p i)).val :=
      coset_representative_invariance n B m (v i) (t (p i)) (hclass i)
    have hvν (i : Fin B.det.natAbs) (j : Fin n) :
        (((B.transpose * A).mulVec (ρ i)) j : ℚ) = (m j : ℚ) * (v i).val j :=
      (orthogonal_residue_formula n A B m hA.1 hB.1
        (fun j => (hB.2.1 j).1) hB.2.2 (ρ i) 0).1 j
    have hvprod (i : Fin B.det.natAbs) :=
      (individual_coset_integral_product n A B m hA hB (v i)
        ((B.transpose * A).mulVec (ρ i)) (hvν i)).2 D hD hd
    apply (expanded_identity_faithful D hD _ _).mp
    change PowerSeries.expand D hD (thetaZ A) = _ at hfull
    calc
      PowerSeries.expand D hD (thetaZ A) =
          ∑ i, ∏ j, scaledUnary (m j) (D / (2 * m j))
            (((B.transpose * A).mulVec (ρ i)) j) := hfull
      _ = ∑ i, PowerSeries.expand D hD (cosetSeries m (v i).val) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hvprod i).symm
      _ = ∑ i, PowerSeries.expand D hD (cosetSeries m (t (p i)).val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hseries i]
      _ = ∑ i, PowerSeries.expand D hD (cosetSeries m (t i).val) :=
        p.sum_comp (fun i => PowerSeries.expand D hD (cosetSeries m (t i).val))
      _ = PowerSeries.expand D hD (∑ i, cosetSeries m (t i).val) :=
        (map_sum (PowerSeries.expand D hD) _ _).symm
  refine ⟨hsum, ?_⟩
  intro D hD hd
  rw [hsum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => hind i D hD hd)

end ArithmeticThetaOrthogonalConsumerR0127
