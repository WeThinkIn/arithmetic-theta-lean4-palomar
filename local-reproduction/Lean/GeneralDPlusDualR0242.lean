import GeneralDPlusEvenUnimodularR0242

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArithmeticThetaGeneralDPlusR0242
namespace Dual
open ArithmeticThetaRank16

lemma cast_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (A.map (Int.castRingHom ℚ)).mulVec (fun i => (x i : ℚ)) =
      fun i => (A.mulVec x i : ℚ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

lemma member_coordinates (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ) :
    v ∈ lattice n ↔ ∃ z : Fin n → ℤ,
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) = v := by
  rw [(general_dplus_even_unimodular n hn).2.2.1 v,
    Coordinates.original_basis_image n hn]

lemma member_of_dual (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ)
    (hv : dualMember n v) : v ∈ lattice n := by
  classical
  obtain ⟨b, hb⟩ := (general_dplus_even_unimodular n hn).2.2.2.1
  have hp : ∀ j : Fin n, ∃ a : ℤ,
      (latticeBasis n).transpose.mulVec v j = (a : ℚ) := by
    intro j
    obtain ⟨a, ha⟩ := hv (b j)
    refine ⟨a, ?_⟩
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hb, mul_comm] using ha
  choose a ha using hp
  let z : Fin n → ℤ := (latticeGram n).adjugate.mulVec a
  have hz : (latticeGram n).mulVec z = a := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      (general_dplus_even_unimodular n hn).2.1, one_smul, Matrix.one_mulVec]
  apply (member_coordinates n hn v).mpr
  refine ⟨z, ?_⟩
  have hu : IsUnit (latticeBasis n).transpose :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by
      rw [Matrix.det_transpose, (general_dplus_basis_metric n hn).1]
      exact isUnit_one)
  apply Matrix.mulVec_injective_of_isUnit hu
  rw [Matrix.mulVec_mulVec, (general_dplus_basis_metric n hn).2, cast_mulVec, hz]
  exact (funext ha).symm

lemma dual_of_member (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ)
    (hv : v ∈ lattice n) : dualMember n v := by
  obtain ⟨x, rfl⟩ := (member_coordinates n hn v).mp hv
  intro w
  obtain ⟨y, hy⟩ := (member_coordinates n hn w.val).mp w.property
  refine ⟨x ⬝ᵥ (latticeGram n).mulVec y, ?_⟩
  change (latticeBasis n).mulVec (fun i => (x i : ℚ)) ⬝ᵥ w.val = _
  rw [← hy, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, (general_dplus_basis_metric n hn).2, cast_mulVec]
  simp [dotProduct]

end Dual

/-- The actual integer span of the prescribed D-plus basis equals its dual
for the standard rational Euclidean pairing, including in rank zero. -/
theorem general_dplus_dual : ∀ n : ℕ, 8 ∣ n → ∀ v : Fin n → ℚ,
    dualMember n v ↔ v ∈ lattice n := by
  intro n hn v
  exact ⟨Dual.member_of_dual n hn v, Dual.dual_of_member n hn v⟩

end ArithmeticThetaGeneralDPlusR0242

#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_dual
