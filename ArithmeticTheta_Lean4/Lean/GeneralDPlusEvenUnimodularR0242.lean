import GeneralDPlusDefinitionsR0242
import GeneralDPlusBasisMetricR0242
import GeneralDPlusCoordinatesR0242

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArithmeticThetaGeneralDPlusR0242
namespace EvenUnimodular
open ArithmeticThetaRank16

lemma sum_columns (n : ℕ) (z : Fin n → ℤ) :
    (∑ j, z j • (fun i => latticeBasis n i j)) =
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma member (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ) :
    v ∈ lattice n ↔ originalDPlus n v := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun,
    Coordinates.original_basis_image n hn]
  simp_rw [sum_columns]

lemma independent (n : ℕ) (hn : 8 ∣ n) :
    LinearIndependent ℤ (fun j : Fin n => fun i => latticeBasis n i j) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro x y h
  have he : x = y := Coordinates.lattice_basis_injective n hn (by
    simpa only [sum_columns] using h)
  exact fun i => congrFun he i

lemma basis (n : ℕ) (hn : 8 ∣ n) :
    ∃ b : Module.Basis (Fin n) ℤ (lattice n),
      ∀ j i, (b j).val i = latticeBasis n i j := by
  refine ⟨Module.Basis.span (independent n hn), ?_⟩
  intro j i
  exact congrFun (Module.Basis.coe_span_apply (independent n hn) j) i

lemma determinant (n : ℕ) (hn : 8 ∣ n) : (latticeGram n).det = 1 := by
  have hd := congrArg Matrix.det (general_dplus_basis_metric n hn).2
  rw [Matrix.det_mul, Matrix.det_transpose,
    (general_dplus_basis_metric n hn).1, det_map_int] at hd
  have hq : ((latticeGram n).det : ℚ) = 1 := by simpa using hd.symm
  exact_mod_cast hq

lemma valid (n : ℕ) (hn : 8 ∣ n) : ArithmeticThetaComputed.validGram (latticeGram n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (latticeGram n).transpose = latticeGram n
    have hs : ((latticeGram n).map (Int.castRingHom ℚ)).transpose =
        (latticeGram n).map (Int.castRingHom ℚ) := by
      rw [← (general_dplus_basis_metric n hn).2]
      simp [Matrix.transpose_mul]
    ext i j
    have hij := congrFun (congrFun hs i) j
    change (latticeGram n j i : ℚ) = (latticeGram n i j : ℚ) at hij
    change latticeGram n j i = latticeGram n i j
    exact_mod_cast hij
  · intro i
    obtain ⟨k, rfl⟩ := hn
    simp only [latticeGram]
    split_ifs
    · have h : 8*k/4 = 2*k := by omega
      rw [h]
      exact ⟨(k : ℤ), by push_cast; ring⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨1, by norm_num⟩
  · apply QuadraticMap.PosDef.smul _ (by norm_num : (0:ℚ) < 1/2)
    rw [← (general_dplus_basis_metric n hn).2]
    apply Matrix.PosDef.toQuadraticForm'
    have hu : IsUnit (latticeBasis n) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
      rw [(general_dplus_basis_metric n hn).1]
      exact isUnit_one)
    simpa using Matrix.PosDef.conjTranspose_mul_self (latticeBasis n)
      (Matrix.mulVec_injective_of_isUnit hu)

lemma half_norm (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ)
    (hv : originalDPlus n v) : ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ) := by
  obtain ⟨c, hc⟩ := (Coordinates.original_basis_image n hn v).mp hv
  let y := (doubledBasis n).mulVec c
  have hy : DPlusDoubled n y := Coordinates.doubled_basis_member hn c
  have he : doubledRealization n y = v := by
    simpa only [doubled_basis_mul] using hc
  obtain ⟨z, hz⟩ := norm_divisible_eight n hn y hy
  refine ⟨z, ?_⟩
  rw [← he]
  change (∑ i, ((y i : ℚ)/2)^2)/2 = _
  rw [rational_norm, hz]
  push_cast
  ring

end EvenUnimodular

/-- The prescribed integral span is an even unimodular lattice in every rank
  divisible by eight, including rank zero. -/
theorem general_dplus_even_unimodular : ∀ n : ℕ, 8 ∣ n →
    ArithmeticThetaComputed.validGram (ArithmeticThetaRank16.latticeGram n) ∧
    (ArithmeticThetaRank16.latticeGram n).det = 1 ∧
    (∀ v : Fin n → ℚ, v ∈ lattice n ↔ ArithmeticThetaRank16.originalDPlus n v) ∧
    (∃ b : Module.Basis (Fin n) ℤ (lattice n), ∀ (j i : Fin n),
      (b j).val i = ArithmeticThetaRank16.latticeBasis n i j) ∧
    (∀ v : Fin n → ℚ, ArithmeticThetaRank16.originalDPlus n v →
      ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ)) := by
  intro n hn
  exact ⟨EvenUnimodular.valid n hn, EvenUnimodular.determinant n hn,
    EvenUnimodular.member n hn, EvenUnimodular.basis n hn,
    EvenUnimodular.half_norm n hn⟩

end ArithmeticThetaGeneralDPlusR0242

#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular
