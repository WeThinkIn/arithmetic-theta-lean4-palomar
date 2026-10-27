import ComputableIntegerBoxes
import EnumerationAlgorithm

import Mathlib

namespace ArithmeticThetaEnumeration

theorem integer_numerator_identity (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    ((∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) : ℚ) =
      2 * ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap, mul_assoc, mul_comm, mul_left_comm]

theorem interval_membership (R : ℕ) (x : ℤ) :
    x ∈ (Finset.range (2 * R + 1)).image (fun k : ℕ => (k : ℤ) - (R : ℤ)) ↔
      -(R : ℤ) ≤ x ∧ x ≤ (R : ℤ) := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨(x + (R : ℤ)).toNat, ?_, ?_⟩ <;> omega

theorem rational_cofactor_bound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : M.IsSymm) (hp : M.toQuadraticForm'.PosDef) (x : Fin n → ℚ)
    (C : ℚ) (hC : M.toQuadraticForm' x ≤ C) (j : Fin n) :
    M.det ≠ 0 ∧ |M.det| * x j ^ 2 ≤ C * |M.adjugate j j| := by
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.PosDef.of_toQuadraticForm' hM hp).isUnit).ne_zero
  refine ⟨hdet, ?_⟩
  let v : Fin n → ℚ := fun i => M.adjugate i j
  have hv : M.mulVec v = M.det • Pi.single j 1 := by
    ext i
    have hi := congrArg (fun T : Matrix (Fin n) (Fin n) ℚ => T i j) (Matrix.mul_adjugate M)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, v, Matrix.one_apply,
      Pi.single_apply, eq_comm] using hi
  have hb (u : Fin n → ℚ) : M.toBilin' u v = M.det * u j := by
    rw [Matrix.toBilin'_apply', hv]
    simp [dotProduct, Pi.single_apply, mul_comm]
  have hn (u : Fin n → ℚ) : 0 ≤ M.toBilin' u u := hp.nonneg u
  have hcs := M.toBilin'.apply_sq_le_of_symm hn
    ⟨fun x y => (Matrix.isSymm_toBilin'_iff_isSymm.mpr hM).eq x y⟩ x v
  rw [hb x, hb v] at hcs
  have hdv : 0 ≤ M.det * M.adjugate j j := by simpa [hb, v] using hn v
  have habs : M.det * M.adjugate j j = |M.det| * |M.adjugate j j| := by
    rw [← abs_mul, abs_of_nonneg hdv]
  have hsq : M.det ^ 2 = |M.det| ^ 2 := (sq_abs _).symm
  have hxx : M.toBilin' x x ≤ C := hC
  have hh := mul_le_mul_of_nonneg_right hxx hdv
  change (M.det * x j) ^ 2 ≤ M.toBilin' x x * (M.det * M.adjugate j j) at hcs
  have hprod : |M.det| * (|M.det| * x j ^ 2) ≤
      |M.det| * (C * |M.adjugate j j|) := by
    calc
      _ = (M.det * x j) ^ 2 := by rw [mul_pow, hsq]; ring
      _ ≤ _ := hcs.trans (by simpa [habs, mul_assoc, mul_comm, mul_left_comm] using hh)
  exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp hprod

theorem cofactor_square_bound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    A.det ≠ 0 ∧ ∀ (m : ℕ) (x : Fin n → ℤ),
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) ≤ (m : ℚ) → ∀ j : Fin n,
      (A.det.natAbs : ℤ) * x j ^ 2 ≤ 2 * (m : ℤ) * ((A.adjugate j j).natAbs : ℤ) := by
  let M := A.map (Int.castRingHom ℚ)
  have hm : M.IsSymm := hs.map _
  have hpos : M.toQuadraticForm'.PosDef := by
    intro x hx
    have hh := hp x hx
    change 0 < (1 / 2 : ℚ) * M.toQuadraticForm' x at hh
    linarith
  have hd : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.PosDef.of_toQuadraticForm' hm hpos).isUnit).ne_zero
  have hcast : M.det = (A.det : ℚ) := ((Int.castRingHom ℚ).map_det A).symm
  refine ⟨?_, ?_⟩
  · intro hz
    apply hd
    rw [hcast, hz, Int.cast_zero]
  · intro m x hx j
    have hx' : M.toQuadraticForm' (fun i => (x i : ℚ)) ≤ 2 * (m : ℚ) := by
      change (1 / 2 : ℚ) * M.toQuadraticForm' (fun i => (x i : ℚ)) ≤ (m : ℚ) at hx
      linarith
    have hh := (rational_cofactor_bound n M hm hpos (fun i => (x i : ℚ))
      (2 * (m : ℚ)) hx' j).2
    have ha : M.adjugate j j = ((A.adjugate j j : ℤ) : ℚ) := by
      have he := congrArg (fun T : Matrix (Fin n) (Fin n) ℚ => T j j)
        ((Int.castRingHom ℚ).map_adjugate A)
      exact he.symm
    rw [hcast, ha] at hh
    simp only [Int.natCast_natAbs]
    exact_mod_cast hh

theorem computed_radius_complete (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (m : ℕ) (x : Fin n → ℤ)
    (hx : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) ≤ (m : ℚ)) (j : Fin n) :
    -(Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) ≤ x j ∧
      x j ≤ (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) := by
  obtain ⟨hd, hb⟩ := cofactor_square_bound n A hs hp
  have hi := hb m x hx j
  have hi' : (A.det.natAbs : ℤ) * ((x j).natAbs : ℤ) ^ 2 ≤
      2 * (m : ℤ) * ((A.adjugate j j).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs, sq_abs] using hi
  have hnat : A.det.natAbs * (x j).natAbs ^ 2 ≤ 2 * m * (A.adjugate j j).natAbs := by
    exact_mod_cast hi'
  have hdiv : (x j).natAbs ^ 2 ≤ 2 * m * (A.adjugate j j).natAbs / A.det.natAbs := by
    apply (Nat.le_div_iff_mul_le (Int.natAbs_pos.mpr hd)).mpr
    simpa only [mul_comm] using hnat
  have hroot : (x j).natAbs ≤ Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) :=
    Nat.le_sqrt'.mpr hdiv
  have habs : |x j| ≤ (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hroot
  exact abs_le.mp habs

end ArithmeticThetaEnumeration
