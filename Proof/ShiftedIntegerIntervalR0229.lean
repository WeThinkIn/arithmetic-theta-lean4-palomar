module

public import LDLEnumerationDefinitionsR0229

@[expose] public section

set_option autoImplicit false

namespace ArithmeticThetaLDLEnumerationR0229

private theorem range_image_membership (l u z : ℤ) :
    z ∈ (Finset.range (u - l + 1).toNat).image (fun i : ℕ => l + (i : ℤ)) ↔
      l ≤ z ∧ z ≤ u := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨(z - l).toNat, ?_, ?_⟩ <;> omega

private theorem integer_square_bound (t : ℤ) (S : ℚ) (hS : 0 ≤ S) :
    (t : ℚ)^2 ≤ S ↔
      -(Nat.sqrt ⌊S⌋.toNat : ℤ) ≤ t ∧ t ≤ (Nat.sqrt ⌊S⌋.toNat : ℤ) := by
  have hf : 0 ≤ ⌊S⌋ := Int.floor_nonneg.mpr hS
  have hs : (t : ℚ)^2 ≤ S ↔ t^2 ≤ ⌊S⌋ := by
    rw [Int.le_floor]
    norm_cast
  have hn : t^2 ≤ ⌊S⌋ ↔ t.natAbs^2 ≤ ⌊S⌋.toNat := by
    have he : ((t.natAbs^2 : ℕ) : ℤ) = t^2 := by
      simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    rw [← he, ← Int.toNat_of_nonneg hf]
    exact_mod_cast Iff.rfl
  rw [hs, hn, ← Nat.le_sqrt']
  have ha : t.natAbs ≤ Nat.sqrt ⌊S⌋.toNat ↔
      |t| ≤ (Nat.sqrt ⌊S⌋.toNat : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast Iff.rfl
  exact ha.trans abs_le

private theorem endpoints_iff (c R : ℚ) (z : ℤ) :
    lowerEndpoint c R ≤ z ∧ z ≤ upperEndpoint c R ↔
      -(intervalRadius c R : ℤ) ≤ (c.den : ℤ) * z - c.num ∧
      (c.den : ℤ) * z - c.num ≤ (intervalRadius c R : ℤ) := by
  have hd : (0 : ℚ) < c.den := by exact_mod_cast c.den_pos
  rw [lowerEndpoint, upperEndpoint, Int.ceil_le, Int.le_floor,
    div_le_iff₀ hd, le_div_iff₀ hd]
  have he :
      ((c.num : ℚ) - (intervalRadius c R : ℚ) ≤ (z : ℚ) * c.den ∧
       (z : ℚ) * c.den ≤ (c.num : ℚ) + (intervalRadius c R : ℚ)) ↔
      (-(intervalRadius c R : ℚ) ≤ (c.den : ℚ) * z - c.num ∧
       (c.den : ℚ) * z - c.num ≤ (intervalRadius c R : ℚ)) := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  rw [he]
  norm_cast

theorem shifted_integer_interval :
    ∀ (c R : ℚ) (z : ℤ), z ∈ shiftedInterval c R ↔ ((z : ℚ) - c)^2 ≤ R := by
  intro c R z
  by_cases hR : R < 0
  · simp only [shiftedInterval, if_pos hR, Finset.notMem_empty, false_iff]
    exact not_le.mpr ((sq_nonneg ((z : ℚ) - c)).trans_lt' hR)
  · have hR0 : 0 ≤ R := le_of_not_gt hR
    rw [shiftedInterval, if_neg hR, range_image_membership, endpoints_iff]
    unfold intervalRadius
    rw [← integer_square_bound ((c.den : ℤ) * z - c.num)
      (R * (c.den : ℚ)^2) (mul_nonneg hR0 (sq_nonneg _))]
    have hd : (0 : ℚ) < (c.den : ℚ)^2 := by positivity
    have hc : (c.num : ℚ) = c * c.den := by
      exact (div_eq_iff (by positivity)).mp (Rat.num_div_den c)
    push_cast
    rw [hc]
    have he : ((c.den : ℚ) * z - c * c.den)^2 =
        ((z : ℚ) - c)^2 * (c.den : ℚ)^2 := by ring
    rw [he, mul_le_mul_iff_left₀ hd]

end ArithmeticThetaLDLEnumerationR0229
