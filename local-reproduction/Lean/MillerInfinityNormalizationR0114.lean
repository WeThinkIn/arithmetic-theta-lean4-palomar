import InfinityFunctionFieldR0114

/-! Full Laurent normalization of the actual Miller function. -/
noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
open WeierstrassCurve.Affine

private lemma tangent_function (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (x y : k) :
    algebraMap (Coord k e) (FF k e) (tangentClass k e x y) =
      yFunction k e - algebraMap k (FF k e) (tangentSlope k e x y) *
        (xFunction k e - algebraMap k (FF k e) x) - algebraMap k (FF k e) y := by
  simp only [tangentClass, yFunction, xFunction, CoordinateRing.YClass,
    CoordinateRing.XClass, linePolynomial, map_zero, sub_zero,
    map_add, map_sub, map_mul]
  rw [sub_add_eq_sub_sub]
  rfl

theorem miller_infinity_normalization :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Distinct k e → ∀ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
        branchEquation k e h → IsInfinityEmbedding k e h E →
        ∀ (i : Fin 3) (x y : k), IsHalf k e i x y →
          ∃ s : PowerSeries k, PowerSeries.constantCoeff s = 1 ∧
            E (millerFunction k e i x y) = parameter k ^ (-4 : ℤ) *
              algebraMap (PowerSeries k) (LaurentSeries k) s := by
  intro k _ _ _ e _ h E hh hE i x y _
  let m := tangentSlope k e x y
  let A : PowerSeries k := -h - PowerSeries.C m * PowerSeries.X * h +
    PowerSeries.C (m * x - y) * PowerSeries.X ^ 3
  let B : PowerSeries k := h - PowerSeries.C (e i) * PowerSeries.X ^ 2
  have hB : PowerSeries.constantCoeff B = 1 := by simp [B, hh.1]
  have hA : PowerSeries.constantCoeff A = -1 := by simp [A, hh.1]
  let L := algebraMap (PowerSeries k) (LaurentSeries k)
  have hBinv : L (B⁻¹) = (L B)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, PowerSeries.inv_mul_cancel B (by simp [hB]), map_one]
  have hBne : L B ≠ 0 := by
    have hu : L B * L (B⁻¹) = 1 := by
      rw [← map_mul, PowerSeries.mul_inv_cancel B (by simp [hB]), map_one]
    exact left_ne_zero_of_mul_eq_one hu
  refine ⟨A ^ 2 * B⁻¹, ?_, ?_⟩
  · simp [map_mul, map_pow, PowerSeries.constantCoeff_inv, hA, hB]
  have hc (a : k) : L (PowerSeries.C a) = algebraMap k (LaurentSeries k) a := rfl
  have hz : parameter k ≠ 0 := parameter_ne_zero k
  have htan : E (algebraMap (Coord k e) (FF k e) (tangentClass k e x y)) =
      parameter k ^ (-3 : ℤ) * L A := by
    rw [tangent_function, map_sub, map_sub, map_mul, map_sub,
      E.commutes, E.commutes, E.commutes, hE.1, hE.2]
    simp only [A, map_add, map_sub, map_neg, map_mul, map_pow, hc,
      infinityX, infinityY, zpow_neg, zpow_ofNat]
    change -((parameter k ^ 3)⁻¹ * L h) - algebraMap k (LaurentSeries k) m *
      ((parameter k ^ 2)⁻¹ * L h - algebraMap k (LaurentSeries k) x) -
      algebraMap k (LaurentSeries k) y = _
    change _ = (parameter k ^ 3)⁻¹ * (-L h - algebraMap k (LaurentSeries k) m *
      parameter k * L h + (algebraMap k (LaurentSeries k) m *
      algebraMap k (LaurentSeries k) x - algebraMap k (LaurentSeries k) y) * parameter k ^ 3)
    field_simp
    ring
  have hden : E (xFunction k e - algebraMap k (FF k e) (e i)) =
      parameter k ^ (-2 : ℤ) * L B := by
    rw [map_sub, E.commutes, hE.1]
    simp only [B, map_sub, map_mul, map_pow, hc, infinityX, zpow_neg, zpow_ofNat]
    change (parameter k ^ 2)⁻¹ * L h - algebraMap k (LaurentSeries k) (e i) =
      (parameter k ^ 2)⁻¹ * (L h - algebraMap k (LaurentSeries k) (e i) * parameter k ^ 2)
    field_simp
  rw [millerFunction, map_div₀, map_pow, htan, hden, map_mul, map_pow]
  change _ = parameter k ^ (-4 : ℤ) * (L A ^ 2 * L (B⁻¹))
  rw [hBinv]
  simp only [zpow_neg, zpow_ofNat]
  field_simp

/-- The branch and embedding providers instantiate the normalization theorem. -/
lemma exists_normalized_miller (k : Type u) [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (he : Distinct k e) (i : Fin 3) (x y : k)
    (hhalf : IsHalf k e i x y) :
    ∃ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k) (s : PowerSeries k),
      branchEquation k e h ∧ IsInfinityEmbedding k e h E ∧
      Function.Injective E ∧ PowerSeries.constantCoeff s = 1 ∧
      E (millerFunction k e i x y) = parameter k ^ (-4 : ℤ) *
        algebraMap (PowerSeries k) (LaurentSeries k) s := by
  obtain ⟨h, E, hh, hE, hinj⟩ := exists_infinity_embedding k e he
  obtain ⟨s, hs, hf⟩ := miller_infinity_normalization k e he h E hh hE i x y hhalf
  exact ⟨h, E, s, hh, hE, hinj, hs, hf⟩

end ArithmeticThetaMillerR0114
