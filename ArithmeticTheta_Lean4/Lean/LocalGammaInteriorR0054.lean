import LocalNormDefinitionsR0054

/-! Interior charts have no unpowered horizontal gamma factor. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

theorem gamma_interior_units :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (hc : 1 < c)
      (hj0 : 0 < j) (hj : j+1 < 2*c),
      ArithmeticThetaLocalNormR0054.gammaHorizontal k (2*c) j = 1 ∧
        IsUnit (ArithmeticThetaLocalNormR0054.gammaLocal k (2*c) j
          (by omega) (by omega)) := by
  intro k _ _ c j hc hj0 hj
  have hhorizontal : gammaHorizontal k (2*c) j = 1 := by
    simp [gammaHorizontal, ArithmeticThetaScaledAnnularR0050.gammaHorizontal,
      Nat.ne_of_gt hj0, Nat.ne_of_lt hj]
  refine ⟨hhorizontal, ?_⟩
  have hunit : IsUnit (gammaUnit k (2*c) j (by omega) (by omega)) :=
    (Classical.choose_spec (ArithmeticThetaScaledAnnularR0050.gamma_unit_product
      k 1 (2*c) j (by omega) (by omega))).1.1
  simpa only [gammaLocal, hhorizontal, one_mul] using
    hunit.map (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)

end ArithmeticThetaLocalNormR0054
