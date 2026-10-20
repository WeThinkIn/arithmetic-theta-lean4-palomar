module

public import CyclicCompletedFamilyConstantR0088
public import LaurentScalarGraphR0088
public import RegularFamilyDescentR0067
public import UniformCompletedClearingR0067

@[expose] public section

/-! Laurent constancy from prime-local no-pole hypotheses on the actual cyclic
annular charts. The descent and clearing providers retain the specified maps. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCyclicConstantsR0088

theorem cyclic_no_pole_constant :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
      (f : Fin r → ArithmeticThetaRatioRegularityR0067.FunctionField k),
      ArithmeticThetaRatioRegularityR0067.RationalCompatible k r hr f →
      (∀ (j : Fin r) (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k)),
        P.IsPrime → P.height = 1 →
          ArithmeticThetaLocalOrdersR0066.RegularAt k P (f j)) →
      ∃! c : LaurentSeries k, ∀ j : Fin r, ScalarValue k c (f j) := by
  intro k _ _ r hr f hcompatible hregular
  obtain ⟨v, ⟨hv, hvcompatible⟩, _⟩ :=
    ArithmeticThetaRatioRegularityR0067.regular_family_descent
      k r hr f hcompatible hregular
  obtain ⟨n, a, hclear, hacompatible⟩ :=
    ArithmeticThetaRatioRegularityR0067.uniform_completed_clearing
      k r hr v hvcompatible
  obtain ⟨b, hb, _⟩ := cyclic_completed_family_constant k r hr a hacompatible
  let ι : PowerSeries k →+* LaurentSeries k := algebraMap _ _
  have ht : ι PowerSeries.X ≠ 0 := by
    exact (map_ne_zero_iff ι (IsFractionRing.injective
      (PowerSeries k) (LaurentSeries k))).2 PowerSeries.X_ne_zero
  let c : LaurentSeries k := ι b / (ι PowerSeries.X) ^ n
  have hc : ∀ j : Fin r, ScalarValue k c (f j) := by
    intro j
    refine ⟨n, b, ?_, ?_⟩
    · exact div_mul_cancel₀ (ι b) (pow_ne_zero n ht)
    · have h := congrArg (ArithmeticThetaLocalOrdersR0066.toFunctionField k)
        ((congrArg (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)
          (hb j)).trans (hclear j))
      change scalarBase k b =
        ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (ArithmeticThetaRatioRegularityR0067.parameter k ^ n * v j) at h
      rw [map_mul, map_pow, hv j] at h
      change scalarBase k b = fieldParameter k ^ n * f j at h
      exact (mul_comm (f j) (fieldParameter k ^ n)).trans h.symm
  obtain ⟨F, ⟨_, hgraph⟩, _⟩ := laurent_scalar_graph k
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply F.injective
  exact ((hgraph d (f ⟨0, hr⟩)).mp (hd ⟨0, hr⟩)).trans
    ((hgraph c (f ⟨0, hr⟩)).mp (hc ⟨0, hr⟩)).symm

end ArithmeticThetaCyclicConstantsR0088
