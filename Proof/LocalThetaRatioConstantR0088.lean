module

public import CyclicNoPoleConstantR0088
public import LaurentScalarGraphR0088

@[expose] public section

/-! A comparison family with the literal theta divisor differs from the literal
local theta products by a unique nonzero Laurent scalar. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCyclicConstantsR0088

open ArithmeticThetaRatioRegularityR0067 ArithmeticThetaLocalOrdersR0066

theorem local_theta_ratio_constant :
    ∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hr : 0 < 2*c) (g : Fin (2*c) → ArithmeticThetaRatioRegularityR0067.FunctionField k),
      RationalCompatible k (2*c) hr g →
      (∀ (j : Fin (2*c)) (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k))
        [P.IsPrime], P.height = 1 →
        HasOrder k P (g j) (divisorCoefficient k c j.val ζ P)) →
      ∃! v : LaurentSeries k, v ≠ 0 ∧ ∀ j : Fin (2*c),
        ScalarValue k v (ratio k (g j) (LocalTheta k c ζ hc hcop hζ j)) := by
  intro k _ _ c ζ hc hcop hζ hr g hg hdiv
  obtain ⟨u, n, a, hu, hcompatible, _, _⟩ :=
    local_comparison_family k c ζ hc hcop hζ hr g hg hdiv
  let f : Fin (2*c) → ArithmeticThetaRatioRegularityR0067.FunctionField k :=
    fun j => toFunctionField k (u j)
  have hfcompatible : RationalCompatible k (2*c) hr f := by
    intro j FY FX E hFY hFX hE
    change E (FY (toFunctionField k (u j))) =
      FX (toFunctionField k (u (nextIndex (2*c) hr j)))
    calc
      _ = E (openToField k j.val false
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (u j))) :=
        congrArg E (RingHom.congr_fun hFY (u j))
      _ = openToField k (nextIndex (2*c) hr j).val true
          (adjacent k (2*c) hr j
            (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (u j))) :=
        RingHom.congr_fun hE _
      _ = openToField k (nextIndex (2*c) hr j).val true
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k
            (nextIndex (2*c) hr j).val true (u (nextIndex (2*c) hr j))) :=
        congrArg (openToField k (nextIndex (2*c) hr j).val true) (hcompatible j)
      _ = _ := (RingHom.congr_fun hFX (u (nextIndex (2*c) hr j))).symm
  have hfregular : ∀ j P, P.IsPrime → P.height = 1 → RegularAt k P (f j) := by
    intro j P hP _
    refine ⟨u j, 1, ?_, ?_⟩
    · exact hP.one_notMem
    · simp [f]
  obtain ⟨v, hv, hunique⟩ := cyclic_no_pole_constant k (2*c) hr f hfcompatible hfregular
  obtain ⟨F, ⟨_, hgraph⟩, _⟩ := laurent_scalar_graph k
  have hvzero : v ≠ 0 := by
    intro hz
    have heq := (hgraph v (f ⟨0, hr⟩)).mp (hv ⟨0, hr⟩)
    have hunit : IsUnit (f ⟨0, hr⟩) :=
      (u ⟨0, hr⟩).isUnit.map (toFunctionField k)
    apply hunit.ne_zero
    rw [← heq, hz, map_zero]
  refine ⟨v, ⟨hvzero, ?_⟩, ?_⟩
  · intro j
    rw [← hu j]
    exact hv j
  · intro w hw
    apply hunique w
    intro j
    change ScalarValue k w (toFunctionField k (u j))
    rw [hu j]
    exact hw.2 j

end ArithmeticThetaCyclicConstantsR0088
