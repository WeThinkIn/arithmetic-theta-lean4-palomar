module

public import HeightOneDVRR0066
public import NumeratorOrdersR0066
public import DenominatorOrdersR0066
public import RationalOrderUniqueR0066

@[expose] public section

/-! The horizontal order of the literal local theta fraction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066

/-- A finite ideal-power order rules out the zero element. -/
lemma exactOrder_ne_zero (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    (a : GenericChart k) (n : ℕ) (h : ExactOrder k P a n) : a ≠ 0 := by
  intro ha
  exact h.2 (by simp [ha])

/-- The literal numerator and denominator provide the required presentation;
the actual height-one DVR makes its order unique. -/
theorem local_f_divisor :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c) (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 →
      HasOrder k P (localFunction k c j ζ hc hcop hζ hj)
        (divisorCoefficient k c j ζ P) ∧
      (∀ m : ℤ, HasOrder k P (localFunction k c j ζ hc hcop hζ hj) m →
        m = divisorCoefficient k c j ζ P) := by
  intro k _ _ c j ζ hc hcop hζ hj P _ hP
  let a := ArithmeticThetaGenericOverlapR0065.numerator k c j ζ hc hcop hζ hj
  let b := ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj
  have ha : ExactOrder k P a (numeratorOrder k c j P) :=
    numerator_orders k c j ζ hc hcop hζ hj P hP
  have hb : ExactOrder k P b (denominatorOrder k c j ζ P) :=
    denominator_orders k c j ζ hc hcop hζ hj P hP
  have hb0 : b ≠ 0 := exactOrder_ne_zero k P b _ hb
  have hbf : toFunctionField k b ≠ 0 := by
    exact fun h => hb0 (IsFractionRing.injective (GenericChart k) (FunctionField k)
      (h.trans (map_zero (toFunctionField k)).symm))
  have horder : HasOrder k P (localFunction k c j ζ hc hcop hζ hj)
      (divisorCoefficient k c j ζ P) := by
    refine ⟨a, b, numeratorOrder k c j P, denominatorOrder k c j ζ P,
      hb0, ?_, ha, hb, rfl⟩
    exact div_mul_cancel₀ (toFunctionField k a) hbf
  refine ⟨horder, ?_⟩
  let : IsDiscreteValuationRing (Localization.AtPrime P) := height_one_dvr k P hP
  intro m hm
  exact rational_order_unique k P _ m _ hm horder

/-- Both endpoint representatives of the identity are torsion representatives. -/
lemma identity_is_torsion (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (ζ : k) (hc : 1 < c) (P : Ideal (GenericChart k))
    (h : IsIdentityPrime k c j P) : IsTorsionPrime k c j ζ P := by
  rcases h with ⟨hj, hP⟩ | ⟨hj, hP⟩
  · refine ⟨true, ⟨0, by omega⟩, ?_, ?_⟩
    · simp [hj]
    · simpa using hP
  · refine ⟨false, ⟨0, by omega⟩, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, hj]
      exact dvd_mul_left _ _
    · simpa using hP

/-- In particular, subtraction retains the identity multiplicity c² - 1. -/
lemma divisorCoefficient_identity (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (ζ : k) (hc : 1 < c) (P : Ideal (GenericChart k))
    (h : IsIdentityPrime k c j P) :
    divisorCoefficient k c j ζ P = (c : ℤ)^2 - 1 := by
  have ht := identity_is_torsion k c j ζ hc P h
  simp [divisorCoefficient, numeratorOrder, denominatorOrder, h, ht]

end ArithmeticThetaLocalOrdersR0066
