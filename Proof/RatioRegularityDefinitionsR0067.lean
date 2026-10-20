module

public import LocalFDivisorR0066
public import NormalDomainIntersection

@[expose] public section

/-! Local comparison objects on the accepted completed annular charts.
No proper model or algebraic theta unit is postulated here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067
variable (k : Type u) [Field k] [CharZero k]
abbrev Chart := ArithmeticThetaLocalOrdersR0066.Chart k
abbrev GenericChart := ArithmeticThetaLocalOrdersR0066.GenericChart k
abbrev FunctionField := ArithmeticThetaLocalOrdersR0066.FunctionField k
abbrev GenericOpen (j : ℕ) (side : Bool) := ArithmeticThetaGenericOverlapR0065.GenericOpen k j side
instance openDomain (j : ℕ) (side : Bool) : IsDomain (GenericOpen k j side) :=
  (ArithmeticThetaGenericOverlapR0065.generic_open_faithfulness k j side).1
abbrev OpenField (j : ℕ) (side : Bool) := FractionRing (GenericOpen k j side)
def openToField (j : ℕ) (side : Bool) : GenericOpen k j side →+* OpenField k j side := algebraMap _ _
def IsFractionRestriction (j : ℕ) (side : Bool)
    (F : FunctionField k →+* OpenField k j side) : Prop :=
  F.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k) =
    (openToField k j side).comp (ArithmeticThetaGenericOverlapR0065.genericRestriction k j side)
def nextIndex (r : ℕ) (hr : 0 < r) (j : Fin r) : Fin r :=
  ⟨ArithmeticThetaIndexedOverlapsR0058.next r j.val, Nat.mod_lt _ hr⟩
def adjacent (r : ℕ) (hr : 0 < r) (j : Fin r) :
    GenericOpen k j.val false ≃+* GenericOpen k (nextIndex r hr j).val true :=
  Classical.choose (ArithmeticThetaGenericOverlapR0065.generic_adjacent_providers k r j.val hr j.isLt)
def IsFractionAdjacent (r : ℕ) (hr : 0 < r) (j : Fin r)
    (E : OpenField k j.val false ≃+* OpenField k (nextIndex r hr j).val true) : Prop :=
  E.toRingHom.comp (openToField k j.val false) =
    (openToField k (nextIndex r hr j).val true).comp (adjacent k r hr j).toRingHom
/-- Rational agreement through the fraction-field extensions of the real overlap maps.
Existence and uniqueness of all quantified extensions are separate obligations. -/
def RationalCompatible (r : ℕ) (hr : 0 < r) (f : Fin r → FunctionField k) : Prop :=
  ∀ (j : Fin r)
    (FY : FunctionField k →+* OpenField k j.val false)
    (FX : FunctionField k →+* OpenField k (nextIndex r hr j).val true)
    (E : OpenField k j.val false ≃+* OpenField k (nextIndex r hr j).val true),
    IsFractionRestriction k j.val false FY →
    IsFractionRestriction k (nextIndex r hr j).val true FX →
    IsFractionAdjacent k r hr j E → E (FY (f j)) = FX (f (nextIndex r hr j))
def RegularCompatible (r : ℕ) (hr : 0 < r) (f : Fin r → GenericChart k) : Prop :=
  ∀ j : Fin r,
    adjacent k r hr j (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (f j)) =
      ArithmeticThetaGenericOverlapR0065.genericRestriction k (nextIndex r hr j).val true
        (f (nextIndex r hr j))
def CompletedCompatible (r : ℕ) (hr : 0 < r) (a : Fin r → Chart k) : Prop :=
  ∀ j : Fin r,
    ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
      (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j)) =
    ArithmeticThetaCorrectedGammaR0061.restrict k (nextIndex r hr j).val true
      (a (nextIndex r hr j))
def parameter : GenericChart k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)
def LocalTheta (c : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (j : Fin (2*c)) : FunctionField k :=
  ArithmeticThetaLocalOrdersR0066.localFunction k c j.val ζ hc hcop hζ j.isLt
end ArithmeticThetaRatioRegularityR0067
