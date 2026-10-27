import LocalFRationalCompatibilityR0065
import ChartLaurentSpecializationR0065
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Local divisor objects on the actual completed annular chart after t-inversion.
These definitions contain no assumed orders, residue fields or geometric providers. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066
variable (k : Type u) [Field k] [CharZero k]
abbrev Chart := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev GenericChart := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k

/-- The instance is the accepted domain theorem for this very localization. -/
instance genericDomain : IsDomain (GenericChart k) :=
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by
      have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
        (by omega)).2.2.2.2.1
      simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
        ArithmeticThetaScaledAnnularR0050.tau,
        ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
        ArithmeticThetaScaledTateBridgeR0046.completedParameter,
        ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter] using h))

abbrev FunctionField := FractionRing (GenericChart k)
def toFunctionField : GenericChart k →+* FunctionField k := algebraMap _ _

def sectionEquation (side : Bool) (α : k) : GenericChart k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
    (ArithmeticThetaAnnularTorsionPrereqR0053.sectionEquation k side α)
def sectionIdeal (side : Bool) (α : k) : Ideal (GenericChart k) :=
  Ideal.span {sectionEquation k side α}

/-- Membership in successive powers of the actual local maximal ideal. -/
def ExactOrder (P : Ideal (GenericChart k)) [P.IsPrime]
    (f : GenericChart k) (n : ℕ) : Prop :=
  algebraMap (GenericChart k) (Localization.AtPrime P) f ∈
      (P.map (algebraMap (GenericChart k) (Localization.AtPrime P))) ^ n ∧
  algebraMap (GenericChart k) (Localization.AtPrime P) f ∉
      (P.map (algebraMap (GenericChart k) (Localization.AtPrime P))) ^ (n + 1)

/-- A rational function has order m if an actual numerator/denominator presentation
has this difference of finite local orders. Independence is an obligation. -/
def HasOrder (P : Ideal (GenericChart k)) [P.IsPrime]
    (f : FunctionField k) (m : ℤ) : Prop :=
  ∃ (a b : GenericChart k) (na nb : ℕ), b ≠ 0 ∧
    f * toFunctionField k b = toFunctionField k a ∧
    ExactOrder k P a na ∧ ExactOrder k P b nb ∧ (na : ℤ) - nb = m

/-- Actual membership in the prime-local ring inside its fraction field. -/
def RegularAt (P : Ideal (GenericChart k)) (f : FunctionField k) : Prop :=
  ∃ a b : GenericChart k, b ∉ P ∧ f * toFunctionField k b = toFunctionField k a

def IsIdentityPrime (c j : ℕ) (P : Ideal (GenericChart k)) : Prop :=
  (j = 0 ∧ P = sectionIdeal k true 1) ∨
  (j + 1 = 2*c ∧ P = sectionIdeal k false 1)

def IsTorsionPrime (c j : ℕ) (ζ : k) (P : Ideal (GenericChart k)) : Prop :=
  ∃ (side : Bool) (b : Fin c),
    (if side then 2*c ∣ c*j else 2*c ∣ c*(j+1)) ∧
    P = sectionIdeal k side (ζ ^ b.val)

def numeratorOrder (c j : ℕ) (P : Ideal (GenericChart k)) : ℕ :=
  @ite ℕ (IsIdentityPrime k c j P) (Classical.propDecidable _) (c^2) 0

def denominatorOrder (c j : ℕ) (ζ : k) (P : Ideal (GenericChart k)) : ℕ :=
  @ite ℕ (IsTorsionPrime k c j ζ P) (Classical.propDecidable _) 1 0

def divisorCoefficient (c j : ℕ) (ζ : k) (P : Ideal (GenericChart k)) : ℤ :=
  (numeratorOrder k c j P : ℤ) - denominatorOrder k c j ζ P

def localFunction (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c) : FunctionField k :=
  toFunctionField k (ArithmeticThetaGenericOverlapR0065.numerator k c j ζ hc hcop hζ hj) /
    toFunctionField k (ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj)
end ArithmeticThetaLocalOrdersR0066
