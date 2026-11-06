module

public import CorrectedGammaInteriorOverlapR0061
public import CorrectedGammaPeriodBoundaryR0061
public import LocalNormFactorizationR0054
public import LaurentGammaExistenceR0064
public import LocalNormDefinitionsR0054
public import CorrectedGammaDataExistsR0061

@[expose] public section

/-! Actual localizations of the accepted completed coordinate opens.
The predicates below specify extension squares, not desired product identities.
Existence, injectivity and compatibility are separate proof obligations. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaGenericOverlapR0065
variable (k : Type u) [Field k] [CharZero k]

abbrev Chart := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev GenericChart := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k
abbrev OpenHat (j : ℕ) (side : Bool) := ArithmeticThetaIndexedOverlapsR0058.OpenHat k j side

def openParameter (j : ℕ) (side : Bool) : OpenHat k j side :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side
    (ArithmeticThetaIndexedOverlapsR0058.ot k j side)
abbrev GenericOpen (j : ℕ) (side : Bool) := Localization.Away (openParameter k j side)
def includeOpen (j : ℕ) (side : Bool) : OpenHat k j side →+* GenericOpen k j side :=
  algebraMap _ _
def openT (j : ℕ) (side : Bool) : GenericOpen k j side :=
  includeOpen k j side (openParameter k j side)
def openX (j : ℕ) (side : Bool) : GenericOpen k j side :=
  includeOpen k j side (ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side
    (ArithmeticThetaIndexedOverlapsR0058.ox k j side))

def IsGenericRestriction (j : ℕ) (side : Bool)
    (R : GenericChart k →+* GenericOpen k j side) : Prop :=
  R.comp (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) =
    (includeOpen k j side).comp (ArithmeticThetaCorrectedGammaR0061.restrict k j side)

def IsGenericAdjacent (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (E : GenericOpen k j false ≃+*
      GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next r j) true) : Prop :=
  E.toRingHom.comp (includeOpen k j false) =
    (includeOpen k (ArithmeticThetaIndexedOverlapsR0058.next r j) true).comp
      (ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj).toRingHom

/-- Select the already accepted full gamma limit, retaining its horizontal zeros. -/
def correctedGamma (r j : ℕ) (hr : 0 < r) (hj : j < r) : Chart k :=
  Classical.choose (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))

/-- The already accepted local powered-gamma limit for the source's r=2c. -/
def powered (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c) : GenericChart k :=
  ArithmeticThetaLocalNormR0054.poweredLocal k (2*c) c j ζ
    (by omega) hc (by simp) hcop hζ hj

/-- No quotient is taken here: these are the literal source numerator and denominator. -/
def numerator (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c) : GenericChart k :=
  ArithmeticThetaLocalNormR0054.localNumerator k c j ζ hc hcop hζ hj

def denominator (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c) : GenericChart k :=
  ArithmeticThetaLocalNormR0054.localDenominator k c j ζ hc hcop hζ hj

end ArithmeticThetaGenericOverlapR0065
