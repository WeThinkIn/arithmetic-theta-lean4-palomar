module

public import FieldExtensionNaturalityR0115
public import HalfMillerPrincipalIdealR0114
public import MillerInfinityNormalizationR0114
public import MillerOpenEvaluationR0114
public import ActualMillerPhaseR0114
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! Definitions for geometric local orders and the moved-divisor Miller pairing.
The translation maps are constrained by the actual generic chord formulas.
Existence, local geometric interpretation, finite support and reciprocity are
separate proof obligations; none is a field of an assumed pairing structure. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116

abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e
abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.FF k e
abbrev Translations (k : Type u) [Field k] (e : Fin 3 → k) :=
  (Curve k e).Point → (FF k e ≃ₐ[k] FF k e)

def translatedCoordinates (k : Type u) [Field k] (e : Fin 3 → k) :
    (Curve k e).Point → FF k e × FF k e
  | .zero => (ArithmeticThetaMillerR0114.xFunction k e,
      ArithmeticThetaMillerR0114.yFunction k e)
  | .some a b _ =>
      let x := ArithmeticThetaMillerR0114.xFunction k e
      let y := ArithmeticThetaMillerR0114.yFunction k e
      let c := algebraMap k (FF k e)
      let slope := (y - c b) / (x - c a)
      let newX := slope ^ 2 + c (e 0 + e 1 + e 2) - x - c a
      (newX, -y + slope * (x - newX))

def IsTranslationSystem (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) : Prop :=
  ∀ P, T P (ArithmeticThetaMillerR0114.xFunction k e) =
    (translatedCoordinates k e P).1 ∧
    T P (ArithmeticThetaMillerR0114.yFunction k e) =
    (translatedCoordinates k e P).2

def expansion (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (P : (Curve k e).Point) (f : FF k e) : LaurentSeries k := E (T P f)

def pointOrder (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) : ℤ :=
  (expansion k e T E P f).order

def localLeading (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) : k :=
  (expansion k e T E P f).leadingCoeff

def localValue (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) : k :=
  (expansion k e T E P f).coeff 0

def tameSymbol (k : Type u) [Field k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (P : (Curve k e).Point) : k :=
  (-1 : k) ^ (pointOrder k e T E f P * pointOrder k e T E g P) *
    localLeading k e T E f P ^ pointOrder k e T E g P /
    localLeading k e T E g P ^ pointOrder k e T E f P

def millerAt (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (i : Fin 3) : (Curve k e).Point → FF k e
  | .zero => 1
  | .some x y _ => ArithmeticThetaMillerR0114.millerFunction k e i x y

def GoodShift (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (P Q Z : (Curve k e).Point) : Prop :=
  Z ≠ 0 ∧ Z ≠ P ∧ Q + Z ≠ 0 ∧ Q + Z ≠ P

def movedPairing (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (P Q Z : (Curve k e).Point) : k :=
  localValue k e T E (millerAt k e 0 P) (Q + Z) /
    localValue k e T E (millerAt k e 0 P) Z *
    (localValue k e T E (millerAt k e 1 Q) (-Z) /
      localValue k e T E (millerAt k e 1 Q) (P - Z))

def fixedLabelPhase (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) :
    (Curve k e).Point → (Curve k e).Point → k
  | .some x₁ y₁ _, .some x₂ y₂ _ =>
      ArithmeticThetaMillerR0114.millerRatio k e x₁ y₁ x₂ y₂
  | _, _ => 0

end ArithmeticThetaReciprocityR0116
