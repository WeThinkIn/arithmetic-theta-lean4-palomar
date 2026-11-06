module

public import IndependentHalvesFourBasisR0114
public import ActualMillerPhaseR0114
public import TwoTorsionTranslation
public import LevelFourFiniteCharacter
public import MillerGeometryDefinitionsR0114

@[expose] public section

/-! Ordinary definitions on the actual split-cubic point group. The Miller
phase below is an evaluation ratio, not a definition of the Weil pairing. -/
noncomputable section
universe u v
namespace ArithmeticThetaMarkingR0115

abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e

abbrev Marking (k : Type u) [Field k] (e : Fin 3 → k) :=
  Fin 2 → (Curve k e).Point

def pointX (k : Type u) [Field k] (e : Fin 3 → k) : (Curve k e).Point → k
  | .zero => 0
  | .some x _ _ => x

def pointY (k : Type u) [Field k] (e : Fin 3 → k) : (Curve k e).Point → k
  | .zero => 0
  | .some _ y _ => y

def coordinates (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) (z : Fin 2 → ZMod 4) : (Curve k e).Point :=
  (z 0).val • b 0 + (z 1).val • b 1

def IsBasis (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) : Prop :=
  (∀ i, 4 • b i = 0) ∧ Function.Injective (coordinates k e b) ∧
    ∀ T : (Curve k e).Point, 4 • T = 0 → ∃ z, coordinates k e b z = T

def act (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) (M : ArithmeticThetaFourTorsion.Mat4) : Marking k e :=
  fun j => (M 0 j).val • b 0 + (M 1 j).val • b 1

def labels (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) : Fin 3 → k :=
  ![pointX k e (2 • b 0), pointX k e (2 • b 1),
    pointX k e (2 • b 0 + 2 • b 1)]

def root (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) : k :=
  ArithmeticThetaFourTorsion.rootExpression
    (labels k e b 0) (labels k e b 1) (labels k e b 2)
    (pointX k e (b 1)) (pointY k e (b 1))

def tangent (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (P Q : (Curve k e).Point) : k :=
  ArithmeticThetaMillerR0114.tangentValue k e
    (pointX k e P) (pointY k e P) (pointX k e Q) (pointY k e Q)

def phase (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (b : Marking k e) : k :=
  ((tangent k e (b 0) (b 1)) ^ 2 /
    (pointX k e (b 1) - labels k e b 0)) /
  ((tangent k e (b 1) (b 0)) ^ 2 /
    (pointX k e (b 0) - labels k e b 1))

def IsCoordinateMap (k : Type u) (K : Type v) [Field k] [Field K]
    [DecidableEq k] [DecidableEq K] (e : Fin 3 → k) (f : k →+* K)
    (F : (Curve k e).Point →+ (Curve K (f ∘ e)).Point) : Prop :=
  ∀ P : (Curve k e).Point, P ≠ 0 →
    F P ≠ 0 ∧ pointX K (f ∘ e) (F P) = f (pointX k e P) ∧
      pointY K (f ∘ e) (F P) = f (pointY k e P)

def changedLabels (k : Type u) [Field k] (e : Fin 3 → k) (a : kˣ) (r : k) :
    Fin 3 → k := fun i => (a : k)^2 * e i + r

def IsCoordinateChange (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (a : kˣ) (r : k)
    (F : (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point) : Prop :=
  ∀ P : (Curve k e).Point, P ≠ 0 →
    pointX k (changedLabels k e a r) (F P) = (a : k)^2 * pointX k e P + r ∧
    pointY k (changedLabels k e a r) (F P) = (a : k)^3 * pointY k e P

end ArithmeticThetaMarkingR0115
