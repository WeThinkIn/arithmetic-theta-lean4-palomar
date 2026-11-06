module

public import FourTorsionRoot
public import MillerPhaseAlgebra
public import TwoTorsionTranslation
public import LevelFourFiniteCharacter
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import FourTorsionDefinitions
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

@[expose] public section

/-! Actual split-cubic coordinates, tangent functions, fractional ideals and
the branch at infinity used to normalize the four-torsion Miller functions.
These are definitions only. No pairing or divisor identity is assumed. -/
noncomputable section
universe u
namespace ArithmeticThetaMillerR0114

abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaFourTorsion.splitCurve (e 0) (e 1) (e 2)

abbrev Coord (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  (Curve k e).CoordinateRing

abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  (Curve k e).FunctionField

def Distinct (k : Type u) (e : Fin 3 → k) : Prop := Function.Injective e

def IsHalf (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (i : Fin 3) (x y : k) : Prop :=
  ∃ (hR : (Curve k e).Nonsingular x y) (hP : (Curve k e).Nonsingular (e i) 0),
    2 • WeierstrassCurve.Affine.Point.some x y hR =
      WeierstrassCurve.Affine.Point.some (e i) 0 hP

def IsHalfPoint (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (i : Fin 3) (P : (Curve k e).Point) : Prop :=
  ∃ hP : (Curve k e).Nonsingular (e i) 0,
    2 • P = WeierstrassCurve.Affine.Point.some (e i) 0 hP

def tangentSlope (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (x y : k) : k := (Curve k e).slope x x y y

def tangentValue (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (x y a b : k) : k :=
  b - y - tangentSlope k e x y * (a - x)

def tangentClass (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (x y : k) : Coord k e :=
  WeierstrassCurve.Affine.CoordinateRing.YClass (Curve k e)
    (WeierstrassCurve.Affine.linePolynomial x y (tangentSlope k e x y))

def pointIdeal (k : Type u) [Field k] (e : Fin 3 → k) (x y : k) : Ideal (Coord k e) :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal (Curve k e) x (Polynomial.C y)

def pointFraction (k : Type u) [Field k] (e : Fin 3 → k) (x y : k) :
    FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e) :=
  (pointIdeal k e x y : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))

def xFunction (k : Type u) [Field k] (e : Fin 3 → k) : FF k e :=
  algebraMap (Coord k e) (FF k e)
    (WeierstrassCurve.Affine.CoordinateRing.XClass (Curve k e) 0)

def yFunction (k : Type u) [Field k] (e : Fin 3 → k) : FF k e :=
  algebraMap (Coord k e) (FF k e)
    (WeierstrassCurve.Affine.CoordinateRing.YClass (Curve k e) 0)

def millerFunction (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (i : Fin 3) (x y : k) : FF k e :=
  (algebraMap (Coord k e) (FF k e) (tangentClass k e x y)) ^ 2 /
    (xFunction k e - algebraMap k (FF k e) (e i))

def millerValue (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (i : Fin 3) (x y a b : k) : k :=
  (tangentValue k e x y a b) ^ 2 / (a - e i)

abbrev MillerOpen (k : Type u) [Field k] (e : Fin 3 → k) (i : Fin 3) :=
  Localization.Away (WeierstrassCurve.Affine.CoordinateRing.XClass (Curve k e) (e i))

def localMiller (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (i : Fin 3) (x y : k) : MillerOpen k e i :=
  (algebraMap (Coord k e) (MillerOpen k e i) (tangentClass k e x y)) ^ 2 *
    IsLocalization.Away.invSelf
      (WeierstrassCurve.Affine.CoordinateRing.XClass (Curve k e) (e i))

def millerRatio (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (x₁ y₁ x₂ y₂ : k) : k :=
  millerValue k e 0 x₁ y₁ x₂ y₂ / millerValue k e 1 x₂ y₂ x₁ y₁

def branchEquation (k : Type u) [Field k] (e : Fin 3 → k) (h : PowerSeries k) : Prop :=
  PowerSeries.constantCoeff h = 1 ∧
    h ^ 2 = ∏ i : Fin 3, (h - PowerSeries.C (e i) * PowerSeries.X ^ 2)

def parameter (k : Type u) [Field k] : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X

def infinityX (k : Type u) [Field k] (h : PowerSeries k) : LaurentSeries k :=
  parameter k ^ (-2 : ℤ) * algebraMap (PowerSeries k) (LaurentSeries k) h

def infinityY (k : Type u) [Field k] (h : PowerSeries k) : LaurentSeries k :=
  -(parameter k ^ (-3 : ℤ) * algebraMap (PowerSeries k) (LaurentSeries k) h)

def IsInfinityEmbedding (k : Type u) [Field k] (e : Fin 3 → k)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k) : Prop :=
  E (xFunction k e) = infinityX k h ∧ E (yFunction k e) = infinityY k h

end ArithmeticThetaMillerR0114
