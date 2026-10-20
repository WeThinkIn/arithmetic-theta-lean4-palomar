module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership

@[expose] public section

/-! Ordinary definitions for the algebraic part of manuscript §§7.2–7.3.
No Tate model, expansion, divisor comparison or Weil pairing is postulated here.
-/
namespace ArithmeticThetaFourTorsion

universe u

/-- The displayed split cubic, in the manuscript's completed-square coordinates. -/
def splitCurve {k : Type u} [CommRing k] (e₁ e₂ e₃ : k) : WeierstrassCurve.Affine k where
  a₁ := 0
  a₂ := -(e₁ + e₂ + e₃)
  a₃ := 0
  a₄ := e₁ * e₂ + e₁ * e₃ + e₂ * e₃
  a₆ := -(e₁ * e₂ * e₃)

/-- The rational expression of the source; nonzero denominators are theorem conclusions. -/
def rootExpression {k : Type u} [Field k] (e₁ e₂ e₃ x y : k) : k :=
  ((x - e₁)^2 - (e₁ - e₂) * (e₁ - e₃)) / (2 * y)

/-- Matrices act on column vectors; marking changes act on ordered bases on the right. -/
abbrev Mat4 := Matrix (Fin 2) (Fin 2) (ZMod 4)

def generatorS : Mat4 := !![0, -1; 1, 0]
def generatorT2 : Mat4 := !![1, 2; 0, 1]

/-- Reduction modulo two, defined on representatives without an unproved interface. -/
def reduceTwo (M : Mat4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => ((M i j).val : ZMod 2)

/-- The actual determinant-one stabilizer of the even quadratic form xy modulo two. -/
def PreservesEven (M : Mat4) : Prop :=
  M.det = 1 ∧ ∀ v : Fin 2 → ZMod 2,
    (Matrix.mulVec (reduceTwo M) v) 0 * (Matrix.mulVec (reduceTwo M) v) 1 = v 0 * v 1

/-- Additive exponent of the character, with S mapped to -1 and T² to zero.
This is a total function on matrices; the character laws are required only on the stabilizer. -/
def characterExponent (M : Mat4) : ZMod 4 :=
  if (M 0 0).val % 2 = 1 then M 0 0 - 1 else M 0 1

end ArithmeticThetaFourTorsion
