module

public import RamifiedMarkedSectionsR0154

@[expose] public section

/-! Correct scalar actions for the ramified-period recovery.
The r0154 definitions remain immutable. Its LaurentDegree predicate is not
used by the new degree obligation. Every rank below binds the actual module.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155

def LaurentDegree (k : Type u) [Field k] (d : ℕ)
    (ell : LaurentSeries k →+* LaurentSeries k) : Prop :=
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := ell.toAlgebra
  letI : Module (LaurentSeries k) (LaurentSeries k) :=
    @Algebra.toModule _ _ _ _ ell.toAlgebra
  FiniteDimensional (LaurentSeries k) (LaurentSeries k) ∧
    Module.finrank (LaurentSeries k) (LaurentSeries k) = d

def FiniteFieldMap {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (α : Y.functionField →+* X.functionField) : Prop :=
  letI : Algebra Y.functionField X.functionField := α.toAlgebra
  letI : Module Y.functionField X.functionField :=
    @Algebra.toModule _ _ _ _ α.toAlgebra
  FiniteDimensional Y.functionField X.functionField

def fieldDegree {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (α : Y.functionField →+* X.functionField) : ℕ :=
  letI : Algebra Y.functionField X.functionField := α.toAlgebra
  letI : Module Y.functionField X.functionField :=
    @Algebra.toModule _ _ _ _ α.toAlgebra
  Module.finrank Y.functionField X.functionField

end ArithmeticThetaRamifiedPeriodR0155
