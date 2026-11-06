module

public import UnsplitKatoFullExpansionR0158
public import CompletedMarkedChartIdealR0152
public import AnnularThetaGluingDefinitionsR0128
public import LaurentNormDefinitionsR0064
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

/-! Ordinary rational-value and product predicates. These definitions assert no
new regularity, specialization, base-change or Kato-value theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaMarkedKatoValuesR0159
open CategoryTheory AlgebraicGeometry

/-- Regularity and value through the actual stalk and actual rational point. -/
def HasValue (F : Type u) [Field F] (X : Scheme.{u}) [IsIntegral X]
    (p : Spec (CommRingCat.of F) ⟶ X) (g : X.functionField) (v : F) : Prop :=
  ∃ b : X.presheaf.stalk (p (IsLocalRing.closedPoint F)),
    algebraMap (X.presheaf.stalk (p (IsLocalRing.closedPoint F))) X.functionField b = g ∧
    Scheme.stalkClosedPointTo p b = v

/-- Only the generic chart ring is specialized, never its entire fraction field. -/
def IsSpecialization (k : Type) [Field k] [CharZero k] (a : kˣ)
    (σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries k) : Prop :=
  σ.comp (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) =
    (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (ArithmeticThetaAnnularThetaR0128.specialize k a)

/-- The literal f_c evaluated at z=a*t^j, Q=t^r. -/
def literalValue (k : Type) [Field k] (r c j : ℕ) (a : k)
    (g h : LaurentSeries k) : LaurentSeries k :=
  (ArithmeticThetaLaurentNormR0064.t k ^ r) ^ (ArithmeticThetaNormFiniteR0063.K c / 12) *
    (-(HahnSeries.C a * ArithmeticThetaLaurentNormR0064.t k ^ j)) ^
      ArithmeticThetaNormFiniteR0063.p c * g ^ (c^2) / h

/-- The integral shift in z^c=Q^l*z at N-torsion when c=1+12N. -/
def shift (r c j : ℕ) : ℕ := (c-1)*j/r

/-- The K-th power of the Siegel product in integer-exponent algebraic notation.
The root-of-unity coefficient is retained explicitly. -/
def siegelPower (k : Type) [Field k] (r c j : ℕ) (a : k)
    (g : LaurentSeries k) : LaurentSeries k :=
  (-HahnSeries.C a) ^ (ArithmeticThetaNormFiniteR0063.p c + (shift r c j : ℤ)) *
    ArithmeticThetaLaurentNormR0064.t k ^
      ((r : ℤ) * (ArithmeticThetaNormFiniteR0063.K c / 12) +
       (j : ℤ) * ArithmeticThetaNormFiniteR0063.p c +
       (j : ℤ) * (shift r c j : ℤ) +
       (r : ℤ) * ((shift r c j : ℤ) * ((shift r c j : ℤ)-1) / 2)) *
    g ^ (c^2-1)

end ArithmeticThetaMarkedKatoValuesR0159
