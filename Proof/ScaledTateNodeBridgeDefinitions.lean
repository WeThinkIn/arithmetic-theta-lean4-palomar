module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! Concrete scaled Tate node rings for the source period `Q = X^r`.
Only quotient, localization, Laurent-series, and adic-completion objects are
defined here. Proper polygon gluing, coordinate sections, torsion divisors,
and geometric modular curves remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaScaledTateBridgeR0046

variable (k : Type u) [Field k]
abbrev Base := PowerSeries k

def parameter (r : ℕ) : Base k := PowerSeries.X ^ r
def periodIdeal (r : ℕ) : Ideal (Base k) := Ideal.span {parameter k r}
def periodPower (r n : ℕ) : Ideal (Base k) := (periodIdeal k r) ^ n
abbrev PolynomialChart := MvPolynomial (Fin 2) (Base k)
def relation (r : ℕ) : PolynomialChart k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (parameter k r)
def relationIdeal (r : ℕ) : Ideal (PolynomialChart k) := Ideal.span {relation k r}
abbrev Node (r : ℕ) := PolynomialChart k ⧸ relationIdeal k r
instance (r : ℕ) : CommRing (Node k r) := Ideal.Quotient.commRing (relationIdeal k r)
def quotientMap (r : ℕ) : PolynomialChart k →+* Node k r := Ideal.Quotient.mk (relationIdeal k r)
def x (r : ℕ) : Node k r := quotientMap k r (MvPolynomial.X 0)
def y (r : ℕ) : Node k r := quotientMap k r (MvPolynomial.X 1)
def t (r : ℕ) : Node k r := algebraMap (Base k) (Node k r) (parameter k r)
def nodeIdeal (r : ℕ) : Ideal (Node k r) := Ideal.span {t k r}

abbrev Torus := LaurentPolynomial (Base k)
def torusMap (r : ℕ) : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.T 1
      else LaurentPolynomial.C (parameter k r) * LaurentPolynomial.T (-1))
def oppositeTorusMap (r : ℕ) : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.C (parameter k r) * LaurentPolynomial.T (-1)
      else LaurentPolynomial.T 1)

abbrev GenericNode (r : ℕ) := Localization.Away (t k r)
abbrev GenericTorus := LaurentPolynomial (LaurentSeries k)
def toGeneric (r : ℕ) : Node k r →+* GenericNode k r := algebraMap _ _
def genericTorusMap (r : ℕ) : PolynomialChart k →+* GenericTorus k :=
  MvPolynomial.eval₂Hom
    (LaurentPolynomial.C.comp (algebraMap (Base k) (LaurentSeries k)))
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.T 1
      else LaurentPolynomial.C (algebraMap (Base k) (LaurentSeries k) (parameter k r)) *
        LaurentPolynomial.T (-1))

abbrev CompletedNode (r : ℕ) := AdicCompletion (nodeIdeal k r) (Node k r)
def toCompleted (r : ℕ) : Node k r →+* CompletedNode k r := algebraMap _ _
def completedBaseMap (r : ℕ) : Base k →+* CompletedNode k r :=
  (toCompleted k r).comp (algebraMap (Base k) (Node k r))
def completedParameter (r : ℕ) : CompletedNode k r := toCompleted k r (t k r)
def completedPower (r n : ℕ) : Ideal (CompletedNode k r) :=
  (Ideal.span {completedParameter k r}) ^ n

def LaurentPeriod (r : ℕ) : LaurentSeries k :=
  algebraMap (Base k) (LaurentSeries k) (parameter k r)
def laurentBaseMap : Base k →+* LaurentSeries k := algebraMap (Base k) (LaurentSeries k)
def completedParameterOfBase (r : ℕ) : CompletedNode k r :=
  completedBaseMap k r (parameter k r)
def TatePairing (r : ℕ) (a b : ℤ) : LaurentSeries k :=
  (LaurentPeriod k r) ^ (a * b)

/-- The chart-indexed monomial that occurs in the actual cusp expression `t^j*x`.
This is an ordinary definition; its equality with a specialized power-series
monomial is a separate proof obligation. -/
def chartMonomial (j : ℕ) (a : k) (i d : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ (d * j + i)

/-- The Laurent-series period pairing used by the source after the actual
parameter is embedded in the Laurent-series field. -/
def periodPairing (r : ℕ) (a b : ℤ) : LaurentSeries k :=
  (algebraMap (Base k) (LaurentSeries k) (parameter k r)) ^ (a * b)

end ArithmeticThetaScaledTateBridgeR0046
