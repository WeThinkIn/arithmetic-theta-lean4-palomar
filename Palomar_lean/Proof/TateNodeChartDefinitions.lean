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

/-! Concrete algebraic node charts and their adic completions.
The parameter is the power-series variable over k. The Laurent-polynomial
variable is independent of this parameter. These definitions supply no target
proofs and make no assertion that an affine node is a proper Tate curve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaNodeCharts

variable (k : Type u) [Field k]

abbrev Base := PowerSeries k
def parameter : Base k := PowerSeries.X
abbrev PolynomialChart := MvPolynomial (Fin 2) (Base k)
def relation : PolynomialChart k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (parameter k)
def relationIdeal : Ideal (PolynomialChart k) := Ideal.span {relation k}
abbrev Node := PolynomialChart k ⧸ relationIdeal k
instance (priority := 2000) nodeCommRing : CommRing (Node k) :=
  Ideal.Quotient.commRing (relationIdeal k)
def quotientMap : PolynomialChart k →+* Node k := Ideal.Quotient.mk (relationIdeal k)
def x : Node k := quotientMap k (MvPolynomial.X 0)
def y : Node k := quotientMap k (MvPolynomial.X 1)
def t : Node k := algebraMap (Base k) (Node k) (parameter k)
def nodeIdeal : Ideal (Node k) := Ideal.span {t k}
def polynomialIdeal : Ideal (PolynomialChart k) :=
  Ideal.span {MvPolynomial.C (parameter k)}

/-- Normal-form monomials: all nonnegative powers of x and positive powers of y. -/
def normalMonomial (i : ℤ) : Node k :=
  if 0 ≤ i then x k ^ i.toNat else y k ^ (-i).toNat

abbrev Torus := LaurentPolynomial (Base k)
def torusMap : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.T 1
      else LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1))
def oppositeTorusMap : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then
      LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)
      else LaurentPolynomial.T 1)
abbrev XChart := Localization.Away (x k)
abbrev YChart := Localization.Away (y k)
def toXChart : Node k →+* XChart k := algebraMap (Node k) (XChart k)
def toYChart : Node k →+* YChart k := algebraMap (Node k) (YChart k)

abbrev GenericNode := Localization.Away (t k)
def toGeneric : Node k →+* GenericNode k := algebraMap (Node k) (GenericNode k)
abbrev GenericTorus := LaurentPolynomial (LaurentSeries k)
def genericTorusMap : PolynomialChart k →+* GenericTorus k :=
  MvPolynomial.eval₂Hom
    (LaurentPolynomial.C.comp (algebraMap (Base k) (LaurentSeries k)))
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.T 1
      else LaurentPolynomial.C (algebraMap (Base k) (LaurentSeries k) (parameter k)) *
        LaurentPolynomial.T (-1))

abbrev CompletedNode := AdicCompletion (nodeIdeal k) (Node k)
def toCompleted : Node k →+* CompletedNode k := algebraMap _ _
def completedIdeal : Ideal (CompletedNode k) := Ideal.span {toCompleted k (t k)}
abbrev RestrictedPolynomial := AdicCompletion (polynomialIdeal k) (PolynomialChart k)
def toRestricted : PolynomialChart k →+* RestrictedPolynomial k := algebraMap _ _
def restrictedRelationIdeal : Ideal (RestrictedPolynomial k) :=
  Ideal.span {toRestricted k (relation k)}
abbrev RestrictedNode := RestrictedPolynomial k ⧸ restrictedRelationIdeal k
def restrictedNodeMap : PolynomialChart k →+* RestrictedNode k :=
  (Ideal.Quotient.mk (restrictedRelationIdeal k)).comp (toRestricted k)

end ArithmeticThetaNodeCharts
