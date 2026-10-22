module

public import SchemeDiscriminantTateR0245
public import UnmarkedTateDiscriminantR0245
public import RamifiedLaurentExtensionR0155
public import LegendreNormalFormR0177
public import RelativeAlphaNaturalityR0190
public import ArbitraryDiscriminantDefinitionsR0243
public import GlobalFourTorsionDefinitionsR0190

@[expose] public section

/-! Coefficient extraction defines a concrete period-one cubic. Its descent,
ellipticity, coordinate comparison, normalized frame and discriminant equation
are separate proof obligations. No period-one model or expansion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaPeriodOneR0246
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential

variable (k : Type) [Field k] [CharZero k]

/-- The actual symmetric coefficients of the accepted Q=t^4 cubic. -/
def ramifiedCoefficient (j : Fin 3) : PowerSeries k :=
  let e := ArithmeticThetaCubicModelR0144.rootSeries k 4
  if j.val = 0 then -(e 0 + e 1 + e 2)
  else if j.val = 1 then e 0 * e 1 + e 0 * e 2 + e 1 * e 2
  else -(e 0 * e 1 * e 2)

/-- Extract the coefficient of t^(4n); this is not assumed to invert expansion. -/
def coefficient (j : Fin 3) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff (4*n) (ramifiedCoefficient k j)

/-- A concrete Weierstrass equation over k((Q)), with Q the formal variable. -/
def periodOneCurve : WeierstrassCurve (LaurentSeries k) where
  a₁ := 0
  a₂ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 0)
  a₃ := 0
  a₄ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 1)
  a₆ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 2)

abbrev PeriodCurve := Curve (LaurentSeries k) (periodOneCurve k)
abbrev PeriodFrame :=
  ArithmeticThetaGlobalFourTorsionR0190.CurveFrame (LaurentSeries k) (periodOneCurve k)

abbrev affineInclusion :=
  ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) (periodOneCurve k)

/-- Reuse the accepted normalization dx=(2y+a1*x+a3)delta; here a1=a3=0. -/
abbrev Normalized (δ : PeriodFrame k) : Prop :=
  ArithmeticThetaGlobalFourTorsionR0190.NormalizedFrame (LaurentSeries k) (periodOneCurve k) δ

abbrev generator (δ : PeriodFrame k) :=
  ArithmeticThetaGlobalFourTorsionR0190.hodgeGenerator (LaurentSeries k) (periodOneCurve k) δ

abbrev PeriodSections :=
  (HodgePower (LaurentSeries k) (periodOneCurve k) 24).presheaf.obj (Opposite.op ⊤)

def IsD2 (d : PeriodSections k) : Prop :=
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (periodOneCurve k) d

def FullExpansion (δ : PeriodFrame k) (d : PeriodSections k) : Prop :=
  d = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
    (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 1) •
      ArithmeticThetaTensorPower.tensorPowerSection
        (ArithmeticThetaRelativeDiscriminantR0171.Base (LaurentSeries k))
        (Hodge (LaurentSeries k) (periodOneCurve k)) 24 ⊤ (generator k δ)

/-- Actual pointed Cartesian coefficient comparison, constrained on x and y.
No differential or discriminant equation is part of this data. -/
structure CoordinateComparison (ell : LaurentSeries k →+* LaurentSeries k) extends
    ArithmeticThetaArbitraryDiscriminantR0243.Comparison
      (LaurentSeries k) (LaurentSeries k) (periodOneCurve k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k 4) ell where
  chartMap : ArithmeticThetaLegendreComparisonR0177.ChartRing
      (LaurentSeries k) (periodOneCurve k) →+*
    ArithmeticThetaLegendreComparisonR0177.ChartRing
      (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k 4)
  chart_eq : Spec.map (CommRingCat.ofHom chartMap) ≫ affineInclusion k =
    ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k 4) ≫ map
  x_eq : chartMap (WeierstrassCurve.DrinfeldGlobal.xOverZ (periodOneCurve k).toProjective) =
    WeierstrassCurve.DrinfeldGlobal.xOverZ (ArithmeticThetaTateCuspsR0181.TateCurve k 4).toProjective
  y_eq : chartMap (WeierstrassCurve.DrinfeldGlobal.yOverZ (periodOneCurve k).toProjective) =
    WeierstrassCurve.DrinfeldGlobal.yOverZ (ArithmeticThetaTateCuspsR0181.TateCurve k 4).toProjective

/-- Pullback uses the conormal derivative of this exact pointed curve map. -/
def pulledGenerator [hE : (periodOneCurve k).IsElliptic]
    {ell : LaurentSeries k →+* LaurentSeries k} (C : CoordinateComparison k ell)
    (δ : PeriodFrame k) :
    (Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k 4)).presheaf.obj
      (Opposite.op ⊤) :=
  res _ (by simp)
    ((ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C.toComparison).hom.app _
      (Scheme.Modules.pullbackLocalSection
        (Spec.map (CommRingCat.ofHom ell)) (generator k δ)))

end ArithmeticThetaPeriodOneR0246
