import PeriodOneDiscriminantR0246

/-! A period-one Tate equation over every rational coefficient ring, with the
actual coordinate, differential, conormal and scheme-test maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaRationalTateR0247
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171

/-- Coefficientwise map; no fraction-field or reducedness hypothesis is used. -/
def seriesMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

variable (R : Type) [CommRing R] [Algebra ℚ R]

def rationalMap : LaurentSeries ℚ →+* LaurentSeries R := seriesMap (algebraMap ℚ R)

def equation : WeierstrassCurve (LaurentSeries R) :=
  (ArithmeticThetaPeriodOneR0246.periodOneCurve ℚ).map (rationalMap R)

abbrev Frame := ArithmeticThetaGlobalFourTorsionR0190.CurveFrame (LaurentSeries R) (equation R)
abbrev Normalized (δ : Frame R) :=
  ArithmeticThetaGlobalFourTorsionR0190.NormalizedFrame (LaurentSeries R) (equation R) δ
abbrev generator (δ : Frame R) :=
  ArithmeticThetaGlobalFourTorsionR0190.hodgeGenerator (LaurentSeries R) (equation R) δ
abbrev Sections := (HodgePower (LaurentSeries R) (equation R) 24).presheaf.obj (Opposite.op ⊤)

/-- The entire rational Euler product, coefficientwise over R, at period one. -/
def productSeries : LaurentSeries R :=
  HahnSeries.ofPowerSeries ℤ R (PowerSeries.map (algebraMap ℚ R)
    (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48))

def IsD2 (d : Sections R) : Prop :=
  ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (equation R) d

def FullExpansion (δ : Frame R) (d : Sections R) : Prop :=
  d = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries R) (productSeries R) •
    ArithmeticThetaTensorPower.tensorPowerSection (Base (LaurentSeries R))
      (Hodge (LaurentSeries R) (equation R)) 24 ⊤ (generator R δ)

/-- Coordinate-preserving pointed Cartesian maps; no differential equation is
assumed. The coefficient equation is part of the specified base change. -/
structure CoordinateComparison (A B : Type) [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B) (ι : A →+* B) extends
    ArithmeticThetaArbitraryDiscriminantR0243.Comparison A B W V ι where
  coefficients : W.map ι = V
  chartMap : ArithmeticThetaLegendreComparisonR0177.ChartRing A W →+*
    ArithmeticThetaLegendreComparisonR0177.ChartRing B V
  chart_eq : Spec.map (CommRingCat.ofHom chartMap) ≫
    ArithmeticThetaLegendreComparisonR0177.chartInclusion A W =
    ArithmeticThetaLegendreComparisonR0177.chartInclusion B V ≫ map
  x_eq : chartMap (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
    WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective
  y_eq : chartMap (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
    WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective

def pulledGenerator {A B : Type} [CommRing A] [CommRing B]
    {W : WeierstrassCurve A} [W.IsElliptic] {V : WeierstrassCurve B}
    {ι : A →+* B} (C : CoordinateComparison A B W V ι)
    (δ : ArithmeticThetaGlobalFourTorsionR0190.CurveFrame A W) :
    (Hodge B V).presheaf.obj (Opposite.op ⊤) :=
  res _ (by simp)
    ((ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C.toComparison).hom.app _
      (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι))
        (ArithmeticThetaGlobalFourTorsionR0190.hodgeGenerator A W δ)))

/-- Every test is an actual pointed Cartesian Tate family over R((Q)). R may
have nilpotents or zero divisors. No discriminant or expansion is assumed. -/
structure TateTest {S : Scheme} (σ : S ⟶ Base ℚ)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S) where
  elliptic : (equation R).IsElliptic
  law : Law (LaurentSeries R) (equation R)
  originLaw : IsOriginLaw (LaurentSeries R) (equation R) law
  base : Base (LaurentSeries R) ⟶ S
  base_eq : base ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (LaurentSeries R)))
  comparison : ArithmeticThetaSchemeDiscriminantR0244.Comparison E
    (@ArithmeticThetaSchemeDiscriminantR0244.weierstrassFamily (LaurentSeries R)
      inferInstance (equation R) elliptic law originLaw) base
  differential : Frame R
  normalized : Normalized R differential

def value {S : Scheme} {σ : S ⟶ Base ℚ}
    {E : ArithmeticThetaLocalWeierstrassR0203.Family S}
    (V : TateTest R σ E) (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) : Sections R :=
  letI := V.elliptic
  ArithmeticThetaSchemeDiscriminantR0244.weierstrassValue (LaurentSeries R)
    (equation R) V.law V.originLaw (ArithmeticThetaSchemeDiscriminantR0244.pull V.comparison d)

def HasTateExpansions {S : Scheme} (σ : S ⟶ Base ℚ)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℚ A] (V : TateTest A σ E),
    FullExpansion A V.differential (value A V d)

end ArithmeticThetaRationalTateR0247
