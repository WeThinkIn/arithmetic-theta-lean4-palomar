import CompactAlphaCanonicalHalfLineR0192
import DiskFrameComparisonAdapterR0192
import SquareIsometryInterfaceAdapterR0192

/-! Isogeny-normalized alpha on the actual source family and its compact half-line.
Only ordinary definitions occur here. All existence and expansion claims are targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaIsogenyHalfLinesR0193
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaNormalizedSections ArithmeticThetaSectionOrder ArithmeticThetaLineRoot

/-- The relative alpha is tested against the SAME full-four marking and the
canonical pointed differential comparison on every actual Weierstrass test. -/
def IsFamilyAlpha (S : Type) [CommRing S] (E : EllipticFamily S)
    (M : FamilyLevel S E 4) (a : Γ(hodge E, ⊤)) : Prop :=
  IsFrame (hodge E) ⊤ a ∧
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W), IsOriginLaw R W G →
    ∀ (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
      (B : FullLevel R W G 4 (𝟙 (Base R))),
      B.x.val ≫ C.map = baseMap S R C.scalar ≫ M.x.val →
      B.y.val ≫ C.map = baseMap S R C.scalar ≫ M.y.val →
      ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 B
        ((comparison C).hom.app ⊤ (pullbackGlobalSection (baseMap S R C.scalar) (hodge E) a))

variable (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : LevelData k L)

abbrev SourceFamily := D.atlas.descent.family
abbrev CyclicQuotient := Quotient D.atlas.quotient.ring (SourceFamily k L D) m
  (kernelPoint k L D.atlas m)

/-- Both labels are forced to be the prescribed images of the original full
level; the target is never an independently selected elliptic curve. -/
def TargetMarking (Q : CyclicQuotient k L m D)
    (M : FamilyLevel D.atlas.quotient.ring Q.target 4) : Prop :=
  M.x.val = liftPoint k L D.atlas m 4 0 1 ≫ Q.arrow.map ∧
  M.y.val = liftPoint k L D.atlas m 4 1 0 ≫ Q.arrow.map

/-- Data to be constructed from a level family. No compact section, cusp order,
Tate identity or half-divisor is supplied in this structure. -/
structure OpenAlpha where
  quotient : CyclicQuotient k L m D
  marking : FamilyLevel D.atlas.quotient.ring quotient.target 4
  marked : TargetMarking k L m D quotient marking
  alpha : Γ(hodge quotient.target, ⊤)
  intrinsic : IsFamilyAlpha D.atlas.quotient.ring quotient.target marking alpha

def ambientAlpha (A : OpenAlpha k L m D) : Γ(hodge (SourceFamily k L D), ⊤) :=
  scalar D.atlas.quotient.ring (algebraMap k D.atlas.quotient.ring (m : k)⁻¹) •
    (familyHodgeMap A.quotient.arrow).app ⊤ A.alpha

def openAlpha (A : OpenAlpha k L m D) : Γ(openHodge k L D, ⊤) :=
  pullbackGlobalSection D.quotient.inclusion (hodge (SourceFamily k L D)) (ambientAlpha k L m D A)

def testAlpha (A : OpenAlpha k L m D) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    Γ(Hodge (LaurentSeries k) (TateCurve k L), ⊤) :=
  (testIso k L V).hom.app ⊤ (pullbackGlobalSection (V.base ≫ D.quotient.inclusion)
    (hodge (SourceFamily k L D)) (ambientAlpha k L m D A))

/-- The actual cyclic kernel generator in the source Tate chart. -/
def testKernel (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k L) :=
  (V.level.law.nsmul (𝟙 _) (L/m) V.level.marking.x).val

def KernelCoordinates (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (i : Fin L) (z : kˣ) : Prop :=
  (i.val ≠ 0 ∨ (z : k) ≠ 1) ∧
  ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k L)
    (testKernel k L m D V)
    (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L i.val z))
    (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L i.val z))

/-- d is the order of the actual component label; e=m/d is the toric degree.
The equation 4*m*j=L*e^2 retains the exact source order without rounded division. -/
def AllowedOrder (i : Fin L) (j : ℕ) : Prop :=
  let d := L / Nat.gcd L i.val
  let e := m / d
  0 < d ∧ d ∣ m ∧ 0 < e ∧ e*d = m ∧ Even j ∧
    (j = 0 ∨ 4*m*j = L*e^2)

def AllCuspOrders (A : OpenAlpha k L m D) : Prop :=
  ∀ V : ArithmeticThetaBoundaryHodgeR0182.Test k L D,
    ∃ (i : Fin L) (z : kˣ) (j : ℕ) (v : (PowerSeries k)ˣ),
      KernelCoordinates k L m D V i z ∧ AllowedOrder L m i j ∧
      testAlpha k L m D A V =
        scalar (LaurentSeries k)
          (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential

def DesignatedExpansion (A : OpenAlpha k L m D) : Prop :=
  ∀ (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k),
    IsPrimitiveRoot ζ L → CanonicalMarking k L ζ V.level →
      testAlpha k L m D A V =
        scalar (LaurentSeries k)
          (algebraMap (PowerSeries k) (LaurentSeries k)
            (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m) ^ 2)) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential

variable (X : Compactification k L D) (H : Extension k L D X)

/-- The compact section restricts to the actual normalized isogeny pullback.
Both every-cusp orders and the complete designated series remain in its type. -/
def CompactRealizes (A : OpenAlpha k L m D) (a : Γ(H.line, ⊤)) : Prop :=
  ArithmeticThetaGlobalFourTorsionR0190.restrictAlpha L k D X H a = openAlpha k L m D A ∧
  (∀ V : DiskTest k L D X, ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤),
    ExtendsGenerator k L H V η →
    ∃ (i : Fin L) (z : kˣ) (j : ℕ) (v : (PowerSeries k)ˣ),
      KernelCoordinates k L m D V.toTest i z ∧ AllowedOrder L m i j ∧
      pullbackGlobalSection V.disk H.line a =
        scalar (PowerSeries k) (PowerSeries.X^j * (v : PowerSeries k)) • η) ∧
  (∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    CanonicalMarking k L ζ V.level →
    ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤),
      ExtendsGenerator k L H V η →
      pullbackGlobalSection V.disk H.line a =
        scalar (PowerSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m)^2) • η)

/-- Divisor of the actual compact section in every normal affine frame. -/
def HalfDivisor (x : X.space) (a : Γ(H.line, ⊤))
    (E : Component k L D X x →₀ ℤ) : Prop :=
  (∀ y, 0 ≤ E y) ∧ (∀ y, y ∉ cuspSet k L D X x → E y = 0) ∧
  ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ≠ 0 ∧
  (∃ ι : Type, Nonempty (NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)) ∧
  ∀ (ι : Type) (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι),
    MatchesSectionOrder (Component k L D X x) (hodge k L D X x H) C
      (ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a) (2 • E)

/-- Normalization in the ORIGINAL disk and specified Hodge generator, for the
basic unary factor with target period q^m; no further completion cover. -/
def HalfBranch (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (Component k L D X x))
    (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H) : Prop :=
  ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    CanonicalMarking k L ζ V.level →
    ∀ (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk)
      (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)),
      ExtendsGenerator k L H V η →
      ∃ h : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
        IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ h ∧
        pullbackGlobalSection f A.line A.section_ =
          scalar (PowerSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m)) • h ∧
        (ArithmeticThetaCommonHalfHodgeR0185.diskHodgeIso k L D X x H V f hf).hom.app ⊤
          (((pullback_tensorPower_iso _ _ f A.line 2).symm ≪≫
            (Scheme.Modules.pullback f).mapIso β).hom.app ⊤
            (tensorPowerSection _ ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ h)) = η

end ArithmeticThetaIsogenyHalfLinesR0193
