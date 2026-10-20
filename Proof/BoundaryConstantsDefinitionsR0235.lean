module

public import OpenConstantCartesianR0234
public import OpenHodgeConstantComparisonR0234
public import CompactConstantComparisonR0234
public import ConstantComparisonCoherenceR0234
public import CompactHodgeLatticeExtensionR0182
public import CoefficientCompletedMapsR0157
public import TateFullLevelMarkingR0181

@[expose] public section

/-! Coefficient extension of the actual Tate tests and the compact Hodge lattice.
Only semantic definitions are introduced here; construction and compatibility
are assigned to the new proof modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaBoundaryConstantsR0235
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelConstantsR0234

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]

def laurentMap (ι : k →+* l) : LaurentSeries k →+* LaurentSeries l :=
  Classical.choose (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι).1

def punctureMap (ι : k →+* l) : Puncture l ⟶ Puncture k :=
  Spec.map (CommRingCat.ofHom (laurentMap ι))

def diskMap (ι : k →+* l) : Disk l ⟶ Disk k :=
  Spec.map (CommRingCat.ofHom (PowerSeries.map ι))

/-- The coordinate morphism on the fixed Tate cubics: actual Cartesian and
pointed squares, and the actual affine x,y chart map, fixing both coordinates. -/
def CurveMap (ι : k →+* l) (L : ℕ)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) : Prop :=
  IsPullback b (structureMap (LaurentSeries l) (TateCurve l L))
    (structureMap (LaurentSeries k) (TateCurve k L)) (punctureMap ι) ∧
  origin (LaurentSeries l) (TateCurve l L) ≫ b =
    punctureMap ι ≫ origin (LaurentSeries k) (TateCurve k L) ∧
  ∃ χ : ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) (TateCurve k L) →+*
      ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries l) (TateCurve l L),
    χ.comp (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) (TateCurve k L)) =
      (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries l) (TateCurve l L)).comp (laurentMap ι) ∧
    χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective) =
      WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve l L).toProjective ∧
    χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective) =
      WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve l L).toProjective ∧
    ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries l) (TateCurve l L) ≫ b =
      Spec.map (CommRingCat.ofHom χ) ≫
        ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) (TateCurve k L)

/-- Ordered full markings are compared as actual point morphisms, including
both zero indices. The full natural group laws remain in the TateLevel data. -/
def Transfers (ι : k →+* l) {L : ℕ} (A : TateLevel k L) (B : TateLevel l L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) : Prop :=
  ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
    (LaurentSeries k) (TateCurve k L) A.law
    (LaurentSeries l) (TateCurve l L) B.law (laurentMap ι) b ∧
  ∀ i j : Fin L,
    ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries l)
      (TateCurve l L) B.law B.marking i j ≫ b =
    punctureMap ι ≫ ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k)
      (TateCurve k L) A.law A.marking i j

/-- The differential isomorphism comes from this pointed Cartesian square. -/
def tateHodgeIso (ι : k →+* l) {L : ℕ} (A : TateLevel k L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b) :
    (Scheme.Modules.pullback (punctureMap ι)).obj (Hodge (LaurentSeries k) (TateCurve k L)) ≅
      Hodge (LaurentSeries l) (TateCurve l L) := by
  letI : (TateCurve k L).IsElliptic := A.elliptic
  letI : Algebra (LaurentSeries k) (LaurentSeries l) := (laurentMap ι).toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k L)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k L).toProjective
  exact pointedDifferentialIso _ _ b hb.1 _ _ hb.2.1

/-- The actual open generator expressed in the classifying Hodge fiber. -/
def testGenerator {L : ℕ} {D : LevelData k L} (T : Test k L D) :
    Γ((Scheme.Modules.pullback T.base).obj (weight D), ⊤) :=
  (openTestIso k L T).inv.app ⊤ (hodgeGenerator k L T.differential)

/-- Comparison on a punctured disk, with the actual equality of classifiers. -/
def testComparison (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L}
    (T : Test k L D) (S : Test l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (h : S.base ≫ f = punctureMap ι ≫ T.base) :
    (Scheme.Modules.pullback (punctureMap ι)).obj
      ((Scheme.Modules.pullback T.base).obj (weight D)) ≅
      (Scheme.Modules.pullback S.base).obj (weight E) :=
  (Scheme.Modules.pullbackComp (punctureMap ι) T.base).app _ ≪≫
    pullbackEqIso h.symm _ ≪≫
    ((Scheme.Modules.pullbackComp S.base f).app _).symm ≪≫
    (Scheme.Modules.pullback S.base).mapIso e

/-- The comparison extends the specified normalized open Hodge isomorphism;
there is no free scalar, sign, chosen expansion map, or replacement line. -/
def CompactCompatible (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) : Prop :=
  (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom =
    ((Scheme.Modules.pullbackComp Y.inclusion F).app H.line).hom ≫
    (pullbackEqIso hF.2 H.line).hom ≫
    ((Scheme.Modules.pullbackComp f X.inclusion).app H.line).inv ≫
    (Scheme.Modules.pullback f).map H.onOpen.hom ≫ e.hom

/-- Exact normalized differentials for the fixed Tate coordinates. -/
def GeneratorCompatible (ι : k →+* l) {L : ℕ} (A : TateLevel k L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b) : Prop :=
  ∀ (δ : CurveFrame k L) (ε : CurveFrame l L),
    Normalized k L δ → Normalized l L ε →
    res _ (by simp) ((tateHodgeIso ι A b hb).hom.app _
      (Scheme.Modules.pullbackLocalSection (punctureMap ι) (hodgeGenerator k L δ))) =
      hodgeGenerator l L ε

/-- Both the full classifier and its normalized differential agree. -/
def TestCompatible (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L}
    (T : Test k L D) (S : Test l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) : Prop :=
  ∃ h : S.base ≫ f = punctureMap ι ≫ T.base,
    res _ (by simp) ((testComparison ι T S f e h).hom.app _
      (Scheme.Modules.pullbackLocalSection (punctureMap ι) (testGenerator T))) =
        testGenerator S

/-- The exact integral frame equation on the SAME disks and compact line map. -/
def DiskFrameCompatible (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (H : Extension k L D X) (J : Extension l L E Y)
    (F : Y.space ⟶ X.space) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.disk ≫ F = diskMap ι ≫ T.disk) : Prop :=
  ∀ (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (ηl : Γ((Scheme.Modules.pullback S.disk).obj J.line, ⊤)),
    ExtendsGenerator k L H T η → ExtendsGenerator l L J S ηl →
      res _ (by simp) (((Scheme.Modules.pullbackComp (diskMap ι) T.disk).app H.line ≪≫
        pullbackEqIso h.symm H.line ≪≫
        ((Scheme.Modules.pullbackComp S.disk F).app H.line).symm ≪≫
        (Scheme.Modules.pullback S.disk).mapIso a).hom.app _
          (Scheme.Modules.pullbackLocalSection (diskMap ι) η)) = ηl

/-- Canonical over a general field means comparison with the normalized actual
boundary lattice after EVERY algebraically closed coefficient extension.
The predicate constrains an existing line, and its existence is an obligation. -/
def GeometricallyCanonical {L : ℕ} {D : LevelData k L}
    {X : Compactification k L D} (H : Extension k L D X) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] [IsAlgClosed l] (ι : k →+* l)
    (E : LevelData l L) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hf : RespectsClassifiers ι D E f)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E),
    HodgeCompatible ι D E f e → ∀ J : Extension l L E Y,
    Canonical l L J → ∃! a : (Scheme.Modules.pullback F).obj H.line ≅ J.line,
      CompactCompatible ι f F hF e H J a

end ArithmeticThetaBoundaryConstantsR0235
