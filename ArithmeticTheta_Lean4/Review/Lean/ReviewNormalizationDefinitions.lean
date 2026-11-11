import BoundaryHodgeDefinitionsR0182
import MetaplecticComparisonDefinitionsR0206

/-!
# Tate normalization without a quotient presentation

The differential comparison below is built from a pointed Cartesian map of
actual elliptic families. It is not an arbitrarily chosen line isomorphism.
The compatibility with the identity ideal fixes the cotangent comparison, and
the square equation connects it to the same compact half-weight line.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaReview.Normalization
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaCoverComparison (tensorPowerMap)
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 (EllipticFamily FamilyLevel)
open ArithmeticThetaLocalWeierstrassR0203 (Family)
open ArithmeticThetaSchemeHodgeR0205 (Cotangent IdealCompatible affineDifferential
  cotangentComparison)
open ArithmeticThetaTateCuspsR0181 (Disk Puncture TateCurve TateLevel genericInclusion)
open ArithmeticThetaBoundaryHodgeR0182 (CurveFrame Normalized hodgeGenerator)
open ArithmeticThetaSquareLinesR0192 (SquareLine)

/-- The general-scheme view of an affine elliptic family uses precisely the
same curve, structure map, group operations and geometric properties. -/
def schemeFamily {S : Type} [CommRing S] (E : EllipticFamily S) :
    Family (Base S) where
  curve := E.curve
  p := E.projection
  law :=
    { mul := E.law.mul, one := E.law.one, inv := E.law.inv
      mul_assoc := E.law.mul_assoc, one_mul := E.law.one_mul
      mul_one := E.law.mul_one, inv_mul_cancel := E.law.inv_mul_cancel
      mul_comm := E.commutative, mul_natural := E.law.mul_natural }
  proper := E.proper
  dimension := E.smooth
  connected := E.connected

/-- The affine Hodge-to-cotangent comparison is fixed by the actual conormal
map and the identity-ideal inclusion. This is the original classifier equation
with only its family and maps as parameters. -/
def CanonicalCotangent {S : Type} [CommRing S] (E : EllipticFamily S)
    {U V : Scheme} (F : Family U) (b : U ⟶ V) (v : V ⟶ Base S)
    (f : F.curve ⟶ E.curve)
    (e : (Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pullback v).obj (ArithmeticThetaOpenHodgeR0180.hodge E)) ≅
        Cotangent F) : Prop :=
  ∃ (hz : F.zero ≫ f = (b ≫ v) ≫ (schemeFamily E).zero)
    (a : (Scheme.Modules.pullback f).obj (schemeFamily E).zero.ker.module ≅
      F.zero.ker.module),
    IdealCompatible (schemeFamily E) F f a ∧
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pullback v).map (affineDifferential (schemeFamily E))) ≫
        e.hom =
      ((Scheme.Modules.pullbackComp b v).app (Cotangent (schemeFamily E))).hom ≫
        (cotangentComparison (schemeFamily E) F (b ≫ v) f hz a).hom

/-- A marked Tate test of the actual open Hodge line and its extension to a
disk on a compact target. The period is the one in `TateCurve k L`, namely t^L.
The prescribed differential satisfies dx = (2y) delta on the fixed Tate chart. -/
structure TateChart (k : Type) [Field k] [CharZero k] (L : ℕ)
    (X : Scheme) (W : X.Modules) where
  ring : Type
  [commRing : CommRing ring]
  family : EllipticFamily ring
  marking : FamilyLevel ring family L
  openSpace : Scheme
  inclusion : openSpace ⟶ X
  openImmersion : IsOpenImmersion inclusion
  toFamily : openSpace ⟶ Base ring
  onOpen : (Scheme.Modules.pullback inclusion).obj W ≅
    (Scheme.Modules.pullback toFamily).obj (ArithmeticThetaOpenHodgeR0180.hodge family)
  level : TateLevel k L
  test : ArithmeticThetaOpenHodgeR0180.Test ring family (LaurentSeries k)
    (TateCurve k L) level.law
  puncture : Puncture k ⟶ openSpace
  base_eq : puncture ≫ toFamily = baseMap ring (LaurentSeries k) test.scalar
  marking_x : level.marking.x.val ≫ test.map =
    (puncture ≫ toFamily) ≫ marking.x.val
  marking_y : level.marking.y.val ≫ test.map =
    (puncture ≫ toFamily) ≫ marking.y.val
  disk : Disk k ⟶ X
  extends_eq : genericInclusion k ≫ disk = puncture ≫ inclusion
  differential : CurveFrame k L
  normalized : Normalized k L differential

attribute [instance] TateChart.commRing

/-- Canonical comparison obtained by composing the actual pullback maps and
the pointed differential comparison of the displayed Cartesian Tate test. -/
def TateChart.comparison {k : Type} [Field k] [CharZero k] {L : ℕ}
    {X : Scheme} {W : X.Modules} (T : TateChart k L X W) :
    (Scheme.Modules.pullback (genericInclusion k)).obj
      ((Scheme.Modules.pullback T.disk).obj W) ≅ Hodge (LaurentSeries k) (TateCurve k L) :=
  (Scheme.Modules.pullbackComp (genericInclusion k) T.disk).app W ≪≫
    pullbackEqIso T.extends_eq W ≪≫
    ((Scheme.Modules.pullbackComp T.puncture T.inclusion).app W).symm ≪≫
    (Scheme.Modules.pullback T.puncture).mapIso T.onOpen ≪≫
    (Scheme.Modules.pullbackComp T.puncture T.toFamily).app _ ≪≫
    pullbackEqIso T.base_eq _ ≪≫ ArithmeticThetaOpenHodgeR0180.comparison T.test

/-- Restriction of a specified compact square map along the actual open
triangle, followed by the displayed open Hodge comparison. -/
def restrictedSquare {k : Type} [Field k] [CharZero k] {L : ℕ}
    {X : Scheme} {W : X.Modules} (T : TateChart k L X W)
    {Y U : Scheme} (J : Y.Modules) (p : Y ⟶ X)
    (square : tensorPower Y J 2 ≅ (Scheme.Modules.pullback p).obj W)
    (i : U ⟶ Y) (b : U ⟶ T.openSpace) (triangle : i ≫ p = b ≫ T.inclusion) :
    tensorPower U ((Scheme.Modules.pullback i).obj J) 2 ≅
      (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback T.toFamily).obj
          (ArithmeticThetaOpenHodgeR0180.hodge T.family)) :=
  (pullback_tensorPower_iso _ _ i J 2).symm ≪≫
    (Scheme.Modules.pullback i).mapIso square ≪≫
    (Scheme.Modules.pullbackComp i p).app W ≪≫
    (Scheme.Modules.pullbackCongr triangle).app W ≪≫
    ((Scheme.Modules.pullbackComp b T.inclusion).app W).symm ≪≫
    (Scheme.Modules.pullback b).mapIso T.onOpen

/-- The metaplectic family's marked curve and root square are the restrictions
of this very compact square. The equality of root lines fixes the transport in
the final equation; no independent square root or scalar comparison is chosen. -/
structure InteriorLink {k : Type} [Field k] [CharZero k] {L : ℕ}
    {X : Scheme} {W : X.Modules} (T : TateChart k L X W)
    {Y U : Scheme} (J : Y.Modules) (p : Y ⟶ X)
    (square : tensorPower Y J 2 ≅ (Scheme.Modules.pullback p).obj W)
    (i : U ⟶ Y) (E : ArithmeticThetaMetaplecticComparisonR0206.Object L U)
    (root_eq : E.root.line = (Scheme.Modules.pullback i).obj J) where
  base : U ⟶ T.openSpace
  triangle : i ≫ p = base ≫ T.inclusion
  curve : E.family.curve ⟶ T.family.curve
  cartesian : IsPullback curve E.family.p T.family.projection (base ≫ T.toFamily)
  zero_eq : E.family.zero ≫ curve = (base ≫ T.toFamily) ≫ (schemeFamily T.family).zero
  marking_x : E.marking.x.val ≫ curve = (base ≫ T.toFamily) ≫ T.marking.x.val
  marking_y : E.marking.y.val ≫ curve = (base ≫ T.toFamily) ≫ T.marking.y.val
  multiplicative : ArithmeticThetaSchemeLevelR0204.Multiplicative
    (schemeFamily T.family) E.family (base ≫ T.toFamily) curve
  hodge : (Scheme.Modules.pullback base).obj
    ((Scheme.Modules.pullback T.toFamily).obj
      (ArithmeticThetaOpenHodgeR0180.hodge T.family)) ≅ Cotangent E.family
  canonical : CanonicalCotangent T.family E.family base T.toFamily curve hodge
  square_eq : tensorPowerMap (eqToHom root_eq) 2 ≫
    (restrictedSquare T J p square i base triangle ≪≫ hodge).hom = E.root.square.hom

/-- The square of the actual half-weight frame is a regular Hodge generator,
whose punctured value is the prescribed normalized Tate differential. -/
structure NormalizedFrame {k : Type} [Field k] [CharZero k] {L : ℕ}
    {X : Scheme} {W : X.Modules} (T : TateChart k L X W)
    {Y : Scheme} (J : Y.Modules) (p : Y ⟶ X)
    (square : tensorPower Y J 2 ≅ (Scheme.Modules.pullback p).obj W)
    (d : Disk k ⟶ Y) (triangle : d ≫ p = T.disk)
    (frame : Γ((Scheme.Modules.pullback d).obj J, ⊤)) where
  generator : Γ((Scheme.Modules.pullback T.disk).obj W, ⊤)
  isFrame : IsFrame ((Scheme.Modules.pullback T.disk).obj W) ⊤ generator
  generic_eq : res _ (by simp) (T.comparison.hom.app _
    (Scheme.Modules.pullbackLocalSection (genericInclusion k) generator)) =
      hodgeGenerator k L T.differential
  square_eq : (ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J W square
    d T.disk triangle).hom.app ⊤
      (tensorPowerSection (Disk k) ((Scheme.Modules.pullback d).obj J) 2 ⊤ frame) = generator

/-- All Tate normalization data for one framed compact family. The interior
root, compact square, and disk frame are linked in the same record. -/
structure FrameNormalization {k : Type} [Field k] [CharZero k] (L : ℕ)
    {Y U : Scheme} (J : Y.Modules) (i : U ⟶ Y)
    (E : ArithmeticThetaMetaplecticComparisonR0206.Object L U)
    (root_eq : E.root.line = (Scheme.Modules.pullback i).obj J)
    (d : Disk k ⟶ Y) (frame : Γ((Scheme.Modules.pullback d).obj J, ⊤)) where
  base : Scheme
  weight : base.Modules
  map : Y ⟶ base
  square : tensorPower Y J 2 ≅ (Scheme.Modules.pullback map).obj weight
  chart : TateChart k L base weight
  triangle : d ≫ map = chart.disk
  interior : InteriorLink chart J map square i E root_eq
  normalized : NormalizedFrame chart J map square d triangle frame

end ArithmeticThetaReview.Normalization
