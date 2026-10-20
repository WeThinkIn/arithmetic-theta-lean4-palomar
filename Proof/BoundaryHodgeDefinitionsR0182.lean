module

public import EveryGeometricBoundaryTateDiskR0181
public import TateCompletedLocalParameterR0181
public import InitialTensorBaseChangeR0164
public import IntegralDiscriminantHodgeR0163

@[expose] public section

/-! Actual Hodge lattices on the accepted compactified level base.
These are ordinary definitions; their existence and expansion properties are
new proof obligations. All comparisons use the specified classifying maps. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower

variable (k : Type) [Field k] [CharZero k] (L : ℕ)

abbrev CurveFrame :=
  (SheafOfModules.unit (Curve (LaurentSeries k) (TateCurve k L)).ringCatSheaf :
    (Curve (LaurentSeries k) (TateCurve k L)).Modules) ≅
      (structureMap (LaurentSeries k) (TateCurve k L)).kaehler

/-- The actual differential dx/(2y) on the fixed Tate cubic, normalized on
its specified affine chart. The accepted global-frame provider supplies it. -/
def Normalized (δ : CurveFrame k L) : Prop :=
  let E := Iso.refl (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k L)
  let U := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen k L E
  let x := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)
  let y := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)
  ArithmeticThetaCompactifiedDifferentialR0145.relativeD
    (structureMap (LaurentSeries k) (TateCurve k L)) U x =
      (2*y) • Scheme.Modules.Hom.app δ.hom U (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), U))

def hodgeGenerator (δ : CurveFrame k L) :
    Γ(Hodge (LaurentSeries k) (TateCurve k L), ⊤) :=
  res _ (by simp) (Scheme.Modules.pullbackLocalSection
    (origin (LaurentSeries k) (TateCurve k L)) (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))))

/-- The full marking, point-preserving Cartesian map, multiplication
compatibility and normalized differential all refer to the same cubic. -/
structure Test (D : LevelData k L) where
  level : TateLevel k L
  base : Puncture k ⟶ OpenBase k L D
  map : Curve (LaurentSeries k) (TateCurve k L) ⟶ D.atlas.descent.family.curve
  classifies : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two
    D.cover D.quotient (LaurentSeries k) (TateCurve k L) level.law level.marking base map
  nsmul_eq : ∀ n, level.law.schemeNsmul n ≫ map = map ≫ D.atlas.descent.family.law.schemeNsmul n
  differential : CurveFrame k L
  normalized : Normalized k L differential

structure DiskTest (D : LevelData k L) (X : Compactification k L D) extends Test k L D where
  disk : Disk k ⟶ X.space
  extends_eq : Extends k L D X base disk

abbrev openHodge (D : LevelData k L) :=
  (Scheme.Modules.pullback D.quotient.inclusion).obj (hodge D.atlas.descent.family)
abbrev openPower (D : LevelData k L) (n : ℕ) :=
  tensorPower (OpenBase k L D) (openHodge k L D) n

/-- Canonical differential pullback, not a freely chosen scalar comparison. -/
def testIso {D : LevelData k L} (T : Test k L D) :
    (Scheme.Modules.pullback (T.base ≫ D.quotient.inclusion)).obj
      (hodge D.atlas.descent.family) ≅ Hodge (LaurentSeries k) (TateCurve k L) := by
  let ι : D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
  have hmap : baseMap D.atlas.quotient.ring (LaurentSeries k) ι =
      T.base ≫ D.quotient.inclusion := Spec.map_preimage _
  let C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring
      D.atlas.descent.family (LaurentSeries k) (TateCurve k L) T.level.law :=
    { scalar := ι
      map := T.map
      cartesian := by rw [hmap]; exact T.classifies.2.1
      origin_eq := by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq := T.nsmul_eq }
  exact pullbackEqIso hmap.symm (hodge D.atlas.descent.family) ≪≫ comparison C

def openTestIso {D : LevelData k L} (T : Test k L D) :
    (Scheme.Modules.pullback T.base).obj (openHodge k L D) ≅
      Hodge (LaurentSeries k) (TateCurve k L) :=
  (Scheme.Modules.pullbackComp T.base D.quotient.inclusion).app _ ≪≫ testIso k L T

def pullAmbientPower {D : LevelData k L} (T : Test k L D) (n : ℕ)
    (s : Γ(power D.atlas.descent.family n, ⊤)) :
    Γ(HodgePower (LaurentSeries k) (TateCurve k L) n, ⊤) :=
  res _ (by simp) ((tensorComparison (T.base ≫ D.quotient.inclusion)
    (hodge D.atlas.descent.family) (Hodge (LaurentSeries k) (TateCurve k L))
    (testIso k L T) n).hom.app _
      (Scheme.Modules.pullbackLocalSection (T.base ≫ D.quotient.inclusion) s))

def pullToOpen {D : LevelData k L} (n : ℕ)
    (s : Γ(power D.atlas.descent.family n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPullback.pullback_tensorPower_iso _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (Scheme.Modules.pullbackLocalSection D.quotient.inclusion s))

/-- An invertible sheaf with its identification with the actual open Hodge
line. Canonical boundary lattices are a separate predicate to be proved. -/
structure Extension (D : LevelData k L) (X : Compactification k L D) where
  line : X.space.Modules
  invertible : Scheme.Modules.IsInvertible line
  onOpen : (Scheme.Modules.pullback X.inclusion).obj line ≅ openHodge k L D

def diskGenericIso {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    (Scheme.Modules.pullback (genericInclusion k)).obj
      ((Scheme.Modules.pullback T.disk).obj H.line) ≅
        Hodge (LaurentSeries k) (TateCurve k L) :=
  (Scheme.Modules.pullbackComp (genericInclusion k) T.disk).app H.line ≪≫
    pullbackEqIso T.extends_eq.2.1 H.line ≪≫
    ((Scheme.Modules.pullbackComp T.base X.inclusion).app H.line).symm ≪≫
    (Scheme.Modules.pullback T.base).mapIso H.onOpen ≪≫ openTestIso k L T.toTest

def ExtendsGenerator {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤)) : Prop :=
  IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η ∧
  res _ (by simp) ((diskGenericIso k L H T).hom.app _
    (Scheme.Modules.pullbackLocalSection (genericInclusion k) η)) =
      hodgeGenerator k L T.differential

def Canonical {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) : Prop :=
  ∀ T : DiskTest k L D X,
    ∃! η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤), ExtendsGenerator k L H T η

def restrictPower {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (n : ℕ)
    (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))

def diskPower {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) (n : ℕ)
    (s : Γ(tensorPower X.space H.line n, ⊤)) :
    Γ(tensorPower (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPullback.pullback_tensorPower_iso _ _
    T.disk H.line n).hom.app _ (Scheme.Modules.pullbackLocalSection T.disk s))

/-- The designated source characteristic, normalized modulo N. -/
def unaryResidue (m N : ℕ) (ν : ℤ) : ℕ :=
  Int.toNat ((((N / 2 : ℕ) : ℤ) + ((N / m : ℕ) : ℤ) * ν) % (N : ℤ))

def ExactD2 {D : LevelData k L} (T : Test k L D)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) : Prop :=
  pullAmbientPower k L T 24 d =
    scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L) •
    tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L)) 24 ⊤
      (hodgeGenerator k L T.differential)

end ArithmeticThetaBoundaryHodgeR0182
