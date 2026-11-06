module

public import OpenUnaryDesignatedExpansionR0182
public import CompactDiscriminantSectionR0182
public import BoundaryHodgeDefinitionsR0182

@[expose] public section

/-! Open sections already provided by r0180, and their still unproved compact
extensions. No boundary integrality, global section or expansion is a field of
OpenPower. Every comparison below uses the accepted actual geometric maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182

abbrev level (N : ℕ) : ℕ := 24*N^2
abbrev exponent (N : ℕ) : ℕ := (1+12*N)^2-1
abbrev weight (N : ℕ) : ℕ := exponent N / 2
abbrev dExponent (N : ℕ) : ℕ := exponent N / 48

variable (k : Type) [Field k] [CharZero k] (m N : ℕ)

/-- The already constructed open-family data. IsD2 and IsKatoValue are the
intrinsic initial-tensor and actual point-evaluation predicates, not expansion
assumptions. The two index arguments name the same nonidentity target point. -/
structure OpenPower (D : LevelData k (level N)) (a b : Fin N) where
  quotient : ArithmeticThetaOpenHodgeR0180.Quotient D.atlas.quotient.ring
    (ArithmeticThetaOpenHodgeR0180.levelFamily k (level N) D.atlas) m
    (ArithmeticThetaOpenHodgeR0180.kernelPoint k (level N) D.atlas m)
  discriminant : Γ(ArithmeticThetaOpenHodgeR0180.power quotient.target 24, ⊤)
  intrinsic : ArithmeticThetaOpenHodgeR0180.IsD2 quotient.target discriminant
  value : D.atlas.quotient.ring
  value_spec : ArithmeticThetaOpenHodgeR0180.IsKatoValue quotient.target (1+12*N)
    (ArithmeticThetaOpenHodgeR0180.liftPoint k (level N) D.atlas m N a.val b.val ≫ quotient.arrow.map) value
  section_ : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (weight N), ⊤)
  normalized : ArithmeticThetaOpenHodgeR0180.IsNormalizedPower k (level N) D.atlas
    m N quotient discriminant value section_

/-- Membership in the actual integral Tate lattice of the specified source
Hodge power, with no restriction on the marking in the test. -/
def IntegralAtTest {D : LevelData k (level N)} {a b : Fin N}
    (A : OpenPower k m N D a b) (V : ArithmeticThetaBoundaryHodgeR0182.Test k (level N) D) : Prop :=
  ∃ f : PowerSeries k, f ≠ 0 ∧
    pullAmbientPower k (level N) V (weight N) A.section_ =
      ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
        (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k (level N)))
        (weight N) ⊤ (hodgeGenerator k (level N) V.differential)

/-- A full coefficient identity for the actual compact section on a disk. -/
def DiskCoefficient {D : LevelData k (level N)} {X : Compactification k (level N) D}
    (H : Extension k (level N) D X) (V : DiskTest k (level N) D X)
    (s : Γ(tensorPower X.space H.line (weight N), ⊤)) (f : PowerSeries k) : Prop :=
  ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤),
    ExtendsGenerator k (level N) H V η →
    diskPower k (level N) H V (weight N) s =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) f •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line) (weight N) ⊤ η

/-- Full geometric unary realization on the actual compact level base.
Regularity is encoded by a genuine global sheaf section, and the disk equations
retain the actual completion map and normalized generator. -/
def RealizesUnary {D : LevelData k (level N)} {X : Compactification k (level N) D}
    (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N}
    (A : OpenPower k m N D a b)
    (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : Prop :=
  restrictPower k (level N) H (weight N) s = pullToOpen k (level N) (weight N) A.section_ ∧
  IsFrame (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (weight N)) ⊤ A.section_ ∧
  (∀ V : DiskTest k (level N) D X, ∃ f : PowerSeries k,
    f ≠ 0 ∧ DiskCoefficient k N H V s f) ∧
  (∀ (V : DiskTest k (level N) D X) (ζ : k), IsPrimitiveRoot ζ (level N) →
    CanonicalMarking k (level N) ζ V.level →
    ∃ f : PowerSeries k,
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N ∧
      DiskCoefficient k N H V s f)

end ArithmeticThetaCompactUnaryR0183
