import GeometricCanonicalHodgeDescentR0235
import CompactUnaryHodgeRealizationR0183

/-! Actual compact Hodge sections over the coefficient field. These definitions
retain the accepted normalized geometric maps; construction is separate work. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticSectionsR0236
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

abbrev Comparison :=
  ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent.CoefficientMap

/-- Transport a tensor power through the actual pullback line isomorphism. -/
def powerTransport {X Y : Scheme.{0}} (f : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (n : ℕ)
    (s : Γ(tensorPower X M n, ⊤)) : Γ(tensorPower Y N n, ⊤) :=
  ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection
    f _ _ (tensorComparison f M N e n) s

/-- Full discriminant realization in the given compact extension. The local
coefficient is the literal complete discriminant series, including its leading
coefficient, rather than an arbitrary unit of the same order. -/
def RealizesDiscriminant (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X)
    (d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤))
    (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop :=
  restrictPower k L H 24 s = pullToOpen k L 24 d ∧
  ∀ (V : DiskTest k L D X) (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)),
    ExtendsGenerator k L H V η →
    diskPower k L H V 24 s =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) •
      tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k)
        ((Scheme.Modules.pullback V.disk).obj H.line) 24 ⊤ η ∧
    (∀ j : ℕ, j < 2*L →
      PowerSeries.coeff j (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 0) ∧
    PowerSeries.coeff (2*L) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 1

end ArithmeticThetaArithmeticSectionsR0236
