module

public import FieldIsogenyCanonicalHalfLineR0237
public import FieldCompactUnaryR0236
public import CommonBasicUnaryCoverR0194
public import RatioUnaryRegularSectionsR0195
public import SharpKernelDefinitionsR0195

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaSharpKernelR0195
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaPullback

/-- Actual arithmetic common cover and its regular normalized unary family.
All geometric witnesses and full expansion equations are construction outputs. -/
def CommonUnary (k : Type) [Field k] [CharZero k] (N s : ℕ)
    (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ)
    (D : LevelData k (level N)) (X : Compactification k (level N) D)
    (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ A : ∀ i, CanonicalHalf k (level N) (m i) D X H x,
    ∃ C : RootCover k (Component k (level N) D X x)
      (projection k (level N) D X x) (2^s),
      Etale C.map ∧ (s = 0 → IsIso C.map) ∧
      ∃ F : CoverFrame k N H V (A 0).squareLine (2^s) C,
        ∃ t₀ : Fin (s+1) → Sections C.space
          ((Scheme.Modules.pullback C.map).obj (A 0).data.line),
          (∀ i, t₀ i ≠ 0 ∧
            pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj (A 0).data.line)
              (t₀ i) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
                (unarySeries k N (m i) 0) • F.frame) ∧
          RegularUnary k N (s+1) m ν H V (A 0).squareLine (2^s) C F t₀

end ArithmeticThetaArithmeticCommonCoverR0238
