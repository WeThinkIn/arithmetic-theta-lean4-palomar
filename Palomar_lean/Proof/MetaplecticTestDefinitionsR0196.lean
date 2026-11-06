module

public import RootTestDefinitionsR0196
public import SharpMatrixGeometricFamilyR0195
public import SquareIsometryInterfaceAdapterR0192
public import SharpKernelDefinitionsR0195
public import CoverComparisonDefinitions

@[expose] public section

/-! Test objects of the square-root moduli problem and their actual scheme fibers.
All assertions of representability, naturality and degree are future obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaCoverComparison

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195

/-- The accepted sharp geometric family strengthened by actual representability
at every square-root test object on its compact component. -/
def MetaplecticFamily {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D}
    (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : Prop :=
  let N := commonN A
  let L := level N
  let x := V.disk (closedPoint ℂ)
  ∃ J : SquareLine (Component ℂ L D X x) (hodge ℂ L D X x H),
    ∃ C : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x) (2^(normCount A-1)),
      FiniteRootLevel C.map (pullRoot C.map J) ∧
      Etale C.map ∧ (normCount A = 1 → IsIso C.map) ∧
      SquareCoverDegree ℂ L D X H x J (2^(normCount A-1)) n C ∧
      ∃ F : CoverFrame ℂ N H V J (2^(normCount A-1)) C,
        ∃ (t : Fin U.count → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line))
          (σ : Fin h → Sections C.space (tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n)),
          (∀ j, t j ≠ 0 ∧ pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) (t j) =
            ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (unarySeries ℂ N (U.pair j).1 (U.pair j).2) • F.frame) ∧
          (∀ i, σ i = ∑ a : Cosets A i, tensorProductSection C.space ((Scheme.Modules.pullback C.map).obj J.line)
            n ⊤ (fun j => t (U.index i a j))) ∧
          ∀ c : Fin h → ℂ,
            pullbackPowerSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) n
              (∑ i : Fin h, baseScalar ℂ (C.map ≫ projection ℂ L D X x) (c i) • σ i) =
                ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (expanded A c) •
                  tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback F.disk).obj
                    ((Scheme.Modules.pullback C.map).obj J.line)) n ⊤ F.frame

end ArithmeticThetaMetaplecticTestsR0196
