module

public import CommonBasicUnaryCoverR0194
public import SquareHalfHodgeCoverDegreeR0194
public import HigherLevelProjectiveRatiosR0194
public import ConservativeMatrixKernelR0189
public import EarlyCertificateAssembly
public import SharpCoverRatiosDefinitionsR0194
public import LatticeGlobalSectionsDefinitionsR0188

@[expose] public section

/-! Source-specific definitions for the sharp-cover section and cutoff consumers.
These are ordinary definitions, with all new assertions assigned to proof workers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSharpKernelR0195
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaNormalizedSections ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaCompactUnaryR0183

def norms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n =>
    ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A ij.1) ij.2)

def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (norms A).card

structure NormIndex {n h : ℕ} (A : Matrices n h) where
  norm : Fin (normCount A) → ℕ
  index : Fin h × Fin n → Fin (normCount A)

def IndexesNorms {n h : ℕ} (A : Matrices n h) (I : NormIndex A) : Prop :=
  Function.Injective I.norm ∧ Function.Surjective I.index ∧
  ∀ ij, I.norm (I.index ij) = ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A ij.1) ij.2

/-- Natural division is the exact nonnegative floor, with no enlarged cutoff. -/
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))

/-- Actual common disk frame; every field is geometric data or a concrete
predicate on its maps. Existing common_basic_unary_cover supplies this data. -/
structure CoverFrame (k : Type) [Field k] [CharZero k] (N : ℕ)
    {D : LevelData k (level N)} {X : Compactification k (level N) D}
    (H : Extension k (level N) D X) (V : DiskTest k (level N) D X)
    (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k)))
      (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ)
    (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k)))
      (projection k (level N) D X (V.disk (closedPoint k))) b) where
  disk : Disk k ⟶ C.space
  triangle : disk ≫ (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k))) = V.disk
  dominant : IsDominant (genericInclusion k ≫ disk)
  frame : Sections (Disk k) ((Scheme.Modules.pullback disk).obj ((Scheme.Modules.pullback C.map).obj J.line))
  isFrame : ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ frame
  generator : Sections (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line)
  extendsGenerator : ExtendsGenerator k (level N) H V generator
  square_eq : (squareOnDisk k (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
    ((Scheme.Modules.pullback C.map).obj J.line) H.line
    (squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
      (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
    disk V.disk triangle).hom.app ⊤ (tensorPowerSection _ _ 2 ⊤ frame) = generator

/-- Equality as rational sections, using a genuine nonempty base open and
its actual inverse image. This fixes the multiplication by the base ratio. -/
def RatioMultiple {B Y : Scheme} [IsIntegral B] (p : Y ⟶ B) (J : Y.Modules)
    (t t₀ : Sections Y J) (r : B.functionField) : Prop :=
  ∃ (U : B.Opens) (hU : Nonempty U), letI := hU
    ∃ v : B.presheaf.obj (Opposite.op U), B.germToFunctionField U v = r ∧
      J.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op t =
        p.app U v • J.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op t₀

/-- The output consists of regular sections on the SAME cover, their exact
full series, their rational ratios, and their powers identified with compact F. -/
def RegularUnary (k : Type) [Field k] [CharZero k] (N s : ℕ)
    (m : Fin s → ℕ) (ν : Fin s → ℤ)
    {D : LevelData k (level N)} {X : Compactification k (level N) D}
    (H : Extension k (level N) D X) (V : DiskTest k (level N) D X)
    (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k)))
      (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ)
    (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k)))
      (projection k (level N) D X (V.disk (closedPoint k))) b)
    (F : CoverFrame k N H V J b C)
    (t₀ : Fin s → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line)) : Prop :=
  ∃ t : Fin s → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line),
    UnaryPowers k N s m ν H (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
      ((Scheme.Modules.pullback C.map).obj J.line)
      (squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
        (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
      (fun i => tensorPowerSection _ _ (exponent N) ⊤ (t i)) ∧
    ∀ i, t i ≠ 0 ∧
      pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) (t i) =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (unarySeries k N (m i) (ν i)) • F.frame ∧
      ∃ r : (Component k (level N) D X (V.disk (closedPoint k))).functionField,
        RationalExpansion k _ (genericInclusion k ≫ (F.disk ≫ C.map)) r
          (algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N (m i) (ν i)) /
            algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N (m i) 0)) ∧
        RatioMultiple C.map ((Scheme.Modules.pullback C.map).obj J.line) (t i) (t₀ i) r

/-- Actual sharp-cover matrix family. The exact norm count bounds the degree;
all unary and matrix sections and the common frame are constructed outputs. -/
def GeometricFamily {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D}
    (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : Prop :=
  let N := commonN A
  let L := level N
  let x := V.disk (closedPoint ℂ)
  ∃ J : SquareLine (Component ℂ L D X x) (hodge ℂ L D X x H),
    ∃ C : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x) (2^(normCount A-1)),
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

/-- The existing exact elimination certificate, now to be supplied at the
unconditional sharp cutoff. This is formal-series image data, not modularity. -/
def ImageData {n h : ℕ} (A : Matrices n h) (B : ℕ) : Prop :=
        (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run
          (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j =>
          ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧
          Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns
          (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j =>
          ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) =
          LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin
          (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length =>
          ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ
          (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A
          B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) =
          LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j)
          = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A
          B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates
          (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A
          (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run
          (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) =
          ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) →
          c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j

end ArithmeticThetaSharpKernelR0195
