import CyclotomicMatrixModularityR0239
import AdaptiveUniversalSolverR0230

/-! Actual coefficient extension of the accepted arithmetic theta family.
All constructions are ordinary definitions. The new properties are proof tasks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalizedSections

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
variable {n h : ℕ} {A : Matrices n h}

abbrev fieldMap (ι : k →+* l) : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom ι)
abbrev Space (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  pullback (ArithmeticThetaArithmeticFieldR0231.structureMap G) (fieldMap ι)
abbrev projection (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    Space ι G ⟶ G.cover.space :=
  pullback.fst (ArithmeticThetaArithmeticFieldR0231.structureMap G) (fieldMap ι)
abbrev structureMap (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    Space ι G ⟶ Spec (CommRingCat.of l) :=
  pullback.snd (ArithmeticThetaArithmeticFieldR0231.structureMap G) (fieldMap ι)
abbrev line (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  (Scheme.Modules.pullback (projection ι G)).obj (ArithmeticThetaArithmeticFieldR0231.half G)

def sections (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    Fin h → (tensorPower (Space ι G) (line ι G) n).presheaf.obj (Opposite.op ⊤) :=
  fun i => pullbackPowerSection (projection ι G) (ArithmeticThetaArithmeticFieldR0231.half G) n
    (G.sections i)

abbrev diskMap (ι : k →+* l) : Disk l ⟶ Disk k :=
  Spec.map (CommRingCat.ofHom (PowerSeries.map ι))

/-- Both triangles specify the map to the categorical scalar extension. -/
structure DiskLift (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) where
  map : Disk l ⟶ Space ι G
  triangle : map ≫ projection ι G = diskMap ι ≫ G.frame.disk
  over_eq : map ≫ structureMap ι G = diskStructure l

def frameComparison (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (D : DiskLift ι G) :
    (Scheme.Modules.pullback D.map).obj (line ι G) ≅
    (Scheme.Modules.pullback (diskMap ι)).obj
      ((Scheme.Modules.pullback G.frame.disk).obj (ArithmeticThetaArithmeticFieldR0231.half G)) :=
  (Scheme.Modules.pullbackComp D.map (projection ι G)).app _ ≪≫
    (Scheme.Modules.pullbackCongr D.triangle).app _ ≪≫
    ((Scheme.Modules.pullbackComp (diskMap ι) G.frame.disk).app _).symm

def frame (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (D : DiskLift ι G) :
    ((Scheme.Modules.pullback D.map).obj (line ι G)).presheaf.obj (Opposite.op ⊤) :=
  (frameComparison ι G D).inv.app ⊤
    (pullbackGlobalSection (diskMap ι)
      ((Scheme.Modules.pullback G.frame.disk).obj (ArithmeticThetaArithmeticFieldR0231.half G))
      G.frame.frame)

/-- The complete expansion in the pulled-back original frame, for all new scalars. -/
def Expansion (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (D : DiskLift ι G) : Prop :=
  ∀ c : Fin h → l,
    pullbackPowerSection D.map (line ι G) n
      (ArithmeticThetaFieldImageR0233.combination l (structureMap ι G) (sections ι G) c) =
    ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries l)
      (ArithmeticThetaArithmeticFieldR0231.expanded l A c) •
      tensorPowerSection (Disk l) ((Scheme.Modules.pullback D.map).obj (line ι G)) n ⊤
        (frame ι G D)

/-- The actual output matrix, pivots and rational coordinates are retained. -/
def OutputImage (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (o : ArithmeticThetaAdaptiveSolverR0230.Result h) : Prop :=
  o.matrix = ArithmeticThetaComputed.coefficientMatrix A o.cutoff ∧
  ArithmeticThetaFieldImageR0233.SectionImage l A o.cutoff (structureMap ι G) (sections ι G) ∧
  (∀ c : Fin h → l,
    ArithmeticThetaFieldImageR0233.combination l (structureMap ι G) (sections ι G) c = 0 ↔
    (o.matrix.map (algebraMap ℚ l)).mulVec c = 0) ∧
  (∀ d : Fin (ArithmeticThetaElimination.run o.matrix).pivots.length → l,
    (∑ t, ArithmeticThetaLatticeSectionsR0188.baseScalar l (structureMap ι G) (d t) •
      sections ι G (ArithmeticThetaAdaptiveSolverR0230.pivotIndices o t)) = 0 → d = 0) ∧
  (∀ c : Fin h → l, ∃! d : Fin (ArithmeticThetaElimination.run o.matrix).pivots.length → l,
    ArithmeticThetaFieldImageR0233.combination l (structureMap ι G) (sections ι G) c =
      ∑ t, ArithmeticThetaLatticeSectionsR0188.baseScalar l (structureMap ι G) (d t) •
        sections ι G (ArithmeticThetaAdaptiveSolverR0230.pivotIndices o t)) ∧
  (∀ j : Fin h,
    sections ι G j = ∑ t,
      ArithmeticThetaLatticeSectionsR0188.baseScalar l (structureMap ι G)
        (algebraMap ℚ l (ArithmeticThetaAdaptiveSolverR0230.coordinates o j t)) •
      sections ι G (ArithmeticThetaAdaptiveSolverR0230.pivotIndices o t)) ∧
  (∀ (j : Fin h) (d : Fin (ArithmeticThetaElimination.run o.matrix).pivots.length → ℚ),
    sections ι G j = (∑ t,
      ArithmeticThetaLatticeSectionsR0188.baseScalar l (structureMap ι G) (algebraMap ℚ l (d t)) •
      sections ι G (ArithmeticThetaAdaptiveSolverR0230.pivotIndices o t)) →
    d = ArithmeticThetaAdaptiveSolverR0230.coordinates o j)

end ArithmeticThetaScalarExtensionR0240
