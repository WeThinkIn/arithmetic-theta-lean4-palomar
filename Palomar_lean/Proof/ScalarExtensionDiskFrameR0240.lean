module

public import ScalarExtensionGeometryR0240
public import ClassifiedTateDiskTransferR0235
public import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeDiscriminantR0171
namespace DiskFrameProof
variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
variable {n h : ℕ} {A : Matrices n h}

/-- The full coefficient map commutes with the structural maps. -/
lemma disk_over (ι : k →+* l) :
    diskMap ι ≫ diskStructure k = diskStructure l ≫ fieldMap ι := by
  exact ArithmeticThetaBoundaryConstantsR0235.ClassifiedTateDiskTransfer.disk_structure ι

/-- The universal property retains both specified triangles. -/
def lift (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    DiskLift ι G where
  map := pullback.lift (diskMap ι ≫ G.frame.disk) (diskStructure l) (by
    rw [Category.assoc, GeometryProof.frame_over, disk_over])
  triangle := pullback.lift_fst _ _ _
  over_eq := pullback.lift_snd _ _ _

/-- The fixed comparison carries the pullback of the original frame. -/
lemma frame_isFrame (ι : k →+* l)
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (D : DiskLift ι G) :
    IsFrame ((Scheme.Modules.pullback D.map).obj (line ι G)) ⊤ (frame ι G D) := by
  exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
    (frameComparison ι G D).symm _
    (HodgeBaseChange.pullback_frame (diskMap ι) _ _ G.frame.isFrame)

/-- Coefficient extension preserves the centre of the full disk. -/
lemma disk_closed (ι : k →+* l) : diskMap ι (closedPoint l) = closedPoint k := by
  letI : IsLocalHom (PowerSeries.map ι) := PowerSeries.map.isLocalHom ι
  exact Spec_closedPoint

/-- The lifted generic point cannot specialize to the centre with equal image:
the prescribed original Tate test separates the open curve from its boundary. -/
lemma dominant (ι : k →+* l)
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (D : DiskLift ι G)
    [GeometricallyIntegral (structureMap ι G)]
    [SmoothOfRelativeDimension 1 (structureMap ι G)] :
    IsDominant (genericInclusion l ≫ D.map) := by
  classical
  letI : IsIntegral (Space ι G) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap ι G)
  let p : Space ι G ⟶ G.compact.space := projection ι G ≫ G.cover.map ≫
    ArithmeticThetaComponentDegreeR0184.inclusion k _ G.data G.compact
      (G.test.disk (closedPoint k))
  have ht : D.map ≫ p = diskMap ι ≫ G.test.disk := by
    dsimp [p]
    rw [← Category.assoc, D.triangle, Category.assoc, G.frame.triangle]
  have hg : genericInclusion l ≫ D.map ≫ p =
      ArithmeticThetaBoundaryConstantsR0235.punctureMap ι ≫ G.test.base ≫
        G.compact.inclusion := by
    rw [ht, ← Category.assoc]
    rw [show genericInclusion l ≫ diskMap ι =
      ArithmeticThetaBoundaryConstantsR0235.punctureMap ι ≫ genericInclusion k from
        ArithmeticThetaBoundaryConstantsR0235.ClassifiedTateDiskTransfer.generic_square ι]
    rw [Category.assoc, G.test.extends_eq.2.1]
  let z := _root_.genericPoint (Puncture l)
  have he : (genericInclusion l ≫ D.map) z = _root_.genericPoint (Space ι G) := by
    by_contra hn
    have hc := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (structureMap ι G) _ hn
    have hs : (genericInclusion l ≫ D.map) z ⤳ D.map (closedPoint l) :=
      (IsLocalRing.specializes_closedPoint ((genericInclusion l) z)).map D.map.continuous
    have heq : (genericInclusion l ≫ D.map) z = D.map (closedPoint l) :=
      (hc.closure_subset (specializes_iff_mem_closure.mp hs)).symm
    have hpoint : (ArithmeticThetaBoundaryConstantsR0235.punctureMap ι ≫
        G.test.base ≫ G.compact.inclusion) z = G.test.disk (closedPoint k) := by
      rw [← hg]
      change p ((genericInclusion l ≫ D.map) z) = _
      rw [heq]
      change (D.map ≫ p) (closedPoint l) = _
      rw [ht]
      change G.test.disk (diskMap ι (closedPoint l)) = _
      rw [disk_closed]
    have hb := G.test.extends_eq.2.2
    change G.test.disk (closedPoint k) ∉ Set.range G.compact.inclusion at hb
    exact hb ⟨G.test.base (ArithmeticThetaBoundaryConstantsR0235.punctureMap ι z), hpoint⟩
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (_root_.genericPoint_spec (Space ι G)).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨z, he⟩

end DiskFrameProof

/-- The same full Tate disk and its original frame extend along every coefficient map. -/
theorem scalar_extension_disk_frame
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ∃ D : DiskLift ι G,
      IsFrame ((Scheme.Modules.pullback D.map).obj (line ι G)) ⊤ (frame ι G D) ∧
      IsDominant (genericInclusion l ≫ D.map) := by
  have hg := scalar_extension_geometry k l ι n h hn hh A hA G
  letI : SmoothOfRelativeDimension 1 (structureMap ι G) := hg.2.2.1
  letI : GeometricallyIntegral (structureMap ι G) := hg.2.2.2.1
  exact ⟨DiskFrameProof.lift ι G, DiskFrameProof.frame_isFrame ι G _,
    DiskFrameProof.dominant ι G _⟩

#print axioms scalar_extension_disk_frame
end ArithmeticThetaScalarExtensionR0240
