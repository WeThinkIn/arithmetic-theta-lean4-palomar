module

public import ComponentDegreeDefinitionsR0184
public import TensorLineDegrees

@[expose] public section

/-! Curve geometry and actual Hodge-power frames on each compact component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaComponentDegreeR0184
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot
open ArithmeticThetaRelativeDiscriminantR0171
open CompactHodgeLatticeExtensionR0182

namespace ComponentCurveFramesR0184

/-- Refine actual invertible-sheaf frames to nonempty normal affine opens. -/
lemma normalFrameCover_of_invertible (Y : Scheme.{0}) [IsIntegral Y]
    (hY : NormalAffine Y) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (NormalFrameCover Y M Y) := by
  classical
  have hex : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      Nonempty (LocalFrame Y M U) := by
    intro y
    obtain ⟨V, s, hyV, hs⟩ := local_frame_exists hM y
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
    exact ⟨U, hyU, hU, ⟨InitialHodgeSection.frame M (res M hUV s)
      (HodgeBaseChange.frame_restrict M hUV s hs)⟩⟩
  choose U hy hU e using hex
  letI hn : ∀ y, Nonempty (U y) := fun y => ⟨⟨y, hy y⟩⟩
  exact ⟨{
    opens := U
    covers := fun y _ => Opens.mem_iSup.mpr ⟨y, hy y⟩
    nonempty := hn
    affine := hU
    normal := fun y => hY (U y) (hU y)
    frame := fun y => Classical.choice (e y)
  }⟩

/-- The residue scalar structure is the one induced by the given morphism. -/
lemma closed_placeDegree_one (k : Type) [Field k] [IsAlgClosed k]
    (Y : Scheme) (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ArithmeticThetaCurveDegree.placeDegree k f y = 1 := by
  letI : Algebra k (Y.residueField y) :=
    (ArithmeticThetaCurveDegree.baseToResidue k f y).toAlgebra
  letI : Module.Finite k (Y.residueField y) :=
    ArithmeticThetaCurveDegree.baseToResidue_finite_of_closed Y k f y hy
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral

end ComponentCurveFramesR0184

/-- Every accepted geometric component is a proper normal smooth curve, with
natural normal affine frames for all powers of its actual Hodge extension. -/
theorem component_curve_frames
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space) :
    IsProper (projection k L D X x) ∧
    SmoothOfRelativeDimension 1 (projection k L D X x) ∧
    ArithmeticThetaCurveDegree.OneDimensionalCharts (Component k L D X x) ∧
    NormalAffine (Component k L D X x) ∧
    (∀ (H : Extension k L D X) (n : ℕ),
      IsLineBundle (Component k L D X x) (power k L D X x H n) ∧
      ∃ ι : Type, Nonempty (NormalFrameCover (Component k L D X x)
        (power k L D X x H n) ι)) ∧
    (∀ y : Component k L D X x, IsClosed ({y} : Set (Component k L D X x)) →
      ArithmeticThetaCurveDegree.placeDegree k (projection k L D X x) y = 1) := by
  letI := X.proper
  letI := X.smooth
  letI : IsClosedImmersion (inclusion k L D X x) :=
    IsClosedImmersion.of_isPreimmersion (inclusion k L D X x)
      (by rw [Scheme.Opens.range_ι]; exact compactComponent_closed k L D X x)
  letI : IsProper (projection k L D X x) := inferInstance
  letI : SmoothOfRelativeDimension 1 (projection k L D X x) :=
    smoothOfRelativeDimension_comp 0 1 (inclusion k L D X x) X.projection
  have hn : NormalAffine (Component k L D X x) :=
    fun U hU => ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed
      (Component k L D X x) k (projection k L D X x) U hU
  refine ⟨inferInstance, inferInstance, ?_, hn, ?_, ?_⟩
  · exact ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.smooth_oneDimensionalCharts
      (projection k L D X x)
  · intro H n
    obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
      (Component k L D X x) hn (hodge k L D X x H)
      (H.invertible.pullback (inclusion k L D X x))
    exact ⟨ArithmeticThetaDegreeAssembly.tensorPower_isLineBundle _ _ C n,
      Component k L D X x, ⟨ArithmeticThetaDegreeAssembly.powerCover _ _ C n⟩⟩
  · intro y hy
    exact ComponentCurveFramesR0184.closed_placeDegree_one k _
      (projection k L D X x) y hy

#print axioms component_curve_frames
end ArithmeticThetaComponentDegreeR0184
