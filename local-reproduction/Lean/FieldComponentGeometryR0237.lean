import ComponentCurveFramesR0184

/-! Geometry of the actual compact level component over the coefficient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaArithmeticHalfLinesR0237
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaNormalizedSections

/-- The actual component has the required curve geometry over every
characteristic-zero coefficient field, without a rationality assertion for
its closed points. -/
theorem field_component_geometry
    (k : Type) [Field k] [CharZero k]
    (L : ℕ) (_hL : 3 ≤ L) (_heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space) :
    IsProper (projection k L D X x) ∧
    SmoothOfRelativeDimension 1 (projection k L D X x) ∧
    ArithmeticThetaCurveDegree.OneDimensionalCharts (Component k L D X x) ∧
    NormalAffine (Component k L D X x) := by
  letI := X.proper
  letI := X.smooth
  letI : IsClosedImmersion (inclusion k L D X x) :=
    IsClosedImmersion.of_isPreimmersion (inclusion k L D X x)
      (by rw [Scheme.Opens.range_ι]; exact compactComponent_closed k L D X x)
  letI : IsProper (projection k L D X x) := inferInstance
  letI : SmoothOfRelativeDimension 1 (projection k L D X x) :=
    smoothOfRelativeDimension_comp 0 1 (inclusion k L D X x) X.projection
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.smooth_oneDimensionalCharts
      (projection k L D X x)
  · exact fun U hU => ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed
      (Component k L D X x) k (projection k L D X x) U hU

#print axioms field_component_geometry
end ArithmeticThetaArithmeticHalfLinesR0237
