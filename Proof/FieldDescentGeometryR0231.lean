module

public import ArithmeticFieldDefinitionsR0231
public import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

@[expose] public section

/-! Geometry of the actual sharp family over an algebraically closed coefficient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaArithmeticFieldR0231
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaSquareLinesR0192

/-- The specified common formal disk is a morphism over the coefficient field. -/
private theorem frame_over {k : Type} [Field k] [CharZero k]
    {n h : ℕ} {A : Matrices n h} (G : MatrixData k A) :
    G.frame.disk ≫ structureMap G = diskStructure k := by
  change G.frame.disk ≫ (G.cover.map ≫
    (inclusion k (level (commonN A)) G.data G.compact
      (G.test.disk (closedPoint k)) ≫ G.compact.projection)) = _
  rw [← Category.assoc G.cover.map, ← Category.assoc G.frame.disk,
    G.frame.triangle]
  exact G.test.extends_eq.1

/-- The rational point is the centre of this same disk, not a newly chosen cusp. -/
private theorem cusp_over {k : Type} [Field k] [CharZero k]
    {n h : ℕ} {A : Matrices n h} (G : MatrixData k A) :
    cusp G ≫ structureMap G = 𝟙 _ := by
  rw [cusp, Category.assoc, frame_over]
  change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))) = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap k (PowerSeries k)) ≫
      CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k) =
      𝟙 (CommRingCat.of k) := by
    ext x
    simp
  rw [he, Spec.map_id]

/-- The geometric hypotheses for descent hold for the given sharp family,
with its original structural morphisms, sheaves, and formal-disk centre. -/
theorem field_descent_geometry
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (A : Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : MatrixData k A) : DescentGeometry G := by
  have hN : 0 < commonN A :=
    (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [level]
    omega
  have geom := component_curve_frames k (level (commonN A)) hL heven
    G.data G.compact (G.test.disk (closedPoint k))
  letI : IsProper (baseMap G) := geom.1
  letI : SmoothOfRelativeDimension 1 (baseMap G) := geom.2.1
  letI : IsIntegral G.cover.space := G.cover.integral
  letI : SmoothOfRelativeDimension 1 (structureMap G) := G.cover.smooth
  refine ⟨geom.1, geom.2.1, geometricallyIntegral_of_isAlgClosed (baseMap G),
    geometricallyIntegral_of_isAlgClosed (structureMap G), ?_, ?_, cusp_over G⟩
  · exact DiskFrameComparisonAdapterR0192.line_of_invertible _
      (G.hodge.invertible.pullback (inclusion k (level (commonN A)) G.data G.compact
        (G.test.disk (closedPoint k))))
  · exact DiskFrameComparisonAdapterR0192.line_of_invertible _
      (G.half.invertible.pullback G.cover.map)

#print axioms field_descent_geometry
end ArithmeticThetaArithmeticFieldR0231
