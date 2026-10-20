module

public import ScalarExtensionDefinitionsR0240
public import FieldComponentGeometryR0237
public import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
public import Theorems.Thm_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero
public import Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper

@[expose] public section

/-! Geometry of the same arithmetic cover after coefficient extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTensorPower
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaSquareLinesR0192

namespace GeometryProof

/-- Constants are detected by the specified rational section. Properness and
integrality give the constants theorem; smoothness then gives the geometric
irreducibility criterion. Characteristic zero gives geometric reducedness. -/
theorem geometricallyIntegral_of_point (k : Type) [Field k] [CharZero k]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [Smooth f] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyIntegral f := by
  have hb := P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section
    k f s hs
  letI : GeometricallyIrreducible f :=
    (geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth f).2 hb
  letI : GeometricallyReduced f := geometricallyReduced_of_isReduced_of_charZero k f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

variable {k : Type} [Field k] [CharZero k] {n h : ℕ} {A : Matrices n h}

lemma frame_over (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    G.frame.disk ≫ ArithmeticThetaArithmeticFieldR0231.structureMap G = diskStructure k := by
  change G.frame.disk ≫ (G.cover.map ≫
    (inclusion k (level (commonN A)) G.data G.compact
      (G.test.disk (closedPoint k)) ≫ G.compact.projection)) = _
  rw [← Category.assoc G.cover.map, ← Category.assoc G.frame.disk, G.frame.triangle]
  exact G.test.extends_eq.1

lemma cusp_over (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ArithmeticThetaArithmeticFieldR0231.cusp G ≫
      ArithmeticThetaArithmeticFieldR0231.structureMap G = 𝟙 _ := by
  rw [ArithmeticThetaArithmeticFieldR0231.cusp, Category.assoc, frame_over]
  change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))) = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap k (PowerSeries k)) ≫
      CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k) =
      𝟙 (CommRingCat.of k) := by
    ext x
    simp
  rw [he, Spec.map_id]

/-- Descent geometry over the original field, using the centre of the given disk. -/
theorem descent_geometry (hn : 0 < n) (hh : 0 < h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ArithmeticThetaArithmeticFieldR0231.DescentGeometry G := by
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
  have geom := ArithmeticThetaArithmeticHalfLinesR0237.field_component_geometry
    k (level (commonN A)) hL heven G.data G.compact (G.test.disk (closedPoint k))
  letI : IsProper (ArithmeticThetaArithmeticFieldR0231.baseMap G) := geom.1
  letI : SmoothOfRelativeDimension 1 (ArithmeticThetaArithmeticFieldR0231.baseMap G) := geom.2.1
  letI : IsIntegral G.cover.space := G.cover.integral
  letI : IsProper (ArithmeticThetaArithmeticFieldR0231.structureMap G) := G.cover.proper
  letI : SmoothOfRelativeDimension 1 (ArithmeticThetaArithmeticFieldR0231.structureMap G) :=
    G.cover.smooth
  have hc := cusp_over G
  have hb : (ArithmeticThetaArithmeticFieldR0231.cusp G ≫ G.cover.map) ≫
      ArithmeticThetaArithmeticFieldR0231.baseMap G = 𝟙 _ := by
    simpa only [Category.assoc] using hc
  refine ⟨geom.1, geom.2.1,
    geometricallyIntegral_of_point k (ArithmeticThetaArithmeticFieldR0231.baseMap G)
      (ArithmeticThetaArithmeticFieldR0231.cusp G ≫ G.cover.map) hb,
    geometricallyIntegral_of_point k (ArithmeticThetaArithmeticFieldR0231.structureMap G)
      (ArithmeticThetaArithmeticFieldR0231.cusp G) hc, ?_, ?_, hc⟩
  · exact DiskFrameComparisonAdapterR0192.line_of_invertible _
      (G.hodge.invertible.pullback (inclusion k (level (commonN A)) G.data G.compact
        (G.test.disk (closedPoint k))))
  · exact DiskFrameComparisonAdapterR0192.line_of_invertible _
      (G.half.invertible.pullback G.cover.map)

end GeometryProof

/-- The original arithmetic cover and its categorical coefficient extension
retain their structural maps, rational cusp, and actual pulled-back line. -/
theorem scalar_extension_geometry
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ArithmeticThetaArithmeticFieldR0231.DescentGeometry G ∧
    IsProper (structureMap ι G) ∧ SmoothOfRelativeDimension 1 (structureMap ι G) ∧
    GeometricallyIntegral (structureMap ι G) ∧
    Scheme.Modules.IsInvertible (line ι G) ∧
    ArithmeticThetaNormalizedSections.IsLineBundle (Space ι G)
      (tensorPower (Space ι G) (line ι G) n) := by
  have hg := GeometryProof.descent_geometry hn hh hA G
  letI : IsProper (ArithmeticThetaArithmeticFieldR0231.structureMap G) := G.cover.proper
  letI : SmoothOfRelativeDimension 1 (ArithmeticThetaArithmeticFieldR0231.structureMap G) :=
    G.cover.smooth
  letI : GeometricallyIntegral (ArithmeticThetaArithmeticFieldR0231.structureMap G) := hg.2.2.2.1
  have hi : Scheme.Modules.IsInvertible (line ι G) :=
    (G.half.invertible.pullback G.cover.map).pullback (projection ι G)
  refine ⟨hg, inferInstance, inferInstance, inferInstance, hi, ?_⟩
  exact DiskFrameComparisonAdapterR0192.line_of_invertible _
    (ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorPower_invertible
      (line ι G) hi n)

#print axioms GeometryProof.geometricallyIntegral_of_point
#print axioms scalar_extension_geometry
end ArithmeticThetaScalarExtensionR0240
