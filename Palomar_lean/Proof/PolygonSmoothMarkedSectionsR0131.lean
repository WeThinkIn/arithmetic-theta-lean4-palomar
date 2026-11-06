module

public import PolygonCohomologyDefinitionsR0131
public import InfinitesimalPolygonFlatR0129
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Smooth marked sections of the actual finite cyclic polygon. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

namespace SmoothMarkedSections
variable (k : Type u) [Field k] [CharZero k]

lemma markedPoint_base (n : ℕ) (a : kˣ) :
    (markedPoint k n a).comp (base k n) = RingHom.id _ := by
  exact mkPoint_base _ _ _ _

lemma section_over (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (i : Fin r) (a : kˣ) : markedSection k r n hr D i a ≫ D.p = 𝟙 _ := by
  rw [markedSection, Category.assoc, D.chart_over]
  change Spec.map (CommRingCat.ofHom (markedPoint k n a)) ≫
    Spec.map (CommRingCat.ofHom (base k n)) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((markedPoint k n a).comp (base k n))) = _
  rw [markedPoint_base]
  exact Spec.map_id _

lemma factor_open (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (i : Fin r) (a : kˣ) :
    ∃ s : specR k n ⟶ specB k n true,
      s ≫ (rightLeg k n ≫ D.chart i) = markedSection k r n hr D i a := by
  have hu : IsUnit (markedPoint k n a (if true then coordX k n else coordY k n)) := by
    simp [markedPoint]
  refine ⟨Spec.map (CommRingCat.ofHom (openPoint (markedPoint k n a) true hu)), ?_⟩
  rw [← Category.assoc]
  congr 1
  rw [rightLeg, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (openPoint_restriction (markedPoint k n a) true hu)

lemma raw_base_smooth :
    ((algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))).Smooth := by
  obtain ⟨e, he, _⟩ := (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
  have hc : e.toRingHom.comp
      ((algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
        (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))) =
      LaurentPolynomial.C := by
    apply RingHom.ext
    intro z
    change e ((ArithmeticThetaNodeCharts.toXChart k)
      (ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.C z))) = _
    simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using
      RingHom.congr_fun he (MvPolynomial.C z)
  have hp : (Polynomial.C : PowerSeries k →+* Polynomial (PowerSeries k)).Smooth := by
    apply RingHom.smooth_algebraMap.mpr
    exact ⟨inferInstance, inferInstance⟩
  have hl : (algebraMap (Polynomial (PowerSeries k))
      (LaurentPolynomial (PowerSeries k))).Smooth :=
    RingHom.smooth_algebraMap.mpr
      (Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial (PowerSeries k)))
  have hC : (LaurentPolynomial.C : PowerSeries k →+* LaurentPolynomial (PowerSeries k)).Smooth := by
    convert hp.comp hl using 1
    ext z
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  let : Algebra.Smooth (PowerSeries k) (LaurentPolynomial (PowerSeries k)) :=
    RingHom.smooth_algebraMap.mp hC
  let ae : ArithmeticThetaNodeCharts.XChart k ≃ₐ[PowerSeries k]
      LaurentPolynomial (PowerSeries k) := AlgEquiv.ofRingEquiv (R := PowerSeries k)
      (f := e) (by
        intro z
        exact RingHom.congr_fun hc z)
  have ha : Algebra.Smooth (PowerSeries k) (ArithmeticThetaNodeCharts.XChart k) :=
    Algebra.Smooth.of_equiv ae.symm
  have hf := RingHom.smooth_algebraMap.mpr ha
  convert hf using 1

lemma open_smooth (n : ℕ) : Smooth (rightLeg k n ≫ structureMap k n) := by
  let f : PowerSeries k →+* RawOpen k true :=
    (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
  have hf : Smooth (Spec.map (CommRingCat.ofHom f)) :=
    HasRingHomProperty.Spec_iff.mpr (raw_base_smooth k)
  have sq := (trunc_isPushout f PowerSeries.X (openParameter k true) rfl n).op.map
    Scheme.Spec
  have hs := MorphismProperty.of_isPullback (P := @Smooth) sq.flip hf
  rw [rightLeg, structureMap, ← Spec.map_comp]
  change Smooth (Spec.map (CommRingCat.ofHom
    ((restriction k n true).comp (base k n))))
  change Smooth (Spec.map (CommRingCat.ofHom
    (truncMap f PowerSeries.X (openParameter k true) rfl n))) at hs
  have heq : (restriction k n true).comp (base k n) =
      truncMap f PowerSeries.X (openParameter k true) rfl n := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  rw [heq]
  exact hs

end SmoothMarkedSections

/-- The prescribed marked points are closed sections through the actual smooth x-open. -/
theorem polygon_smooth_marked_sections :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (E : B k n false ≃+* B k n true), IsAdjacent k n E →
      ∀ (D : Atlas k r n hr E) (i : Fin r) (a : kˣ),
      IsClosedImmersion (markedSection k r n hr D i a) ∧
      markedSection k r n hr D i a ≫ D.p = 𝟙 (specR k n) ∧
      Smooth (rightLeg k n ≫ structureMap k n) ∧
      (∃ s : specR k n ⟶ specB k n true,
        s ≫ (rightLeg k n ≫ D.chart i) = markedSection k r n hr D i a) := by
  intro k _ _ r n hr _ E hE D i a
  have hsec := SmoothMarkedSections.section_over k r n hr D i a
  have : IsSeparated D.p := D.isSeparated hE
  have : IsClosedImmersion (markedSection k r n hr D i a ≫ D.p) := by
    rw [hsec]
    infer_instance
  exact ⟨IsClosedImmersion.of_comp _ D.p, hsec,
    SmoothMarkedSections.open_smooth k n,
    SmoothMarkedSections.factor_open k r n hr D i a⟩

end ArithmeticThetaPolygonCohomologyR0131
