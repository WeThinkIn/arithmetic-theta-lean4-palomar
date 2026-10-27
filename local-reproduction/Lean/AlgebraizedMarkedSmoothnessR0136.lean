import AlgebraizedMarkedLineDefinitionsR0136
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk

/-! Smooth neighborhoods of the actual algebraized marked sections. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135

namespace AlgebraizedMarkedSmoothnessR0136
variable (k : Type u) [Field k] [CharZero k]

/-- The first-order marked reduction places the closed section point in the
regular model chart. The chart and its scalar map are the prescribed ones. -/
lemma closed_stalk_regular {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (i : Fin r) (a : kˣ)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i a s) :
    IsRegularLocalRing (M.X.presheaf.stalk (s (IsLocalRing.closedPoint (PowerSeries k)))) := by
  obtain ⟨b, hb⟩ := closedPoint_in_baseInclusion_all k 1
  obtain ⟨v, hv⟩ := SmoothMarkedSections.factor_open k r 1 hr (T.atlas 1) i a
  have hpoint : s (IsLocalRing.closedPoint (PowerSeries k)) =
      modelChart k M 1 i (rightLeg k 1 (v b)) := by
    rw [← hb]
    change (baseInclusion k 1 ≫ s) b = _
    rw [hs.2 1, ← hv]
    rfl
  rw [hpoint]
  exact (modelChart_stalk_regular k M hM i (rightLeg k 1 (v b))).1

/-- Flatness and the actual section split the local scalar map. Regularity of
the model stalk therefore gives smoothness at the closed section point. -/
lemma closed_mem_smoothLocus {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (i : Fin r) (a : kˣ)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i a s)
    [LocallyOfFinitePresentation M.p] :
    s (IsLocalRing.closedPoint (PowerSeries k)) ∈ M.p.smoothLocus := by
  let : Flat M.p := hM.2.1
  exact SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
    (PowerSeries k) M.p ⟨s, hs.1⟩ (closed_stalk_regular k M hM i a s hs)

end AlgebraizedMarkedSmoothnessR0136

/-- Every prescribed algebraized marked section is contained in an open
smooth over the power-series base, including its closed point. -/
theorem algebraized_marked_smoothness :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : Tower k r hr) (M : Model k T), IsModel k T M →
    ∀ (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X), MarkedLift k M i a s →
    ∃ U : M.X.Opens, (∀ x : baseScheme k, s x ∈ U) ∧ Smooth (U.ι ≫ M.p) := by
  intro k _ _ r hr _ T M hM i a s hs
  let := model_finitePresentation k M hM
  refine ⟨M.p.smoothLocus, ?_, ?_⟩
  · intro x
    exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open
      M.p.smoothLocus.isOpen
      (AlgebraizedMarkedSmoothnessR0136.closed_mem_smoothLocus k M hM i a s hs)
  · apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact x.property

end ArithmeticThetaAlgebraizedMarkedLineR0136

#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.algebraized_marked_smoothness
