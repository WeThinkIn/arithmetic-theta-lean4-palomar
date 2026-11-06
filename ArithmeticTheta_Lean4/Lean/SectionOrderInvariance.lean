import SectionOrderDefinitions

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

universe u v
noncomputable section

namespace ArithmeticThetaSectionOrder

/-- The generic coefficients of an actual section transform by the actual
unit relating its local frames on their overlap. -/
theorem sectionCoefficient_transition
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) {ι : Type v}
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i j : ι) :
    sectionCoefficient X H (C.opens i) (C.frame i) s =
      X.germToFunctionField (C.opens i ⊓ C.opens j) (overlapUnit C i j) *
        sectionCoefficient X H (C.opens j) (C.frame j) s := by
  have h := global_sections_compatible C s i j
  change H.presheaf.map (homOfLE inf_le_left).op
      ((C.frame i).equiv _ le_rfl (coordinate C s i)) =
    H.presheaf.map (homOfLE inf_le_right).op
      ((C.frame j).equiv _ le_rfl (coordinate C s j)) at h
  rw [(C.frame i).naturality, (C.frame j).naturality,
    transition_apply ((C.frame i).equiv _ inf_le_left)
      ((C.frame j).equiv _ inf_le_right)] at h
  have hc := congrArg (X.germToFunctionField (C.opens i ⊓ C.opens j))
    (((C.frame i).equiv _ inf_le_left).injective h)
  rw [map_mul, germ_restrict, germ_restrict] at hc
  exact hc

theorem local_order_frame_invariant
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (ι : Type v) (C : NormalFrameCover X H ι)
    (s : Γ(H, ⊤)) (i j : ι) (x : X)
    (hi : x ∈ C.opens i) (hj : x ∈ C.opens j) :
    localOrder X H C s i x = localOrder X H C s j x := by
  unfold localOrder
  rw [sectionCoefficient_transition X H C s i j]
  by_cases hz : sectionCoefficient X H (C.opens j) (C.frame j) s = 0
  · rw [hz, mul_zero]
  · rw [Scheme.ord_mul
      (((overlapUnit C i j).isUnit.map
        (X.germToFunctionField (C.opens i ⊓ C.opens j)).hom).ne_zero) hz,
      Scheme.ord_of_isUnit (overlapUnit C i j).isUnit ⟨hi, hj⟩, zero_add]

/-- A regular function has nonnegative totalized scheme order on its domain. -/
theorem regular_coefficient_order_nonnegative
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (x : X) (hx : x ∈ U) :
    0 ≤ Scheme.ord (X.germToFunctionField U a) x := by
  by_cases ha : a = 0
  · simp [ha]
  · have hone : Scheme.ord (1 : X.functionField) x = 0 := by
      simpa using (Scheme.ord_of_isUnit (X := X)
        (f := (1 : Γ(X, U))) isUnit_one hx)
    have h := Scheme.ord_le_smul hx ha (1 : X.functionField)
    simpa only [hone, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one] using h

theorem local_order_nonnegative
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (ι : Type v) (C : NormalFrameCover X H ι)
    (s : Γ(H, ⊤)) (i : ι) (x : X) (hi : x ∈ C.opens i) :
    0 ≤ localOrder X H C s i x := by
  exact regular_coefficient_order_nonnegative X (C.opens i)
    (sectionCoordinate X H (C.opens i) (C.frame i) s) x hi

end ArithmeticThetaSectionOrder

#print axioms ArithmeticThetaSectionOrder.local_order_frame_invariant
#print axioms ArithmeticThetaSectionOrder.local_order_nonnegative
