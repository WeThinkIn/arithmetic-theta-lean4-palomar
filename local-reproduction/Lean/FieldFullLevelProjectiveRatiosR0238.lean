import FullLevelProjectiveRatiosR0194

/-! Complete projective unary ratios over the original coefficient field. -/
set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- The accepted arithmetic theta construction gives every complete normalized
unary ratio on the original full-level component over any characteristic-zero
field containing the specified primitive root, without a field extension. -/
theorem field_full_level_projective_ratios :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m), Even m →
      ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m))
        (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D),
      ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X) (ζ : k),
      IsPrimitiveRoot ζ (2*m) →
      ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) ζ V.level →
      ArithmeticThetaSharpCoverR0194.ProjectiveRatios k (2*m) m hm D X V := by
  intro k _ _ m hm he D X V ζ hζ hmark
  obtain ⟨f, θ, hfac, hdom, hθ⟩ := component_field_factor k (2*m) D X V
  apply (projectiveRatios_iff_field_range k m hm D X V f hfac hdom θ hθ).mpr
  have hb := (component_field_map_over k (2*m) D X V f hfac θ hθ).2
  let z : kˣ := (hζ.isUnit (Nat.mul_pos (by decide) hm).ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit (Nat.mul_pos (by decide) hm).ne').unit_spec
  have hzr : IsPrimitiveRoot (z : k) (2*m) := by simpa only [hz] using hζ
  have hzm : CanonicalMarking k (2*m) (z : k) V.level := by simpa only [hz] using hmark
  obtain ⟨Q⟩ := LocalTheta.markedModel_exists k m hm he V.level z hzr hzm
  obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩ := component_symmetric_lifts k m hm he D X V ζ hζ hmark
  exact exact_unary_field_range k m hm D X (V.disk (closedPoint k)) V θ hb z hzr he Q α β hα hβ

#print axioms field_full_level_projective_ratios
end ArithmeticThetaArithmeticCommonCoverR0238
