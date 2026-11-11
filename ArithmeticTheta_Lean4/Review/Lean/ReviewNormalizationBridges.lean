import ReviewNormalizationSource

/-! Exact preservation of the original Tate normalization maps and sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaReview.Normalization

/-- The comparison extracted into the generic interface is the original
canonical punctured-disk comparison, with no scalar change. -/
theorem source_chart_comparison :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ)
      (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
      (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D)
      (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X)
      (T : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X),
      (sourceChart H T).comparison =
        ArithmeticThetaBoundaryHodgeR0182.diskGenericIso k L H T := by
  intro k _ _ L D X H T
  rfl

/-- Every displayed normalization datum remains the exact original datum.
The same `u` supplies both the interior object and its canonical comparison. -/
theorem source_normalization_preserves :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ)
      (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h)
      (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
      (u : ArithmeticThetaCompactModularityR0209.Universal G.root),
      (sourceNormalization G u).map =
          ArithmeticThetaCompactModularityR0209.compactMap G.root ∧
      (sourceNormalization G u).square =
          ArithmeticThetaCompactModularityR0209.compactSquare G.root ∧
      (sourceNormalization G u).normalized.generator = G.frame.generator ∧
      (sourceNormalization G u).chart.differential = G.test.differential ∧
      (sourceNormalization G u).chart.comparison =
        ArithmeticThetaBoundaryHodgeR0182.diskGenericIso k
          (ArithmeticThetaCompactUnaryR0183.level
            (ArithmeticThetaLatticeSectionsR0188.commonN A)) G.hodge G.test := by
  intro k _ _ n h A G u
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end ArithmeticThetaReview.Normalization
