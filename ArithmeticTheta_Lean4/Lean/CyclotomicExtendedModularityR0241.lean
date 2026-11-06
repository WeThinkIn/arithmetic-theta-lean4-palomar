import ExtendedActualMetaplecticLevelR0241

/-! One cyclotomic family and one solver output over every coefficient extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241

open ArithmeticThetaLatticeSectionsR0188 (Matrices)
open ArithmeticThetaComputed (validGram)
open ArithmeticThetaCyclotomicModularityR0239 (CoefficientField)
open ArithmeticThetaArithmeticFieldR0231 (MatrixData)
open ArithmeticThetaAdaptiveSolverR0230 (Relations Result solve Correct bound)
open ArithmeticThetaScalarExtensionR0240 (OutputImage DiskLift line frame Expansion)

/-- Add the actual target-field metaplectic level to the unchanged arithmetic
family, certified output, and complete expansions supplied by r0240. -/
theorem cyclotomic_extended_modularity :
    ∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : Matrices n h),
      (∀ i, validGram (A i)) →
      ∀ R : Matrix (Fin h) (Fin d) ℚ, Relations A R →
      FiniteDimensional ℚ (CoefficientField A) ∧
      ∃ (G : MatrixData (CoefficientField A) A) (o : Result h),
        ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧
        solve A R = some o ∧ Correct A o ∧ o.cutoff ≤ bound A ∧
        ∀ (l : Type) [Field l] [CharZero l] (ι : CoefficientField A →+* l),
          ExtendedLevel ι G ∧ OutputImage ι G o ∧
          ∃ D : DiskLift ι G,
            ArithmeticThetaRelativeDiscriminantR0171.IsFrame
              ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (line ι G))
              ⊤ (frame ι G D) ∧
            AlgebraicGeometry.IsDominant
              (CategoryTheory.CategoryStruct.comp
                (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧
            Expansion ι G D := by
  intro n h d hn hh A hA R hR
  obtain ⟨hfinite, G, o, hlevel, hsolve, hcorrect, hbound, hext⟩ :=
    ArithmeticThetaScalarExtensionR0240.cyclotomic_extension_output
      n h d hn hh A hA R hR
  refine ⟨hfinite, G, o, hlevel, hsolve, hcorrect, hbound, ?_⟩
  intro l _ _ ι
  exact ⟨extended_actual_metaplectic_level _ l ι n h hn hh A hA G hlevel,
    hext l ι⟩

#print axioms cyclotomic_extended_modularity
end ArithmeticThetaExtendedMetaplecticR0241
