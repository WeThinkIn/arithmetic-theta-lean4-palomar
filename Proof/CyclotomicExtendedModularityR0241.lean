module

public import ExtendedActualMetaplecticLevelR0241

@[expose] public section

/-! One cyclotomic family and one solver output over every coefficient extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241

/-- Add the actual target-field metaplectic level to the unchanged arithmetic
family, certified output, and complete expansions supplied by r0240. -/
theorem cyclotomic_extended_modularity :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaExtendedMetaplecticR0241.ExtendedLevel ι G ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := by
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
