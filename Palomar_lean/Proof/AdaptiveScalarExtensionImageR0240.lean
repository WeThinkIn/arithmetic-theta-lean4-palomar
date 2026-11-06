module

public import ScalarExtensionSectionImageR0240
public import AdaptiveUniversalSolverR0230
public import CyclotomicMatrixModularityR0239

@[expose] public section

/-! The actual adaptive output for the same scalar-extended arithmetic family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaAdaptiveSolverR0230 ArithmeticThetaFieldImageR0233

/-- The solver's matrix equality transports every dependent pivot and coordinate
index, not merely its rank. -/
private theorem outputImage_of_correct
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (o : Result h) (hc : Correct A o) : OutputImage ι G o := by
  have hm : o.matrix = ArithmeticThetaComputed.coefficientMatrix A o.cutoff :=
    hc.1.trans (ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix
      n h o.cutoff A hA).1
  have hk : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A o.cutoff).map
        (algebraMap ℚ ℂ)).mulVecLin) := by
    rw [← hm]
    exact hc.2.1
  have hi := scalar_extension_certified_image k l ι n h hn hh A hA G o.cutoff hk
  rcases o with ⟨B, M⟩
  dsimp only at hm hi ⊢
  subst M
  refine ⟨rfl, hi, ?_⟩
  simpa only [pivotIndices, coordinates, pivotCount, pivotCombination,
    ArithmeticThetaComputed.selectedIndex] using hi.2

theorem adaptive_scalar_extension_image :
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ∀ (d : ℕ) (R : Matrix (Fin h) (Fin d) ℚ), ArithmeticThetaAdaptiveSolverR0230.Relations A R → ∃ o : ArithmeticThetaAdaptiveSolverR0230.Result h, ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ o.cutoff ∈ ArithmeticThetaAdaptiveSolverR0230.schedule (ArithmeticThetaAdaptiveSolverR0230.bound A) ∧ (o.cutoff = ArithmeticThetaAdaptiveSolverR0230.bound A ∨ ArithmeticThetaAdaptiveSolverR0230.early A R o.cutoff = true) ∧ (∀ b ∈ ArithmeticThetaAdaptiveSolverR0230.schedule (ArithmeticThetaAdaptiveSolverR0230.bound A), b < o.cutoff → ArithmeticThetaAdaptiveSolverR0230.early A R b = false) ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := by
  intro k l _ _ _ _ ι n h hn hh A hA G d R hR
  obtain ⟨o, ho, hb, hc, hs, he, hf⟩ :=
    adaptive_universal_solver n h d A R hA hR hh
  refine ⟨o, ho, hc, outputImage_of_correct k l ι n h hn hh A hA G o hc,
    hb, hs, he, hf, ?_⟩
  obtain ⟨D, hframe, hdom⟩ := scalar_extension_disk_frame k l ι n h hn hh A hA G
  exact ⟨D, hframe, hdom, scalar_extension_expansion k l ι n h hn hh A hA G D⟩

theorem cyclotomic_extension_output :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := by
  intro n h d hn hh A hA R hR
  obtain ⟨hfinite, G, hlevel, _⟩ :=
    ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity n h hn hh A hA
  obtain ⟨o, ho, hb, hc, _⟩ := adaptive_universal_solver n h d A R hA hR hh
  refine ⟨hfinite, G, o, hlevel, ho, hc, hb, ?_⟩
  intro l _ _ ι
  obtain ⟨o', ho', _, himage, _, _, _, _, hdisk⟩ :=
    adaptive_scalar_extension_image (CyclotomicField (level (commonN A)) ℚ)
      l ι n h hn hh A hA G d R hR
  have he : o' = o := Option.some.inj (ho'.symm.trans ho)
  subst o'
  exact ⟨himage, hdisk⟩

#print axioms adaptive_scalar_extension_image
#print axioms cyclotomic_extension_output
end ArithmeticThetaScalarExtensionR0240
