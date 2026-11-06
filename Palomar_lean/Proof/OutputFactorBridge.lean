module
public import ExtensionFactorBridge
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
noncomputable section
namespace PalomarOutput913
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaAdaptiveSolverR0230 ArithmeticThetaFieldImageR0233
open ArithmeticThetaScalarExtensionR0240 PalomarFactored882
open PalomarExtension908
def SolverCertificates : Prop :=
∀ (n h d : ℕ) (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ),
 (∀ i, ArithmeticThetaComputed.validGram (A i)) → ArithmeticThetaAdaptiveSolverR0230.Relations A R → 0 < h →
 ∃ o : ArithmeticThetaAdaptiveSolverR0230.Result h,
 ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧
 o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧
 o.matrix = ArithmeticThetaComputed.coefficientMatrix A o.cutoff ∧
 LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
  LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A o.cutoff).map (algebraMap ℚ ℂ)).mulVecLin)
def OutputFromCertificate : Prop :=
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
 (ι : k →+* l) (n h : ℕ), 0 < n → 0 < h →
 ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h),
 (∀ i, ArithmeticThetaComputed.validGram (A i)) →
 ∀ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A), ∀ (o : ArithmeticThetaAdaptiveSolverR0230.Result h),
 o.matrix = ArithmeticThetaComputed.coefficientMatrix A o.cutoff →
 LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
  LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A o.cutoff).map (algebraMap ℚ ℂ)).mulVecLin) → ArithmeticThetaScalarExtensionR0240.OutputImage ι G o

theorem solver_certificates : SolverCertificates := by
 intro n h d A R hA hR hh
 obtain ⟨o, ho, hc, hb⟩ := PalomarExtension908.solver_core n h d A R hA hR hh
 have hm : o.matrix = ArithmeticThetaComputed.coefficientMatrix A o.cutoff :=
  hc.1.trans (ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix n h o.cutoff A hA).1
 have hk : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
  LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A o.cutoff).map (algebraMap ℚ ℂ)).mulVecLin) := by
  rw [← hm]
  exact hc.2.1
 exact ⟨o,ho,hc,hb,hm,hk⟩

theorem output_from_certificate : OutputFromCertificate := by
  intro k l _ _ _ _ ι n h hn hh A hA G o hm hk
  have hi := scalar_extension_certified_image k l ι n h hn hh A hA G o.cutoff hk
  rcases o with ⟨B, M⟩
  dsimp only at hm hi ⊢
  subst M
  refine ⟨rfl, hi, ?_⟩
  simpa only [pivotIndices, coordinates, pivotCount, pivotCombination,
    ArithmeticThetaComputed.selectedIndex] using hi.2

theorem recover_from_components (hm : MatrixCore) (hl : CompactLevel)
 (hs : SolverCertificates) (ho : OutputFromCertificate) (hd : DiskTransport) (he : LevelTransport) :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaExtendedMetaplecticR0241.ExtendedLevel ι G ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := by
 intro n h d hn hh A hA R hR
 obtain ⟨hf, hL, heven, G, _⟩ := hm n h hn hh A hA
 have hlevel := hl _ _ _ G.root hL heven G.etale
 obtain ⟨o, hsolve, hcorrect, hbound, hmatrix, hkernel⟩ := hs n h d A R hA hR hh
 refine ⟨hf, G, o, (PalomarCyclotomic669.actualLevel_iff_original G.root).mp hlevel,
  hsolve, hcorrect, hbound, ?_⟩
 intro l _ _ ι
 exact ⟨(PalomarRemaining861.extendedLevel_iff_original ι G).mp
  (he _ l ι n h hn hh A hA G hlevel),
  ho _ l ι n h hn hh A hA G o hmatrix hkernel,
  hd _ l ι n h hn hh A hA G⟩

theorem original_cyclotomic_extended_modularity :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaExtendedMetaplecticR0241.ExtendedLevel ι G ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := recover_from_components matrix_core compact_level solver_certificates output_from_certificate disk_transport level_transport
end PalomarOutput913
