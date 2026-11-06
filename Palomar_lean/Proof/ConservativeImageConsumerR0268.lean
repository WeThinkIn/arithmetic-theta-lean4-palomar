module

public import ConservativeMatrixKernelR0189
public import EarlyCertificateAssembly
public import CyclotomicMatrixModularityR0239
public import CertifiedPrefixFieldImageR0240

@[expose] public section

/-! Exact conservative-bound image data, with one actual cyclotomic family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFullSourceR0268
namespace ConservativeImageConsumer
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaFieldImageR0233
open ArithmeticThetaCyclotomicModularityR0239
open ArithmeticThetaPullback

/-- Transfer a certified prefix through the actual completed-expansion relation
 equivalence. The sections and the structural scalar map are unchanged. -/
private theorem section_image_of_certificate
    (k : Type) [Field k] [CharZero k] (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (A : Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (B : ℕ)
    (hcert : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin)) :
    SectionImage k A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  classical
  let b := ArithmeticThetaArithmeticFieldR0231.structureMap G
  have hr := arithmetic_section_relations k n h hn hh A hA G
  obtain ⟨hk, hi, hspan, hc, hu⟩ := ArithmeticThetaScalarExtensionR0240.certified_prefix_field_image k n h A hA B hcert
  have hp (c : Fin h → k) (d : Fin (pivotCount A B) → k) :
      combination k b G.sections c = pivotCombination k A B b G.sections d ↔
        seriesCombination k A c = seriesPivot k A B d := by
    change combination k b G.sections c =
      ∑ t, baseScalar k b (d t) • G.sections (ArithmeticThetaComputed.selectedIndex A B t) ↔ _
    rw [← FieldSectionImageProof.combination_insert,
      FieldSectionImageProof.equality k b G.sections A hr]
    exact congrArg (fun z => seriesCombination k A c = z)
      (FieldSeriesImageProof.inserted k A B d) |>.to_iff
  have hs (j : Fin h) (d : Fin (pivotCount A B) → k) :
      G.sections j = pivotCombination k A B b G.sections d ↔
        ArithmeticThetaArithmeticFieldR0231.theta k (A j) = seriesPivot k A B d := by
    have he := hp (Pi.single j 1) d
    rw [FieldSectionImageProof.combination_single] at he
    change _ ↔ FieldSeriesImageProof.linear k A (Pi.single j 1) = _ at he
    rw [FieldSeriesImageProof.single] at he
    exact he
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hr c).trans (hk c)
  · intro d hd
    apply hi d
    have hz := (hr (FieldSeriesImageProof.insert k
      (ArithmeticThetaComputed.selectedIndex A B) d)).mp (by
        simpa only [FieldSectionImageProof.combination_insert, pivotCombination] using hd)
    change FieldSeriesImageProof.linear k A _ = 0 at hz
    rwa [FieldSeriesImageProof.inserted] at hz
  · intro c
    obtain ⟨d, hd, hud⟩ := hspan c
    exact ⟨d, (hp c d).mpr hd, fun e he => hud e ((hp c e).mp he)⟩
  · intro j
    exact (hs j _).mpr (hc j)
  · intro j d hd
    exact hu j d ((hs j _).mp hd)
end ConservativeImageConsumer

/-- The exact conservative cutoff simultaneously certifies all formal image
 data and the same compact cyclotomic sections at every larger prefix. -/
theorem conservative_image_consumer :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ B : ℕ, (if n = 0 then B = 0 else ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ B = ArithmeticThetaConservativeKernelR0189.cutoff A U ∧ (B : ℚ) = (n : ℚ) * ((ArithmeticThetaCompactUnaryR0183.exponent (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℕ) : ℚ)^U.count * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / 48) ∧ (∀ B' : ℕ, B ≤ B' → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) ∧ (∀ B' : ℕ, B ≤ B' → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j) ∧ (0 < n → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B' : ℕ, B ≤ B' → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B' (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections) := by
  intro n h hh A hA
  classical
  obtain ⟨B, hB, hker, hzero⟩ :=
    ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel n h hh A hA
  refine ⟨B, hB, hker, hzero, ?_, ?_⟩
  · intro B' hBB
    apply ArithmeticThetaDegreeAssembly.certified_theta_image_data n h B' A hA
      (LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) le_rfl
    rw [hker B' hBB]
    exact ArithmeticThetaLinearAlgebra.rational_matrix_nullity (B' + 1) h
      (ArithmeticThetaComputed.coefficientMatrix A B')
  · intro hn
    obtain ⟨hfinite, G, hlevel, _⟩ :=
      ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity n h hn hh A hA
    refine ⟨hfinite, G, hlevel, ?_⟩
    intro B' hBB
    exact ConservativeImageConsumer.section_image_of_certificate _ n h hn hh A hA G B'
      (hker B' hBB)

#print axioms conservative_image_consumer
end ArithmeticThetaFullSourceR0268
