import ReviewFramedFamily

/-!
# Review statements of the original arithmetic theta results

These are proved projections of the original construction theorems. The original
theorems and all construction witnesses remain unchanged. Here the conclusion
exposes the compact modular curve, its canonical normalized frame and the actual
sections, without requiring the reader to interpret an atlas or a quotient
construction first. One family is chosen before quantifying over all cutoffs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaReview.Geometry
open ArithmeticThetaLatticeSectionsR0188 (Matrices commonN)
open ArithmeticThetaCompactUnaryR0183 (level)
open ArithmeticThetaSharpKernelR0195 (normCount cutoff)
open ArithmeticThetaCyclotomicModularityR0239 (CoefficientField)
open ArithmeticThetaConservativeKernelR0189 (CutoffSpecification PrefixDeterminesKernel)
open ArithmeticThetaDegreeAssembly (CertifiedImageData)
open ArithmeticThetaComputed (validGram thetaMap)
open ArithmeticThetaFieldImageR0233 (SectionImage)

/-- Explicit preservation, not an unrelated realization with the same series.
The eight equalities retain the actual compact curve, scalar map, half line,
disk, frame, sections, compact square and normalized Hodge generator. -/
theorem matrix_family_review :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ) (A : Matrices n h)
      (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A),
      ArithmeticThetaCompactModularityR0209.ActualLevel G.root →
      ∃ F : FramedFamily k (level (commonN A)) (2 * 2 ^ (normCount A - 1)) n h,
        Realizes F A ∧
        (∀ B : ℕ,
          SectionImage k A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections ↔
            SectionImage k A B F.curve.structureMap F.sections) ∧
        F.curve.space = G.cover.space ∧
        HEq F.curve.structureMap (ArithmeticThetaArithmeticFieldR0231.structureMap G) ∧
        HEq F.curve.half (ArithmeticThetaArithmeticFieldR0231.half G) ∧
        HEq F.disk G.frame.disk ∧ HEq F.frame G.frame.frame ∧ HEq F.sections G.sections ∧
        HEq F.normalization.square (ArithmeticThetaCompactModularityR0209.compactSquare G.root) ∧
        HEq F.normalization.normalized.generator G.frame.generator := by
  intro k _ _ n h A G hG
  classical
  obtain ⟨hgeometry, u, C, hforget, hstack, hcomparison, hlevel⟩ := hG
  let F := familyOfData G hgeometry u C hforget hstack hcomparison hlevel
  refine ⟨F, ?_, ?_, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl⟩
  · intro c
    exact G.expansion c
  · intro B
    rfl

/-- The sharp modularity conclusion, with a normalized actual finite level
over the prescribed number field and one family valid at every larger cutoff.
The factor two in the level rank comes from the square-root torsor; the sharp
coefficient bound itself is exactly the original bound. -/
theorem cyclotomic_modularity_review :
    ∀ (n h : ℕ), 0 < n → 0 < h → ∀ A : Matrices n h,
      (∀ i, validGram (A i)) →
      FiniteDimensional ℚ (CoefficientField A) ∧
      ∃ F : FramedFamily (CoefficientField A) (level (commonN A))
          (2 * 2 ^ (normCount A - 1)) n h,
        Realizes F A ∧
        ∀ B : ℕ, cutoff A ≤ B →
          SectionImage (CoefficientField A) A B F.curve.structureMap F.sections := by
  intro n h hn hh A hA
  obtain ⟨hfinite, G, hlevel, himage⟩ :=
    ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity n h hn hh A hA
  obtain ⟨F, hrealizes, hsame, _⟩ := matrix_family_review _ n h A G hlevel
  exact ⟨hfinite, F, hrealizes, fun B hB => (hsame B).mp (himage B hB)⟩

/-- The conservative bound, every finite kernel and image conclusion, the
rank-zero formula, and the same normalized geometric family for all cutoffs. -/
theorem conservative_image_review :
    ∀ (n h : ℕ), 0 < h → ∀ A : Matrices n h,
      (∀ i, validGram (A i)) →
      ∃ B : ℕ,
        CutoffSpecification A B ∧
        (∀ Bp : ℕ, B ≤ Bp → PrefixDeterminesKernel A Bp) ∧
        (n = 0 → ∀ c : Fin h → ℂ, thetaMap A c = PowerSeries.C (∑ i, c i)) ∧
        (∀ Bp : ℕ, B ≤ Bp → CertifiedImageData A Bp) ∧
        (0 < n →
          FiniteDimensional ℚ (CoefficientField A) ∧
          ∃ F : FramedFamily (CoefficientField A) (level (commonN A))
              (2 * 2 ^ (normCount A - 1)) n h,
            Realizes F A ∧
            ∀ Bp : ℕ, B ≤ Bp →
              SectionImage (CoefficientField A) A Bp F.curve.structureMap F.sections) := by
  intro n h hh A hA
  obtain ⟨B, hB, hkernel, hzero, himage, hgeometry⟩ :=
    ArithmeticThetaFullSourceR0268.conservative_image_consumer n h hh A hA
  refine ⟨B, hB, hkernel, hzero, himage, ?_⟩
  intro hn
  obtain ⟨hfinite, G, hlevel, hsections⟩ := hgeometry hn
  obtain ⟨F, hrealizes, hsame, _⟩ := matrix_family_review _ n h A G hlevel
  exact ⟨hfinite, F, hrealizes, fun Bp hBp => (hsame Bp).mp (hsections Bp hBp)⟩

end ArithmeticThetaReview.Geometry
