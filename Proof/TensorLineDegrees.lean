module

public import TensorSectionDivisors
public import LineIsomorphismDivisors
public import SectionDivisorComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree

universe u v w
noncomputable section

namespace ArithmeticThetaDegreeAssembly

/-- A normal frame cover supplies genuine local sheaf trivializations. -/
theorem isLineBundle_of_normalFrameCover
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    {ι : Type v} (C : NormalFrameCover X H ι) : IsLineBundle X H := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (C.covers (show x ∈ (⊤ : X.Opens) by trivial))
  exact ⟨C.opens i, hi, ⟨localFrameIso X H (C.opens i) (C.frame i)⟩⟩

/-- The actual tensor power remains locally free of rank one, including power zero. -/
theorem tensorPower_isLineBundle
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    {ι : Type v} (C : NormalFrameCover X H ι) (n : ℕ) :
    IsLineBundle X (tensorPower X H n) :=
  isLineBundle_of_normalFrameCover X (tensorPower X H n) (powerCover X H C n)

/-- Residue-weighted degree commutes with natural scaling of divisors. -/
theorem weightedDegree_nsmul
    (X : Scheme.{u}) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) (D : X →₀ ℤ) :
    weightedDegree k f (n • D) = (n : ℤ) * weightedDegree k f D := by
  induction n with
  | zero => simp [weightedDegree]
  | succ n ih =>
      rw [succ_nsmul, weightedDegree_add, ih]
      push_cast
      ring

/-- Any nonzero section of the genuine tensor power has the scaled line degree. -/
theorem tensor_power_fixed_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (H : X.Modules) (hH : IsLineBundle X H)
    (ι : Type v) (C : NormalFrameCover X H ι) (n : ℕ)
    (κ : Type w) (E : NormalFrameCover X (tensorPower X H n) κ)
    (s : Γ(H, ⊤)) (t : Γ(tensorPower X H n, ⊤)) (D Dn : X →₀ ℤ) :
    s ≠ 0 → t ≠ 0 → MatchesSectionOrder X H C s D →
    MatchesSectionOrder X (tensorPower X H n) E t Dn →
    weightedDegree k f Dn = (n : ℤ) * weightedDegree k f D := by
  intro hs ht hD hDn
  have hP := tensorPower_isLineBundle X H C n
  obtain ⟨hp, hDp⟩ := tensor_power_divisor X H hH ι C n s D hs hD
  have he := line_isomorphism_divisor X (tensorPower X H n) (tensorPower X H n)
    hP hP ι κ (powerCover X H C n) E (Iso.refl _)
    (tensorPowerSection X H n ⊤ s) (n • D) hp hDp
  have hDE : MatchesSectionOrder X (tensorPower X H n) E
      (tensorPowerSection X H n ⊤ s) (n • D) := by
    simpa using he.2
  calc
    weightedDegree k f Dn = weightedDegree k f (n • D) :=
      ArithmeticThetaSectionCompletion.section_fixed_degree X k f hcurve
        (tensorPower X H n) hP κ E t (tensorPowerSection X H n ⊤ s)
        Dn (n • D) ht hp hDn hDE
    _ = (n : ℤ) * weightedDegree k f D := weightedDegree_nsmul X k f n D

/-- A specified square-line isomorphism gives twice the reference line degree. -/
theorem square_line_fixed_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (H J : X.Modules)
    (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    (ι : Type v) (κ : Type w) (C : NormalFrameCover X H ι)
    (E : NormalFrameCover X J κ) (e : tensorPower X H 2 ≅ J)
    (s : Γ(H, ⊤)) (t : Γ(J, ⊤)) (D DJ : X →₀ ℤ) :
    s ≠ 0 → t ≠ 0 → MatchesSectionOrder X H C s D →
    MatchesSectionOrder X J E t DJ →
    2 * weightedDegree k f D = weightedDegree k f DJ := by
  intro hs ht hD hDJ
  have hP := tensorPower_isLineBundle X H C 2
  obtain ⟨hp, hDp⟩ := tensor_power_divisor X H hH ι C 2 s D hs hD
  obtain ⟨he, hDe⟩ := line_isomorphism_divisor X (tensorPower X H 2) J
    hP hJ ι κ (powerCover X H C 2) E e
    (tensorPowerSection X H 2 ⊤ s) (2 • D) hp hDp
  calc
    2 * weightedDegree k f D = weightedDegree k f (2 • D) :=
      (weightedDegree_nsmul X k f 2 D).symm
    _ = weightedDegree k f DJ :=
      ArithmeticThetaSectionCompletion.section_fixed_degree X k f hcurve J hJ κ E
        (e.hom.app ⊤ (tensorPowerSection X H 2 ⊤ s)) t (2 • D) DJ he ht hDe hDJ

end ArithmeticThetaDegreeAssembly

#print axioms ArithmeticThetaDegreeAssembly.tensor_power_fixed_degree
#print axioms ArithmeticThetaDegreeAssembly.square_line_fixed_degree
