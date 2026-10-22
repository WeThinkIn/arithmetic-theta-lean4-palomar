module

public import AdaptiveSolverDefinitionsR0230
public import LDLThetaPrefixR0229
public import EarlyCertificateAssembly

@[expose] public section

/-! Exact executable certification from arbitrary finite full-series relation
columns. Repeated and dependent columns are measured by rank. -/
set_option autoImplicit false

namespace ArithmeticThetaAdaptiveSolverR0230
namespace ExecutableRelationCertificate

private def relationSpace {h d : ℕ} (R : Matrix (Fin h) (Fin d) ℚ) :
    Submodule ℂ (Fin h → ℂ) :=
  Submodule.span ℂ (Set.range (R.map (algebraMap ℚ ℂ)).col)

private theorem relationSpace_le {n h d : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (hR : Relations A R) :
    relationSpace R ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact hR j

private theorem relationSpace_finrank {h d : ℕ} (R : Matrix (Fin h) (Fin d) ℚ) :
    Module.finrank ℂ (relationSpace R) = R.rank := by
  rw [relationSpace, ← Matrix.rank_eq_finrank_span_cols]
  exact ArithmeticThetaLinearAlgebra.rational_matrix_rank h d R

private theorem relation_rank_le_nullity {n h d : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (hv : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (hR : Relations A R) (B : ℕ) :
    R.rank ≤ h - (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).rank := by
  have hinc : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ≤
      LinearMap.ker ((ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin := by
    intro c hc
    rw [← (ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix n h B A hv).2.2]
    change ArithmeticThetaComputed.prefixMap B (ArithmeticThetaComputed.thetaMap A c) = 0
    rw [show ArithmeticThetaComputed.thetaMap A c = 0 from hc, map_zero]
  have hd := Submodule.finrank_mono ((relationSpace_le A R hR).trans hinc)
  rw [relationSpace_finrank, ArithmeticThetaLinearAlgebra.rational_matrix_nullity] at hd
  exact hd

private theorem early_iff {n h d : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (hv : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (hR : Relations A R) (B : ℕ) :
    early A R B = true ↔
      R.rank + (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).rank = h := by
  have hle := relation_rank_le_nullity A R hv hR B
  simp only [early,
    (ArithmeticThetaElimination.run_kernel_rank (B+1) h
      (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B)).2,
    (ArithmeticThetaElimination.run_kernel_rank h d R).2,
    Bool.or_eq_true, beq_iff_eq]
  omega

private theorem assembled_correct {n h d : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (hv : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (hR : Relations A R) (B : ℕ)
    (hr : R.rank + (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).rank = h) :
    Correct A (assemble A B) := by
  have he := (ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix n h B A hv).1
  have hdim : Module.finrank ℂ (relationSpace R) =
      h - (ArithmeticThetaComputed.coefficientMatrix A B).rank := by
    rw [relationSpace_finrank]
    rw [he] at hr
    omega
  have hk := (ArithmeticThetaDegreeAssembly.actual_early_certificate n h B A hv
    (relationSpace R) (relationSpace_le A R hR) hdim).2
  have hd := ArithmeticThetaDegreeAssembly.certified_theta_image_data n h B A hv
    (relationSpace R) (relationSpace_le A R hR) hdim
  dsimp [Correct, assemble, nullVectors, pivotIndices, coordinates]
  rw [he]
  exact ⟨rfl, hk, hd⟩

end ExecutableRelationCertificate

open ExecutableRelationCertificate in
theorem executable_relation_certificate :
    ∀ (n h d : ℕ) (A : ArithmeticThetaAdaptiveSolverR0230.Matrices n h)
      (R : Matrix (Fin h) (Fin d) ℚ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ArithmeticThetaAdaptiveSolverR0230.Relations A R → ∀ B : ℕ,
      (ArithmeticThetaAdaptiveSolverR0230.early A R B = true ↔
        R.rank + (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).rank = h) ∧
      (∀ o : ArithmeticThetaAdaptiveSolverR0230.Result h,
        ArithmeticThetaAdaptiveSolverR0230.certify A R B = some o →
        ArithmeticThetaAdaptiveSolverR0230.Correct A o) ∧
      (ArithmeticThetaAdaptiveSolverR0230.certify A R B = none ↔
        R.rank + (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).rank ≠ h) := by
  intro n h d A R hv hR B
  have he := early_iff A R hv hR B
  refine ⟨he, ?_, ?_⟩
  · intro o ho
    unfold certify at ho
    split at ho
    · next hb =>
      have heo : assemble A B = o := Option.some.inj ho
      subst o
      exact assembled_correct A R hv hR B (he.mp hb)
    · contradiction
  · simp only [certify, ite_eq_right_iff, Option.some_ne_none, imp_false]
    exact not_congr he

end ArithmeticThetaAdaptiveSolverR0230

#print axioms ArithmeticThetaAdaptiveSolverR0230.executable_relation_certificate
