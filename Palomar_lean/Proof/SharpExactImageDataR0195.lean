module

public import SharpMatrixKernelR0195
public import EarlyCertificateAssembly

@[expose] public section

/-! Exact elimination data for the complete formal theta image at every
prefix at least the sharp cutoff. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaSharpKernelR0195

/-- The computed rational nullspace, selected columns, and unique rational
coordinates describe the full formal theta map at the sharp cutoff and above. -/
theorem sharp_exact_image_data :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaSharpKernelR0195.ImageData A B := by
  intro n h hh A hA B hB
  have hker := (sharp_matrix_kernel n h hh A hA).1 B hB
  apply ArithmeticThetaDegreeAssembly.certified_theta_image_data n h B A hA
    (LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) le_rfl
  rw [hker]
  exact ArithmeticThetaLinearAlgebra.rational_matrix_nullity (B + 1) h
    (ArithmeticThetaComputed.coefficientMatrix A B)

#print axioms sharp_exact_image_data
end ArithmeticThetaSharpKernelR0195
