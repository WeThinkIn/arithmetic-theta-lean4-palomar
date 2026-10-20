module

public import SchemeThetaInversionR0259
public import SchemeMidpointThetaLiftR0259
public import SchemeCyclicThetaSplittingR0259
public import SchemePrimitiveThetaCommutatorR0259
public import SchemeThetaSectionCohomologyR0259

@[expose] public section

/-! Assembly of the normalized theta marking for the given scheme family. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259

/-- The full-level marking and section cohomology use the same actual theta line. -/
theorem scheme_full_level_theta_marking :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (m : ℕ), 0 < m → Even m → ∀ M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m), ArithmeticThetaSchemeThetaMarkingR0259.MarkingExists E m M := by
  intro k _ _ S σ E m hm he M
  obtain ⟨ι, hι, _⟩ := scheme_theta_inversion k S σ E m
  obtain ⟨α, hα, _⟩ :=
    scheme_midpoint_theta_lift k S σ E m hm he M.x M.killed_x ι hι
  obtain ⟨β, hβ, _⟩ :=
    scheme_midpoint_theta_lift k S σ E m hm he M.y M.killed_y ι hι
  exact ⟨scheme_theta_section_cohomology k S σ E m hm, ι, hι,
    scheme_cyclic_theta_splitting k S σ E m hm he M.x M.killed_x ι hι,
    scheme_cyclic_theta_splitting k S σ E m hm he M.y M.killed_y ι hι,
    α, β, hα.1, hα.2, hβ.1, hβ.2,
    scheme_primitive_theta_commutator k S σ E m hm he M α β⟩

#print axioms scheme_full_level_theta_marking
end ArithmeticThetaSchemeThetaMarkingR0259
