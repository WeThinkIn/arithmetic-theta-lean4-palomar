module

public import SchemeThetaPushforwardActionR0261
public import SchemeThetaPushforwardBaseChangeR0261
public import SchemeThetaActionRelationsR0261
public import SchemeInvariantThetaLineR0261
public import SchemeSchrodingerOrbitR0261
public import SchemeThetaIdentityEvaluationR0261
public import SchemeFixedLineBaseChangeR0261
public import SchemeFullLevelThetaMarkingR0259

@[expose] public section

/-! Geometric assembly for the actual theta sheaf and full level marking. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaSchemeSchrodingerR0261
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259

/-- The full level marking constructs all operators and the common value line;
no frame or theta structure is an additional hypothesis. -/
theorem scheme_geometric_schrodinger
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    (E : Family S) (m : ℕ) (hm : 0 < m) (he : Even m)
    (M : FullLevel E (2*m)) : Comparison E m M := by
  obtain ⟨_, ι, hι, _, _, α, β, hα, hsα, hβ, hsβ, c, ⟨hc, hp⟩, _⟩ :=
    scheme_full_level_theta_marking k S σ E m hm he M
  obtain ⟨A, hA, _⟩ := scheme_theta_pushforward_action k S σ E m
    (translation E M.x) (SchemeDoubledTorsionLift.translation_over E M.x) α
  obtain ⟨B, hB, _⟩ := scheme_theta_pushforward_action k S σ E m
    (translation E M.y) (SchemeDoubledTorsionLift.translation_over E M.y) β
  have hrel := scheme_theta_action_relations k S σ E m hm he M ι α β
    hι hα hβ A B c hc hA hB
  have hrank := (scheme_theta_pushforward_base_change k S σ E m hm).1
  have hline := scheme_invariant_theta_line k S σ E m hm A B c hrel hp
  have horbit := scheme_schrodinger_orbit k S σ (V E m) m hm A B c hrel hp
  have hnatural := scheme_fixed_line_base_change k S σ (V E m) m hm A hrel.1
  have hvalue : Scheme.Modules.IsInvertible (commonValueLine E m A) :=
    hline.dual.1.tensor_monoidalV2
      ((SchemeThetaSectionCohomology.line_invertible E m).pullback E.zero)
  have hm2 : 2 ≤ m := by
    obtain ⟨n, hn⟩ := he
    omega
  have heval := scheme_theta_identity_evaluation k S σ E m hm2
  refine ⟨ι, α, β, c, A, B, hι, hα, hsα, hβ, hsβ, hc, hp, hA, hB,
    hrel, hrank, hline, horbit, hnatural, hvalue, heval, ?_⟩
  obtain ⟨e, hinc, _, _⟩ := horbit
  refine ⟨e, hinc, ?_⟩
  intro i
  rw [← Category.assoc, hinc i]
  rfl

#print axioms scheme_geometric_schrodinger
end ArithmeticThetaSchemeSchrodingerR0261
