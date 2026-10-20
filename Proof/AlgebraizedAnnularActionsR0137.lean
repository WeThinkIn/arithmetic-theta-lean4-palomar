module

public import TowerPeriodRotationR0137
public import TowerScalarTranslationR0137
public import TowerInversionR0137
public import ProperTowerAutomorphismEffectivityR0137

@[expose] public section

/-! Assemble the three geometric tower actions on the same proper algebraic
model. All coordinates and finite-stage equations are retained by `ModelAction`.
The construction uses the proved morphism-effectivity provider. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaModelSymmetriesR0137
open CategoryTheory

/-- Period translation, every constant-unit translation, and inversion on the
specified proper-flat model, with their exact annular restrictions. -/
theorem algebraized_annular_actions :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∃ (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X),
      ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv := by
  intro k _ _ r hr h3 T M hM
  obtain ⟨grot, hgrot, _⟩ := tower_period_rotation k r hr h3 T
  obtain ⟨rot, hrot, _⟩ :=
    proper_tower_automorphism_effectivity k r hr h3 T M hM grot hgrot.1
  have hscal : ∀ a : kˣ, ∃ f : M.X ≅ M.X, ModelAction k M id a false f := by
    intro a
    obtain ⟨g, hg, _⟩ := tower_scalar_translation k r hr h3 T a
    obtain ⟨f, hf, _⟩ :=
      proper_tower_automorphism_effectivity k r hr h3 T M hM g hg.1
    exact ⟨f, g, hg, hf⟩
  choose scal hscal using hscal
  obtain ⟨ginv, hginv, _⟩ := tower_inversion k r hr h3 T
  obtain ⟨inv, hinv, _⟩ :=
    proper_tower_automorphism_effectivity k r hr h3 T M hM ginv hginv.1
  exact ⟨rot, scal, inv, ⟨grot, hgrot, hrot⟩, hscal, ⟨ginv, hginv, hinv⟩⟩

end ArithmeticThetaModelSymmetriesR0137

#print axioms ArithmeticThetaModelSymmetriesR0137.algebraized_annular_actions
