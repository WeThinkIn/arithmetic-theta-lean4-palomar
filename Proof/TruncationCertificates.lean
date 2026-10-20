module

public import Mathlib

@[expose] public section

namespace ArithmeticThetaElementary

/-- A relation of full series vanishes in each retained coefficient. -/
theorem truncation_inclusion :
    ∀ (h B : ℕ) (θ : Fin h → PowerSeries ℂ) (c : Fin h → ℂ),
      (∑ i : Fin h, c i • θ i) = 0 → ∀ a : Fin (B + 1),
        (∑ i : Fin h, c i * PowerSeries.coeff a.val (θ i)) = 0 := by
  intro h B θ c hc a
  have ha := congrArg (PowerSeries.coeff a.val) hc
  simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using ha

/-- Independent truncated columns certify independence of the full series. -/
theorem full_column_rank_early_stop :
    ∀ (h B : ℕ) (θ : Fin h → PowerSeries ℂ),
      LinearIndependent ℂ (fun i : Fin h => fun a : Fin (B + 1) =>
        PowerSeries.coeff a.val (θ i)) → LinearIndependent ℂ θ := by
  intro h B θ hcols
  rw [Fintype.linearIndependent_iff] at hcols ⊢
  intro c hc
  apply hcols c
  funext a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
    truncation_inclusion h B θ c hc a

/-- Nested relation spaces coincide when their outer dimensions agree. -/
theorem dimension_sandwich_certificate :
    ∀ (h : ℕ) (W K T : Submodule ℂ (Fin h → ℂ)),
      W ≤ K → K ≤ T → Module.finrank ℂ W = Module.finrank ℂ T →
        W = K ∧ K = T := by
  intro h W K T hWK hKT hdim
  have hWT : W = T := Submodule.eq_of_le_of_finrank_eq (hWK.trans hKT) hdim
  have hKW : K ≤ W := hWT.symm ▸ hKT
  exact ⟨le_antisymm hWK hKW, (le_antisymm hWK hKW).symm.trans hWT⟩

end ArithmeticThetaElementary
