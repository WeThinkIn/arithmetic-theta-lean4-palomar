module

public import CorrectedGammaFiniteFactorizationR0061
public import CorrectedGammaTailExistsR0061

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

theorem gamma_data_exists :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ), 0 < r → j < r →
      ∃ v u : Chart k, IsGammaData k r j v u := by
  intro k _ _ r j hr hj
  obtain ⟨v, hvunit, hvtail⟩ := gamma_tail_exists k r j hr hj
  refine ⟨v, horizontal k r j * v, hvunit, hvtail, ?_, rfl⟩
  intro n
  obtain ⟨N₀, hN₀⟩ := hvtail n
  refine ⟨N₀ + 1, ?_⟩
  intro N hN
  have hpos : 0 < N := by omega
  have htail : v - tailPartial k r j N ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n :=
    hN₀ N (by omega)
  have heq : horizontal k r j * v - fullPartial k r j N =
      horizontal k r j * (v - tailPartial k r j N) := by
    rw [gamma_finite_factorization k r j N hr hj hpos]
    ring
  rw [heq]
  exact (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).mul_mem_left _ htail

end ArithmeticThetaCorrectedGammaR0061
