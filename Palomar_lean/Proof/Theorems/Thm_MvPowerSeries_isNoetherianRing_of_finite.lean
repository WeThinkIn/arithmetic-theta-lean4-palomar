module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import P2M.Util
public import P2M.Sol.S_MvPowerSeries_isNoetherianRing_of_finite
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Data.Rat.Floor

@[expose] public section

universe u v w
theorem MvPowerSeries.isNoetherianRing_of_finite {σ : Type u} {R : Type v} [Finite σ] [CommRing R] [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries σ R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.solution
