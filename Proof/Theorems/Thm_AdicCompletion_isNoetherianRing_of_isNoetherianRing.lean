module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing

@[expose] public section

universe u

theorem AdicCompletion.isNoetherianRing_of_isNoetherianRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.solution
