module

public import Mathlib
public import Definitions.Def_Patching_SystemTypes
public import P2M.Util
public import P2M.Sol.S_IsRegularLocalRing_depth_self_eq_ringKrullDim

@[expose] public section

set_option autoImplicit false

open IsLocalRing RingTheory

theorem IsRegularLocalRing.depth_self_eq_ringKrullDim
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsRegularLocalRing R] :
    (Module.depth R R : WithBot ℕ∞) = ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_depth_self_eq_ringKrullDim.solution
