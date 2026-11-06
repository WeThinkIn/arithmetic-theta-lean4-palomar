module

public import Definitions.Def_Patching_SystemTypes
public import P2M.Util
public import P2M.Sol.S_Module_depth_quotSMulTop_succ_eq

@[expose] public section

open IsLocalRing RingTheory
theorem Module.depth_quotSMulTop_succ_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 = Module.depth R M := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_quotSMulTop_succ_eq.solution
