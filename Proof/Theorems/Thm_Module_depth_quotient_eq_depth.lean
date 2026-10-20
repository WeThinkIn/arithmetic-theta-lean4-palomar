module

public import Mathlib
public import Definitions.Def_Patching_SystemTypes
public import P2M.Util
public import P2M.Sol.S_Module_depth_quotient_eq_depth

@[expose] public section

open IsLocalRing RingTheory
theorem Module.depth_quotient_eq_depth
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_quotient_eq_depth.solution
