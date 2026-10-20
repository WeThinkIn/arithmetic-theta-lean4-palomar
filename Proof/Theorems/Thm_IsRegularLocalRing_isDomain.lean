module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_IsRegularLocalRing_isDomain

@[expose] public section

open IsLocalRing
theorem IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isDomain.solution
