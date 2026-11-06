module

public import P2M.Util
public import P2M.Sol.S_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem

@[expose] public section

open IsLocalRing
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem.solution
