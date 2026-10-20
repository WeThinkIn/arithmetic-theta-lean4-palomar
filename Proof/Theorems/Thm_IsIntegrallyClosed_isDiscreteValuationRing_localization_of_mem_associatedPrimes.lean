module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes

@[expose] public section

theorem IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.solution
