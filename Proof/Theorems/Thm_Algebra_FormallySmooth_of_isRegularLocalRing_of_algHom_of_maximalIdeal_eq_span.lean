module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span

@[expose] public section

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.FormallySmooth.of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (S : Type u) [CommRing S] [IsRegularLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Module.Flat R S]
    (ρ : S →ₐ[R] R) :
    Algebra.FormallySmooth R S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span.solution
