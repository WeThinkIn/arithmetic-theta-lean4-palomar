module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
    {κ : Type u} [Field κ] {C U P : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of κ)) [IsIntegral C]
    (u : U ⟶ C) [IsOpenImmersion u] [Nonempty U]

    (hreg : ∀ x : C, x ∉ Set.range u.base → IsDiscreteValuationRing (C.presheaf.stalk x))
    (p : P ⟶ Spec (CommRingCat.of κ)) [IsProper p]
    (f : U ⟶ P) (hf : f ≫ p = u ≫ c) :
    ∃ g : C ⟶ P, g ≫ p = c ∧ u ≫ g = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk.solution
