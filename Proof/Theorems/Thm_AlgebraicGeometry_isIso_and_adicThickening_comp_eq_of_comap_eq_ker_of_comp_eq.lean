module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_AdicThickening
public import Definitions.Def_AlgebraicGeometry_ProjSpace
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (J : (pullback f g).IdealSheafData)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ : ∀ n : ℕ, IsClosedImmersion (γ n))
    (hγJ : ∀ n : ℕ, J.comap (adicThickeningι (pullback.fst f g ≫ f) I n) = (γ n).ker)
    (hγX : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (n : ℕ)
    (ζ : adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hζ : ζ ≫ adicThickeningι f I n = adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) :
    IsIso ζ ∧ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι =
      ζ ≫ γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq.solution
