module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyIntegral.of_isPullback_of_geometricallyIntegral
    {κ k : Type u} [Field κ] [Field k] [Algebra κ k]
    {C C' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of k)) (g : C' ⟶ C)
    (h : IsPullback g c' c (Spec.map (CommRingCat.ofHom (algebraMap κ k))))
    [GeometricallyIntegral c'] :
    GeometricallyIntegral c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral.solution
