module

public import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Finiteness.Basic
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
    (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover) :
    (OModulePresheaf.pushforward π i H).CechFinite K ↔ H.CechFinite (K.preimage i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.solution
