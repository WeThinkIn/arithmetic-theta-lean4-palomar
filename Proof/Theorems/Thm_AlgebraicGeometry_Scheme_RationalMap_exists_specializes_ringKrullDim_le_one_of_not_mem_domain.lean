module

public import Mathlib
public import Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) [IsAffine Y]
    (u : X ⤏ Y) (x : X) (hx : x ∉ u.domain) :
    ∃ z : X, z ∉ u.domain ∧ z ⤳ x ∧ ringKrullDim (X.presheaf.stalk z) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain.solution
