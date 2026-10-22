module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
    (Y : Scheme.{u}) (y : ↥Y) (Z₁ Z₂ : Set ↥Y)
    (hZ₁ : Z₁ ∈ irreducibleComponents ↥Y) (hZ₂ : Z₂ ∈ irreducibleComponents ↥Y)
    (hne : Z₁ ≠ Z₂) (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) :
    ¬ IsDomain (Y.presheaf.stalk y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne.solution
