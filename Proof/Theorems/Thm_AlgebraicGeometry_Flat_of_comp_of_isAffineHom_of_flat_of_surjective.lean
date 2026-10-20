module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective {X Y S : Scheme.{u}}
    (σ : X ⟶ Y) (y : Y ⟶ S) [Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective.solution
