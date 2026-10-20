module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.solution
