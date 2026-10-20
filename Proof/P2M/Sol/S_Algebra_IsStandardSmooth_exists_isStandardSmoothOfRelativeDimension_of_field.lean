module

public import Mathlib
public import P2M.Util

@[expose] public section
namespace P2MW.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field

set_option autoImplicit false

theorem solution
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] :
    ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth k B).out
  exact ⟨P.dimension, ⟨ι, σ, hσ, hι, P, rfl⟩⟩
