module

public import Mathlib

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace ArithmeticThetaProperFunctions

/-- The actual structure morphism's pullback of constants to global regular functions. -/
noncomputable def constantMap (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom

end ArithmeticThetaProperFunctions
