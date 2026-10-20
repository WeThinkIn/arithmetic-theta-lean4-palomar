module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; Function.Injective (K.aug π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.solution
