module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.solution
