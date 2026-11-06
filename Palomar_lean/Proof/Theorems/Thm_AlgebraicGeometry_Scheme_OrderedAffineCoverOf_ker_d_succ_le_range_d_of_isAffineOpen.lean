module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] {W : V.Opens} (K : V.OrderedAffineCoverOf W) (hW : IsAffineOpen W) (p : ℕ) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; LinearMap.ker (K.d π (p + 1)) ≤ LinearMap.range (K.d π p) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.solution
