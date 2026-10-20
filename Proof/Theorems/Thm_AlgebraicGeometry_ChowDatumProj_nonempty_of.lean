module

public import Definitions.Def_AlgebraicGeometry_ProjSpace
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_ChowDatumProj_nonempty_of

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ChowDatumProj.nonempty_of {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) : Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.solution
