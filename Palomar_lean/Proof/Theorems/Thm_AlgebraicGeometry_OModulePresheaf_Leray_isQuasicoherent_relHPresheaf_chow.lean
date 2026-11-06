module

public import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
public import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsQuasicoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.solution
