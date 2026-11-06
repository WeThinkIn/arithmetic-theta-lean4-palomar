module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule {R : CommRingCat.{u}}
    (M : (Spec (.of R)).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
      ((modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.solution
