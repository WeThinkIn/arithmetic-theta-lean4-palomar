module

public import Definitions.Def_PresheafOfModules_ExteriorPower
public import Definitions.Def_AlgebraicGeometry_ModulesDet
public import Definitions.Def_AlgebraicGeometry_KaehlerModule
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ(f.kaehler, U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
          ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension.solution
