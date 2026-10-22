module

public import Definitions.Def_PresheafOfModules_ExteriorPower
public import Definitions.Def_AlgebraicGeometry_ModulesDet
public import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
public import Definitions.Def_AlgebraicGeometry_KaehlerModule
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        letI := f.sectionsAlgebra W
        letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn (f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis.solution
