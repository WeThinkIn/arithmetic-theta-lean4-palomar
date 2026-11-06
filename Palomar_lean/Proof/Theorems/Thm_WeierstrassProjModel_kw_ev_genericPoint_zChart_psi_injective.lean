module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Definitions.Def_WeierstrassCurve_ProjModel
public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
public import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
theorem WeierstrassProjModel.kw_ev_genericPoint_zChart_psi_injective
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    letI : Algebra R (projModelCR W.toProjective).functionField :=
      (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
        (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    ∀ (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
      → Function.Injective ψ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective.solution
