module

public import Mathlib
public import Definitions.Def_JacJ1Iface
public import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
public import Definitions.Def_AlgebraicGeometry_PolarisationRosati
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr.solution
