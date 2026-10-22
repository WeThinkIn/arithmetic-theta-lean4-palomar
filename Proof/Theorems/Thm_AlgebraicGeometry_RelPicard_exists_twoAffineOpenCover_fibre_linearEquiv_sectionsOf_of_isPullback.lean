module

public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
public import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
public import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
public import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
public import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
public import Definitions.Def_AlgebraicGeometry_IdealSheafModule
public import Definitions.Def_SheafOfModules_Monoidal
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.solution
