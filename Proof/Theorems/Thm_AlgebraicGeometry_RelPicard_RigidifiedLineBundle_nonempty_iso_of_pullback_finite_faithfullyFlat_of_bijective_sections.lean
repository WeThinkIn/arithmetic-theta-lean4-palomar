module

public import Mathlib
public import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
public import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅
      (M₂.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.solution
