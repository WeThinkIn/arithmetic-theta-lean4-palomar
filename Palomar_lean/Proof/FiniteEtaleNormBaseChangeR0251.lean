module

public import FiniteEtaleNormSectionR0251

@[expose] public section

/-! Arbitrary Cartesian base change for the section determinant norm. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150

namespace NormBaseChange

lemma restrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Sections Y U) :
    restrict V W h (f.appLE U V e a) = f.appLE U W (h.trans e) a := by
  exact ConcreteCategory.congr_hom (f.appLE_map e (homOfLE h).op) a

lemma appLE_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (W : X.Opens) (e : V ≤ U) (h : W ≤ f ⁻¹ᵁ V)
    (a : Sections Y U) :
    f.appLE V W h (restrict U V e a) =
      f.appLE U W (h.trans (f.preimage_mono e)) a := by
  exact ConcreteCategory.congr_hom (f.map_appLE h (homOfLE e).op) a

end NormBaseChange

/-- The determinant section norm commutes with every Cartesian base change,
including nonflat maps and nonreduced schemes. -/
theorem finite_etale_norm_base_change
    (X Y Xb Yb : Scheme.{u})
    (f : X ⟶ Y) (fb : Xb ⟶ Yb) (i : Xb ⟶ X) (j : Yb ⟶ Y)
    [IsFinite f] [Etale f] [IsFinite fb] [Etale fb]
    (h : IsPullback i fb f j)
    (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U)
    (hab : IsNormSection f U a b)
    (V : Yb.Opens) (e : V ≤ j ⁻¹ᵁ U) :
    ∃ ep : fb ⁻¹ᵁ V ≤ i ⁻¹ᵁ (f ⁻¹ᵁ U),
      IsNormSection fb V (i.appLE _ _ ep a) (j.appLE U V e b) := by
  have preimage_le : ∀ (W : Y.Opens) (Z : Yb.Opens),
      Z ≤ j ⁻¹ᵁ W → fb ⁻¹ᵁ Z ≤ i ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    intro W Z eZ
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact fb.preimage_mono eZ
  refine ⟨preimage_le U V e, ?_⟩
  intro T eT hT
  apply NormSection.sections_eq_local
  intro y hy
  obtain ⟨W, hyW, eW, hW⟩ := finite_etale_free_cover X Y f U (j y) (e (eT hy))
  obtain ⟨Z, hZ, hyZ, eZ⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ T.1 ⊓ j ⁻¹ᵁ W.1 from ⟨hy, hyW⟩)
  have eZT : Z ≤ T.1 := eZ.trans inf_le_left
  have eZW : Z ≤ j ⁻¹ᵁ W.1 := eZ.trans inf_le_right
  refine ⟨Z, hyZ, eZT, ?_⟩
  rw [NormSection.affineNorm_restrict fb T ⟨Z, hZ⟩ eZT hT,
    NormSection.restrict_trans, NormSection.restrict_trans,
    NormBaseChange.restrict_appLE, NormBaseChange.restrict_appLE]
  have hp := BaseChange.sections_pushout f fb i j h W.1 Z W.2 hZ eZW
    (preimage_le W.1 Z eZW)
  have hn := (BaseChange.norm_of_pushout _ _ _ _ hp hW
    (f.finite_app W.1 W.2)).2
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ W.1) (f.preimage_mono eW) a)
  change j.appLE W.1 Z eZW
      (affineNorm f W.1 (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ W.1) (f.preimage_mono eW) a)) =
    affineNorm fb Z (i.appLE _ _ (preimage_le W.1 Z eZW)
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ W.1) (f.preimage_mono eW) a)) at hn
  rw [hab W eW hW, NormBaseChange.appLE_restrict,
    NormBaseChange.appLE_restrict] at hn
  exact hn.symm

end ArithmeticThetaSchemeKatoNormR0251
