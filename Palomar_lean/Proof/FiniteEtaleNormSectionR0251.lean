module

public import SchemeKatoNormDefinitionsR0251
public import FiniteEtaleFreeCoverR0251

@[expose] public section

/-! The determinant norm glued on arbitrary opens of arbitrary schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150

namespace NormSection
variable {X Y : Scheme.{u}}

lemma restrict_trans (U V W : Y.Opens) (e : V ≤ U) (e' : W ≤ V)
    (a : Sections Y U) :
    restrict V W e' (restrict U V e a) = restrict U W (e'.trans e) a := by
  exact (ConcreteCategory.congr_hom (Y.presheaf.map_comp
    (homOfLE e).op (homOfLE e').op) a).symm

/-- On affine refinements, determinant compatibility is the actual section-ring
pushout theorem applied to the identity Cartesian square. -/
lemma affineNorm_restrict (f : X ⟶ Y) [IsFinite f]
    (U V : Y.affineOpens) (e : V.1 ≤ U.1) (hf : AffineFree f U.1)
    (a : Sections X (f ⁻¹ᵁ U.1)) :
    restrict U.1 V.1 e (affineNorm f U.1 a) =
      affineNorm f V.1 (restrict (f ⁻¹ᵁ U.1) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) := by
  have hp : IsPullback (𝟙 X) f f (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs := BaseChange.sections_pushout f f (𝟙 X) (𝟙 Y) hp
    U.1 V.1 U.2 V.2 e (f.preimage_mono e)
  have hn := (BaseChange.norm_of_pushout _ _ _ _ hs hf (f.finite_app U.1 U.2)).2 a
  simpa [Scheme.Hom.appLE, affineNorm, restrict,
    ArithmeticThetaArbitraryKatoUnitR0249.restrict] using hn

/-- Equality of sections can be tested on a neighborhood of each point. -/
lemma sections_eq_local (U : Y.Opens) (s t : Sections Y U)
    (h : ∀ y ∈ U, ∃ (V : Y.Opens) (hy : y ∈ V) (e : V ≤ U),
      restrict U V e s = restrict U V e t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf U s t
  intro y hy
  change Y.presheaf.germ U y hy s = Y.presheaf.germ U y hy t
  obtain ⟨V, hyV, e, he⟩ := h y hy
  have H := congrArg (Y.presheaf.germ V y hyV) he
  simpa only [restrict, ArithmeticThetaArbitraryKatoUnitR0249.restrict,
    TopCat.Presheaf.germ_res_apply] using H

/-- The local determinants agree even when the intersection is not affine. -/
lemma affineNorm_overlap (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U))
    (V W : Y.affineOpens) (eV : V.1 ≤ U) (eW : W.1 ≤ U)
    (hV : AffineFree f V.1) (hW : AffineFree f W.1) :
    restrict V.1 (V.1 ⊓ W.1) inf_le_left
      (affineNorm f V.1 (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono eV) a)) =
    restrict W.1 (V.1 ⊓ W.1) inf_le_right
      (affineNorm f W.1 (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ W.1) (f.preimage_mono eW) a)) := by
  apply sections_eq_local
  intro y hy
  obtain ⟨T, hT, hyT, eT⟩ := exists_isAffineOpen_mem_and_subset hy
  refine ⟨T, hyT, eT, ?_⟩
  rw [restrict_trans, restrict_trans,
    affineNorm_restrict f V ⟨T, hT⟩ (eT.trans inf_le_left) hV,
    affineNorm_restrict f W ⟨T, hT⟩ (eT.trans inf_le_right) hW,
    restrict_trans, restrict_trans]

end NormSection

/-- The unique section norm is obtained by gluing all free affine determinants.
The index family covers every open by the arbitrary-scheme free-cover theorem. -/
theorem finite_etale_norm_section
    (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f]
    (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)) :
    ∃! b : Sections Y U, IsNormSection f U a b := by
  classical
  let I := {V : Y.affineOpens // V.1 ≤ U ∧ AffineFree f V.1}
  let O : I → Y.Opens := fun V => V.1.1
  let e : ∀ V : I, O V ≤ U := fun V => V.2.1
  let s : ∀ V : I, Sections Y (O V) := fun V =>
    affineNorm f (O V) (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ O V) (f.preimage_mono (e V)) a)
  have hcover : U ≤ ⨆ V : I, O V := by
    intro y hy
    obtain ⟨V, hyV, eV, hV⟩ := finite_etale_free_cover X Y f U y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, eV, hV⟩, hyV⟩
  have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf O s := by
    intro V W
    exact NormSection.affineNorm_overlap f U a V.1 W.1 V.2.1 W.2.1 V.2.2 W.2.2
  obtain ⟨b, hb, _⟩ := Y.sheaf.existsUnique_gluing' O U
    (fun V => homOfLE (e V)) hcover s hcompat
  change ∀ V : I, restrict U (O V) (e V) b = s V at hb
  refine ⟨b, ?_, ?_⟩
  · intro V eV hV
    exact (hb ⟨V, eV, hV⟩).symm
  · intro b' hb'
    apply NormSection.sections_eq_local U b' b
    intro y hy
    obtain ⟨V, hyV, eV, hV⟩ := finite_etale_free_cover X Y f U y hy
    exact ⟨V.1, hyV, eV, (hb' V eV hV).symm.trans (hb ⟨V, eV, hV⟩).symm⟩

end ArithmeticThetaSchemeKatoNormR0251
