module

public import GeneralEllipticKatoDefinitionsR0168
public import Theorems.Thm_WeierstrassProjModel_projModel_isPullback_baseChange_ring
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
public import ActualGenericGroupLawR0146

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
namespace BaseChange
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}

/-- Translation by a global point of a natural group law. -/
def shift (G : RelativeGroupLaw R f) (a : SchemeHomOver (𝟙 _) f) : A ⟶ A :=
  (G.mul f RelativeGroupLaw.idPoint
    (WeierstrassProjModel.schemeHomOverComp f (Category.comp_id f) a)).val

lemma shift_over (G : RelativeGroupLaw R f) (a : SchemeHomOver (𝟙 _) f) :
    shift G a ≫ f = f :=
  (G.mul f RelativeGroupLaw.idPoint
    (WeierstrassProjModel.schemeHomOverComp f (Category.comp_id f) a)).property

lemma comp_shift (G : RelativeGroupLaw R f) (a : SchemeHomOver (𝟙 _) f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.val ≫ shift G a = (G.mul t x
      (WeierstrassProjModel.schemeHomOverComp t (Category.comp_id t) a)).val := by
  have h := congrArg Subtype.val (G.mul_natural f t x.val x.property
    RelativeGroupLaw.idPoint
    (WeierstrassProjModel.schemeHomOverComp f (Category.comp_id f) a))
  simpa only [shift, WeierstrassProjModel.schemeHomOverComp, Category.comp_id,
    ← Category.assoc, x.property] using h

lemma shift_comp (G : RelativeGroupLaw R f) (a b : SchemeHomOver (𝟙 _) f) :
    shift G a ≫ shift G b = shift G (G.mul (𝟙 _) a b) := by
  rw [comp_shift G b f ⟨shift G a, shift_over G a⟩]
  change (G.mul f (G.mul f _ _) _).val = _
  rw [G.mul_assoc]
  have h := G.mul_natural (𝟙 _) f f (Category.comp_id f) a b
  rw [← h]
  rfl

lemma shift_one (G : RelativeGroupLaw R f) : shift G (G.one (𝟙 _)) = 𝟙 A := by
  unfold shift
  rw [G.one_natural, G.mul_one]

/-- Translation is an isomorphism over the same base. -/
def shiftIso (G : RelativeGroupLaw R f) (a : SchemeHomOver (𝟙 _) f) : A ≅ A where
  hom := shift G a
  inv := shift G (G.inv (𝟙 _) a)
  hom_inv_id := by
    rw [shift_comp]
    letI := G.pointGroup (𝟙 _)
    change shift G (a * a⁻¹) = _
    rw [mul_inv_cancel]
    exact shift_one G
  inv_hom_id := by
    rw [shift_comp, G.inv_mul_cancel, shift_one]

/-- Translate the chosen section to the identity of the pulled-back law. -/
lemma pointed_cartesian {R' : Type u} [CommRing R'] {A' : Scheme.{u}}
    (g : R →+* R') (f' : A' ⟶ Spec (CommRingCat.of R'))
    (α : A' ⟶ A) (hα : IsPullback α f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 _) f') :
    ∃ b : A' ⟶ A, IsPullback b f' f (Spec.map (CommRingCat.ofHom g)) ∧
      e.val ≫ b = (G.one (Spec.map (CommRingCat.ofHom g))).val := by
  obtain ⟨H, _, hHone⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback g f f' α hα G
  let τ := shiftIso H (H.inv (𝟙 _) e)
  have ht : τ.hom ≫ f' = f' := shift_over _ _
  have hp : IsPullback τ.hom f' f' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using ht⟩
  refine ⟨τ.hom ≫ α, ?_, ?_⟩
  · simpa only [Category.id_comp] using hp.paste_horiz hα
  · have he : e.val ≫ τ.hom = (H.one (𝟙 _)).val := by
      rw [show τ.hom = shift H (H.inv (𝟙 _) e) from rfl, comp_shift]
      have hi : WeierstrassProjModel.schemeHomOverComp (𝟙 _) (Category.comp_id _)
          (H.inv (𝟙 _) e) = H.inv (𝟙 _) e := Subtype.ext (Category.id_comp _)
      rw [hi]
      letI := H.pointGroup (𝟙 _)
      exact congrArg Subtype.val (mul_inv_cancel e)
    rw [← Category.assoc, he, hHone]
    rfl

/-- A Cartesian comparison preserving multiplication and identity preserves
all natural-number multiplication morphisms, including zero. -/
lemma nsmul_comp {R' : Type u} [CommRing R'] {A' : Scheme.{u}}
    (g : R →+* R') (f' : A' ⟶ Spec (CommRingCat.of R'))
    (b : A' ⟶ A) (hb : IsPullback b f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R' f')
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
      (x y : SchemeHomOver t f'), (H.mul t x y).val ≫ b =
      (G.mul (t ≫ Spec.map (CommRingCat.ofHom g))
        ⟨x.val ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, x.property]⟩
        ⟨y.val ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, y.property]⟩).val)
    (ho : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')),
      (H.one t).val ≫ b = (G.one (t ≫ Spec.map (CommRingCat.ofHom g))).val)
    (n : ℕ) : H.schemeNsmul n ≫ b = b ≫ G.schemeNsmul n := by
  have hn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
      (x : SchemeHomOver t f') (m : ℕ) :
      (H.nsmul t m x).val ≫ b =
        (G.nsmul (t ≫ Spec.map (CommRingCat.ofHom g)) m
          ⟨x.val ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, x.property]⟩).val := by
    induction m with
    | zero => exact ho t
    | succ m ih =>
      rw [RelativeGroupLaw.nsmul_succ, hm, RelativeGroupLaw.nsmul_succ]
      congr 2
      exact Subtype.ext ih
  have hnat := congrArg Subtype.val (G.nsmul_natural f
    (f' ≫ Spec.map (CommRingCat.ofHom g)) b hb.w n RelativeGroupLaw.idPoint)
  rw [RelativeGroupLaw.schemeNsmul, hn]
  simpa only [RelativeGroupLaw.schemeNsmul, WeierstrassProjModel.schemeHomOverComp,
    Category.id_comp, Category.comp_id] using hnat.symm

end BaseChange

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel

/-- Geometric coefficient change for every characteristic-zero elliptic curve,
with the specified origin and every multiplication map. -/
theorem general_elliptic_base_change :
    ∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic]
      (G : Law F W) (hG : IsOriginLaw F W G)
      (K : Type u) [Field K] [CharZero K] (ι : F →+* K)
      (Gb : Law K (W.map ι)) (hGb : IsOriginLaw K (W.map ι) Gb),
      ∃ b : Curve K (W.map ι) ⟶ Curve F W,
        IsBaseChange F K W (W.map ι) G Gb ι b := by
  intro F _ _ W _ G hG K _ _ ι Gb hGb
  letI := ι.toAlgebra
  obtain ⟨α, hα⟩ := projModel_isPullback_baseChange_ring W.toProjective K
  obtain ⟨b, hb, he⟩ := BaseChange.pointed_cartesian ι (structureMap K (W.map ι))
    α hα G (kwZeroSect K (W.map ι))
  have he' : origin K (W.map ι) ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ origin F W := by
    exact he.trans (hG.1 _)
  refine ⟨b, hb, he', ?_⟩
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι (structureMap F W) (structureMap K (W.map ι)) b hb G
  have hone : (Gb.one (𝟙 _)).val = (H.one (𝟙 _)).val := by
    apply hb.hom_ext
    · rw [hGb.1, Category.id_comp, he', ho, Category.id_comp, hG.1]
    · exact (Gb.one (𝟙 _)).property.trans (H.one (𝟙 _)).property.symm
  have hlaw : Gb = H :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext Gb H
      (fun t x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
        (W.map ι).toProjective Gb H hone t x y)
      (by
        intro T t
        apply Subtype.ext
        have h1 := congrArg Subtype.val (Gb.one_natural (𝟙 _) t t (Category.comp_id t))
        have h2 := congrArg Subtype.val (H.one_natural (𝟙 _) t t (Category.comp_id t))
        exact h1.symm.trans ((congrArg (fun z => t ≫ z) hone).trans h2))
  intro n
  rw [hlaw]
  exact BaseChange.nsmul_comp ι (structureMap K (W.map ι)) b hb G H hm ho n

#print axioms general_elliptic_base_change
end ArithmeticThetaGeneralEllipticKatoR0168
