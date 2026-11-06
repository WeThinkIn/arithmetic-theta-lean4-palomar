module

public import GenericKaehlerComparisonR0149
public import IntegralHodgeFrameR0149
public import GlobalNormalizedDifferentialR0145

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Existence and uniqueness of the prescribed integral identity Hodge frame.
All constructions retain the actual base-change morphism of the frozen model. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
universe u

namespace ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134

lemma pullFrame_one {C S : Scheme.{u}} (s : S ⟶ C) {L : C.Modules}
    (q : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ⟶ L) :
    (Scheme.Modules.Hom.app (pullFrame s q)) ⊤ (1 : Γ(S, ⊤)) =
      Scheme.Modules.pullbackLocalSection s ((Scheme.Modules.Hom.app q) ⊤ (1 : Γ(C, ⊤))) := by
  letI := unitPullback_isIso s
  have hU : (unitPullback s).app ⊤
      (Scheme.Modules.pullbackLocalSection s
        (L := (SheafOfModules.unit C.ringCatSheaf : C.Modules)) (1 : Γ(C, ⊤))) = (1 : Γ(S, ⊤)) := by
    exact (GenericDualLocalizationR0140.unitPullback_app s ⊤ (1 : Γ(C, ⊤))).trans
      (map_one (s.app ⊤).hom)
  have hI : (inv (unitPullback s)).app ⊤ (1 : Γ(S, ⊤)) =
      Scheme.Modules.pullbackLocalSection s
        (L := (SheafOfModules.unit C.ringCatSheaf : C.Modules)) (1 : Γ(C, ⊤)) := by
    rw [← hU, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      IsIso.hom_inv_id]
    rfl
  change ((Scheme.Modules.pullback s).map q).app ⊤
    ((inv (unitPullback s)).app ⊤ (1 : Γ(S, ⊤))) = _
  rw [hI]
  exact (Scheme.Modules.pullbackLocalSection_app s q (U := ⊤) (1 : Γ(C, ⊤))).symm

lemma pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (U : Z.Opens) (m : Γ(L, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app L).app ((f ≫ g) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g m)) =
        Scheme.Modules.pullbackLocalSection (f ≫ g) m := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hv := congrArg (fun q => Scheme.Modules.Hom.app q U m) h
  change Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g m) =
    ((Scheme.Modules.pullbackComp f g).inv.app L).app ((f ≫ g) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection (f ≫ g) m) at hv
  rw [hv, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app]
  rfl
lemma pullback_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (U : Z.Opens) (m : Γ(L, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app L).app ((f ≫ g) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection (f ≫ g) m) =
        Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g m) := by
  rw [← pullback_comp f g L U m, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app]
  rfl

lemma unitEnd_isIso_of_surjective {S : Scheme.{u}}
    (q : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶
      (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (hq : Function.Surjective (Scheme.Modules.Hom.app q ⊤)) : IsIso q := by
  obtain ⟨c, hc⟩ := hq (1 : Γ(S, ⊤))
  let v := fromSection (SheafOfModules.unit S.ringCatSheaf : S.Modules) c
  have hv : v ≫ q = 𝟙 _ := by
    apply unit_hom_ext
    change (Scheme.Modules.Hom.app q ⊤)
      ((Scheme.Modules.Hom.app v ⊤) (1 : Γ(S, ⊤))) = (1 : Γ(S, ⊤))
    simpa [v, fromSection_apply] using hc
  exact ⟨⟨v, (unit_end_comm q v).trans hv, hv⟩⟩

lemma framed_hom_isIso_of_surjective {S : Scheme.{u}} {L N : S.Modules}
    (eL : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ L)
    (eN : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ N)
    (q : L ⟶ N) (hq : Function.Surjective (q.app ⊤)) : IsIso q := by
  let α : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶
      (SheafOfModules.unit S.ringCatSheaf : S.Modules) := eL.hom ≫ q ≫ eN.inv
  have hα : Function.Surjective (Scheme.Modules.Hom.app α ⊤) :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app eN.inv ⊤)).2.comp hq).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app eL.hom ⊤)).2
  letI : IsIso α := unitEnd_isIso_of_surjective α hα
  letI : IsIso (q ≫ eN.inv) := IsIso.of_isIso_comp_left eL.hom (q ≫ eN.inv)
  exact IsIso.of_isIso_comp_right q eN.inv

section Conormal
variable {A : Type u} [CommRing A] {C S : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of A)) (s : S ⟶ C)

/-- The actual section kills every local section of its ideal. -/
lemma ideal_app_zero (U : C.Opens) (x : Γ(idealModule s.ker, U)) :
    s.app U ((idealInclusion s.ker).app U x) = 0 := by
  have h := congrArg (fun q => Scheme.Modules.Hom.app q U x)
    (CategoryTheory.Limits.kernel.condition (quotientMap s.ker))
  change s.ker.subschemeι.app U ((idealInclusion s.ker).app U x) = 0 at h
  have hh := Scheme.Hom.congr_app s.toImage_imageι U
  have hx := ConcreteCategory.congr_hom hh ((idealInclusion s.ker).app U x)
  rw [Scheme.Hom.comp_app] at hx
  simp only [ConcreteCategory.comp_apply, h, map_zero] at hx
  exact (ConcreteCategory.bijective_of_isIso
    (S.presheaf.map (eqToHom (congrArg (fun q => q ⁻¹ᵁ U) s.toImage_imageι)).op)).1
      (hx.symm.trans (map_zero _).symm)

/-- The differential of the ideal, as an additive natural transformation. -/
def conormalAb : (idealModule s.ker).presheaf ⟶
    ((Scheme.Modules.pushforward s).obj ((Scheme.Modules.pullback s).obj f.kaehler)).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun x => Scheme.Modules.pullbackLocalSection s
        (relativeD f U.unop ((idealInclusion s.ker).app U.unop x))
      map_zero' := by simp only [map_zero, relativeD_zero, Scheme.Modules.pullbackLocalSection_zero]
      map_add' := by
        intro x y
        rw [map_add]
        erw [relativeD_add, Scheme.Modules.pullbackLocalSection_add] }
  naturality := by
    intro U V i
    ext x
    change Scheme.Modules.pullbackLocalSection s
        (relativeD f V.unop ((idealInclusion s.ker).app V.unop
          ((idealModule s.ker).presheaf.map i x))) =
      ((Scheme.Modules.pullback s).obj f.kaehler).presheaf.map
        ((TopologicalSpace.Opens.map s.base).map i.unop).op
          (Scheme.Modules.pullbackLocalSection s
            (relativeD f U.unop ((idealInclusion s.ker).app U.unop x)))
    rw [Scheme.Modules.map_pullbackLocalSection]
    erw [relativeD_restrict f U.unop i.unop.le]
    exact congrArg (fun a => Scheme.Modules.pullbackLocalSection s
      (relativeD f V.unop a))
      (ConcreteCategory.congr_hom ((idealInclusion s.ker).mapPresheaf.naturality i) x)

/-- The differential of the ideal is linear after restriction to its section. -/
def conormalPreHom : idealModule s.ker ⟶
    (Scheme.Modules.pushforward s).obj ((Scheme.Modules.pullback s).obj f.kaehler) :=
  ⟨PresheafOfModules.homMk (conormalAb f s) (fun U a x => by
    change Scheme.Modules.pullbackLocalSection s
        (relativeD f U.unop ((idealInclusion s.ker).app U.unop (a • x))) =
      s.app U.unop a • _
    rw [Scheme.Modules.Hom.app_smul]
    change Scheme.Modules.pullbackLocalSection s
        (relativeD f U.unop ((show Γ(C, U.unop) from a) *
          (show Γ(C, U.unop) from (idealInclusion s.ker).app U.unop x))) = _
    rw [relativeD_mul, Scheme.Modules.pullbackLocalSection_add,
      Scheme.Modules.pullbackLocalSection_smul,
      Scheme.Modules.pullbackLocalSection_smul, ideal_app_zero, zero_smul, add_zero]
    rfl)⟩

/-- Canonical map from the pulled-back ideal to the actual relative cotangent sheaf. -/
def conormalHom : (Scheme.Modules.pullback s).obj (idealModule s.ker) ⟶
    (Scheme.Modules.pullback s).obj f.kaehler :=
  ((Scheme.Modules.pullbackPushforwardAdjunction s).homEquiv _ _).symm
    (conormalPreHom f s)

lemma conormalHom_D (U : C.Opens) (x : Γ(idealModule s.ker, U)) :
    (conormalHom f s).app (s ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection s x) =
      Scheme.Modules.pullbackLocalSection s
        (relativeD f U ((idealInclusion s.ker).app U x)) := by
  rw [conormalHom, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

end Conormal

lemma ideal_comparison_on_section {X C S : Scheme.{u}} (j : C ⟶ X) (t : S ⟶ C)
    (e : (Scheme.Modules.pullback j).obj (idealModule (t ≫ j).ker) ⟶ idealModule t.ker)
    (he : e ≫ idealInclusion t.ker = pulledInclusion j (idealInclusion (t ≫ j).ker))
    (U : X.Opens) (x : Γ(idealModule (t ≫ j).ker, U)) :
    (idealInclusion t.ker).app (j ⁻¹ᵁ U)
      (e.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j x)) =
        j.app U ((idealInclusion (t ≫ j).ker).app U x) := by
  have hh := congrArg (fun q => Scheme.Modules.Hom.app q (j ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection j x)) he
  change (idealInclusion t.ker).app (j ⁻¹ᵁ U)
      (e.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j x)) =
    (unitPullback j).app (j ⁻¹ᵁ U)
      (((Scheme.Modules.pullback j).map (idealInclusion (t ≫ j).ker)).app (j ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection j x)) at hh
  rw [← Scheme.Modules.pullbackLocalSection_app] at hh
  exact hh.trans (ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140.unitPullback_app j U _)

lemma differential_naturality {A : Type u} [CommRing A] {X C S : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : C ⟶ Spec (CommRingCat.of A))
    (j : C ⟶ X) (t : S ⟶ C)
    (b : (Scheme.Modules.pullback j).obj f.kaehler ⟶ g.kaehler)
    (hb : ∀ U a, b.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j
      (relativeD f U a)) = relativeD g (j ⁻¹ᵁ U) (j.app U a))
    (I : X.Modules) (J : C.Modules)
    (i : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (l : J ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    (e : (Scheme.Modules.pullback j).obj I ⟶ J)
    (he : ∀ U x, l.app (j ⁻¹ᵁ U) (e.app (j ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection j x)) = j.app U (i.app U x))
    (ds : (Scheme.Modules.pullback (t ≫ j)).obj I ⟶
      (Scheme.Modules.pullback (t ≫ j)).obj f.kaehler)
    (dt : (Scheme.Modules.pullback t).obj J ⟶ (Scheme.Modules.pullback t).obj g.kaehler)
    (hds : ∀ U x, ds.app ((t ≫ j) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (t ≫ j) x) =
      Scheme.Modules.pullbackLocalSection (t ≫ j) (relativeD f U (i.app U x)))
    (hdt : ∀ V x, dt.app (t ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection t x) =
      Scheme.Modules.pullbackLocalSection t (relativeD g V (l.app V x))) :
    (Scheme.Modules.pullback t).map e ≫ dt =
      (Scheme.Modules.pullbackComp t j).hom.app I ≫
      ds ≫ (Scheme.Modules.pullbackComp t j).inv.app f.kaehler ≫
      (Scheme.Modules.pullback t).map b := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp t j).inv.app I)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply Scheme.Modules.pullback_hom_ext (t ≫ j)
  intro U x
  change (dt).app ((t ≫ j) ⁻¹ᵁ U)
    (((Scheme.Modules.pullback t).map e).app ((t ≫ j) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackComp t j).inv.app I).app
        ((t ≫ j) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (t ≫ j) x))) =
    ((Scheme.Modules.pullback t).map b).app ((t ≫ j) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackComp t j).inv.app f.kaehler).app ((t ≫ j) ⁻¹ᵁ U)
        ((ds).app ((t ≫ j) ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection (t ≫ j) x)))
  rw [pullback_comp_inv t j I U x]
  erw [← Scheme.Modules.pullbackLocalSection_app t e (Scheme.Modules.pullbackLocalSection j x)]
  erw [hdt (j ⁻¹ᵁ U), hds U x]
  rw [pullback_comp_inv t j f.kaehler U (relativeD f U (i.app U x))]
  erw [← Scheme.Modules.pullbackLocalSection_app t b
    (Scheme.Modules.pullbackLocalSection j (relativeD f U (i.app U x)))]
  rw [hb U (i.app U x), he U x]

/-- The actual conormal map commutes with restriction, through the canonical
pullback comparison and the specified differential map. -/
lemma conormal_naturality {A : Type u} [CommRing A] {X C S : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : C ⟶ Spec (CommRingCat.of A))
    (j : C ⟶ X) (t : S ⟶ C)
    (b : (Scheme.Modules.pullback j).obj f.kaehler ⟶ g.kaehler)
    (hb : ∀ U a, b.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j
      (relativeD f U a)) = relativeD g (j ⁻¹ᵁ U) (j.app U a))
    (e : (Scheme.Modules.pullback j).obj (idealModule (t ≫ j).ker) ⟶ idealModule t.ker)
    (he : e ≫ idealInclusion t.ker = pulledInclusion j (idealInclusion (t ≫ j).ker)) :
    (Scheme.Modules.pullback t).map e ≫ conormalHom g t =
      (Scheme.Modules.pullbackComp t j).hom.app (idealModule (t ≫ j).ker) ≫
      conormalHom f (t ≫ j) ≫ (Scheme.Modules.pullbackComp t j).inv.app f.kaehler ≫
      (Scheme.Modules.pullback t).map b :=
  differential_naturality f g j t b hb _ _ _ _ e
    (ideal_comparison_on_section j t e he) _ _ (conormalHom_D f (t ≫ j)) (conormalHom_D g t)

section OpenDifferential
open GenericKaehlerComparisonR0149
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
variable {A : Type u} [CommRing A] {C X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : C ⟶ Spec (CommRingCat.of A))
    (j : C ⟶ X) [IsOpenImmersion j] (h : j ≫ f = g)

include h in
lemma open_square : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A A)) := by
  simpa using h

/-- Restriction of relative differentials along the actual open immersion.
The comparison is defined by its action on universal differentials. -/
def openDifferential : (Scheme.Modules.pullback j).obj f.kaehler ⟶ g.kaehler :=
  comparisonHom f g j (open_square f g j h)

lemma openDifferential_D (U : X.Opens) (a : Γ(X, U)) :
    (openDifferential f g j h).app (j ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection j (relativeD f U a)) =
      relativeD g (j ⁻¹ᵁ U) (j.app U a) :=
  comparisonHom_D f g j (open_square f g j h) U a

lemma openDifferential_app_bijective (U : X.Opens) (hU : IsAffineOpen U)
    (hUr : U ≤ j.opensRange) (hV : IsAffineOpen (j ⁻¹ᵁ U)) :
    Function.Bijective ((openDifferential f g j h).app (j ⁻¹ᵁ U)) := by
  letI := f.sectionsAlgebra U
  letI := g.sectionsAlgebra (j ⁻¹ᵁ U)
  letI : Algebra Γ(X, U) Γ(C, j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  haveI : IsScalarTower A Γ(X, U) Γ(C, j ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (fac f g j (open_square f g j h) U))
  haveI : IsIso (j.app U) := j.isIso_app U hUr
  have hring : Function.Bijective (algebraMap Γ(X, U) Γ(C, j ⁻¹ᵁ U)) :=
    ConcreteCategory.bijective_of_isIso (j.app U)
  haveI : Algebra.IsPushout A Γ(X, U) A Γ(C, j ⁻¹ᵁ U) :=
    Algebra.IsPushout.of_bijective_right (R := A) Γ(X, U) Γ(C, j ⁻¹ᵁ U) hring
  haveI : Algebra.IsPushout A A Γ(X, U) Γ(C, j ⁻¹ᵁ U) := Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A Γ(X, U) A Γ(C, j ⁻¹ᵁ U))
  have hd := differential_map_bijective A A Γ(X, U) Γ(C, j ⁻¹ᵁ U) hring
  have hk : Function.Bijective (fun x : f.kaehlerPresheaf.obj (Opposite.op U) =>
      k1app f g j (open_square f g j h) U x) :=
    (g.kaehlerToSections_bijective_of_isAffineOpen hV).comp hd
  have hk1 : Function.Bijective ((k1 f g j (open_square f g j h)).app U) := by
    apply (Function.Bijective.of_comp_iff _ (f.kaehlerToSections_bijective_of_isAffineOpen hU)).mp
    change Function.Bijective (fun x : f.kaehlerPresheaf.obj (Opposite.op U) =>
      (k1 f g j (open_square f g j h)).app U (f.kaehlerToSections U x))
    simpa only [k1_kaehlerToSections] using hk
  apply (Function.Bijective.of_comp_iff _ (pullbackSection_bijective f j U hUr)).mp
  change Function.Bijective (fun x : Γ(f.kaehler, U) =>
    (comparisonHom f g j (open_square f g j h)).app (j ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection j x))
  simpa only [comparisonHom, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection] using hk1

lemma openDifferential_isIso : IsIso (openDifferential f g j h) := by
  apply isIso_of_affine_app
  intro V hV
  let U := j ''ᵁ V
  have he : j ⁻¹ᵁ U = V := j.preimage_image_eq V
  have hb := openDifferential_app_bijective f g j h U
    (hV.image_of_isOpenImmersion j) (j.image_le_opensRange V) (he.symm ▸ hV)
  exact he ▸ hb

end OpenDifferential

section IdealRestriction
variable {C X S : Scheme.{u}} (j : C ⟶ X) [IsOpenImmersion j]
    (t : S ⟶ C) (s : S ⟶ X) [IsClosedImmersion s] (ht : t ≫ j = s)

include ht in
lemma section_ker_restriction : s.ker.comap j = t.ker := by
  have hp : CategoryTheory.IsPullback t (𝟙 S) j s :=
    CategoryTheory.IsPullback.of_vert_isIso_mono ⟨by simpa using ht⟩
  exact AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange hp

include ht in
/-- The ideal comparison on a neighborhood is the unique one preserving the
actual inclusion into regular functions. -/
lemma ideal_restriction_iso :
    ∃ e : (Scheme.Modules.pullback j).obj (idealModule s.ker) ≅ idealModule t.ker,
      e.hom ≫ idealInclusion t.ker = pulledInclusion j (idealInclusion s.ker) := by
  have hr := pullback_open_realization j s.ker (idealModule s.ker)
    (idealInclusion s.ker) (ideal_realization s.ker)
  rw [section_ker_restriction j t s ht] at hr
  obtain ⟨e, he, _⟩ := realization_unique_iso t.ker _ _ _ _ hr (ideal_realization t.ker)
  exact ⟨e, he⟩

end IdealRestriction

section AffineSection
variable {A : Type u} [CommRing A] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of A))
    (s : Spec (CommRingCat.of A) ⟶ C) (hs : s ≫ f = 𝟙 _)

include hs in
lemma section_constant (a : A) :
    s.appTop ((f.constToPresheaf.app (Opposite.op ⊤)).hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv a := by
  have he : f.constToPresheaf.app (Opposite.op ⊤) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop := by
    simp [Scheme.Hom.constToPresheaf, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [he]
  change (f.appTop ≫ s.appTop) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = _
  rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  rfl

lemma relativeD_constant (U : C.Opens) (a : A) :
    relativeD f U ((f.constToPresheaf.app (Opposite.op U)).hom a) = 0 := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U
    (KaehlerDifferential.D A Γ(C, U) (algebraMap A Γ(C, U) a)) = 0
  rw [Derivation.map_algebraMap, map_zero]

include hs in
/-- Subtracting the value along a section does not change the relative
differential. On an affine open it produces an actual section of the ideal. -/
lemma ideal_differential_lift [IsAffine C] [QuasiCompact s] (a : Γ(C, ⊤)) :
    ∃ x : Γ(idealModule s.ker, ⊤),
      relativeD f ⊤ ((idealInclusion s.ker).app ⊤ x) = relativeD f ⊤ a := by
  let c : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom (s.appTop a)
  let a₀ : Γ(C, ⊤) := a - (f.constToPresheaf.app (Opposite.op ⊤)).hom c
  have ha₀ : a₀ ∈ s.ker.ideal ⟨⊤, isAffineOpen_top C⟩ := by
    rw [Scheme.Hom.ker_apply]
    change s.appTop a₀ = 0
    dsimp only [a₀]
    rw [map_sub, section_constant f s hs]
    simp [c]
  change a₀ ∈ (s.ker.ideal ⟨⊤, isAffineOpen_top C⟩).carrier at ha₀
  rw [← (ideal_realization s.ker).2 ⟨⊤, isAffineOpen_top C⟩] at ha₀
  obtain ⟨x, hx⟩ := ha₀
  refine ⟨x, ?_⟩
  refine (congrArg (relativeD f ⊤) hx).trans ?_
  letI := f.sectionsAlgebra ⊤
  change f.kaehlerToSectionsₗ ⊤
    (KaehlerDifferential.D A Γ(C, ⊤)
      (a - algebraMap A Γ(C, ⊤) c)) = relativeD f ⊤ a
  rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rfl

include hs in
/-- Differential generators, and hence every pulled-back affine differential,
are in the image of the conormal map. -/
lemma conormal_range_pullback [IsAffine C] [QuasiCompact s]
    (m : Γ(f.kaehler, ⊤)) :
    Scheme.Modules.pullbackLocalSection s m ∈
      LinearMap.range ((conormalHom f s).val.app (Opposite.op ⊤)).hom := by
  letI := f.sectionsAlgebra ⊤
  obtain ⟨m, rfl⟩ := (f.kaehlerToSections_bijective_of_isAffineOpen
    (isAffineOpen_top C)).2 m
  have hm : m ∈ Submodule.span Γ(C, ⊤) (Set.range (KaehlerDifferential.D A Γ(C, ⊤))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨a, rfl⟩ := hm
    obtain ⟨x, hx⟩ := ideal_differential_lift f s hs a
    refine ⟨Scheme.Modules.pullbackLocalSection s x, ?_⟩
    exact (conormalHom_D f s ⊤ x).trans
      (congrArg (Scheme.Modules.pullbackLocalSection s) hx)
  | zero =>
    change Scheme.Modules.pullbackLocalSection s (f.kaehlerToSectionsₗ ⊤ 0) ∈ _
    simp only [map_zero, Scheme.Modules.pullbackLocalSection_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    change Scheme.Modules.pullbackLocalSection s (f.kaehlerToSectionsₗ ⊤ (x + y)) ∈ _
    rw [map_add, Scheme.Modules.pullbackLocalSection_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    change Scheme.Modules.pullbackLocalSection s (f.kaehlerToSectionsₗ ⊤ (a • x)) ∈ _
    rw [map_smul, Scheme.Modules.pullbackLocalSection_smul]
    exact Submodule.smul_mem _ _ hx

include hs in
/-- If the relative cotangent module has an affine frame, the conormal map
surjects on the entire identity pullback. -/
lemma conormal_surjective [IsAffine C] [QuasiCompact s]
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ f.kaehler) :
    Function.Surjective ((conormalHom f s).app ⊤) := by
  let q := pullFrame s e.hom
  letI := pullFrame_isIso s e.hom
  intro z
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.Hom.app q) ⊤)).2 z
  change (Scheme.Modules.Hom.app q) ⊤ c ∈ LinearMap.range ((conormalHom f s).val.app (Opposite.op ⊤)).hom
  rw [unit_hom_apply q]
  have hq := conormal_range_pullback f s hs ((Scheme.Modules.Hom.app e.hom) ⊤ (1 : Γ(C, ⊤)))
  rw [← pullFrame_one s e.hom] at hq
  change (show Γ(Spec (CommRingCat.of A), ⊤) from c) • (((Scheme.Modules.pullback s).obj f.kaehler).presheaf.map
    (𝟙 (Opposite.op ⊤))) ((Scheme.Modules.Hom.app q) ⊤ (1 : Γ(Spec (CommRingCat.of A), ⊤))) ∈ _
  rw [((Scheme.Modules.pullback s).obj f.kaehler).presheaf.map_id]
  exact Submodule.smul_mem (LinearMap.range ((conormalHom f s).val.app (Opposite.op ⊤)).hom) c hq

include hs in
/-- The actual conormal map is invertible in a framed affine neighborhood of
the section. In particular, its normalization cannot acquire a vertical zero. -/
lemma conormal_isIso [IsAffine C] [QuasiCompact s]
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ f.kaehler)
    (eI : (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :
      (Spec (CommRingCat.of A)).Modules) ≅
        (Scheme.Modules.pullback s).obj (idealModule s.ker)) :
    IsIso (conormalHom f s) := by
  letI := pullFrame_isIso s e.hom
  exact framed_hom_isIso_of_surjective eI (asIso (pullFrame s e.hom))
    (conormalHom f s) (conormal_surjective f s hs e)

end AffineSection

/-- Invertibility of the conormal map transfers from an affine neighborhood
through comparisons which preserve the actual ideal and derivation. -/
lemma conormal_isIso_of_open {A : Type u} [CommRing A] {C X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : C ⟶ Spec (CommRingCat.of A))
    (j : C ⟶ X) [IsOpenImmersion j] (h : j ≫ f = g)
    (t : Spec (CommRingCat.of A) ⟶ C) (ht : t ≫ g = 𝟙 _)
    [IsAffine C] [QuasiCompact t]
    (eΩ : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ g.kaehler)
    (E : (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :
      (Spec (CommRingCat.of A)).Modules) ≅
        (Scheme.Modules.pullback (t ≫ j)).obj (idealModule (t ≫ j).ker))
    (e : (Scheme.Modules.pullback j).obj (idealModule (t ≫ j).ker) ≅ idealModule t.ker)
    (he : e.hom ≫ idealInclusion t.ker = pulledInclusion j (idealInclusion (t ≫ j).ker)) :
    IsIso (conormalHom f (t ≫ j)) := by
  let E' := E ≪≫ ((Scheme.Modules.pullbackComp t j).app (idealModule (t ≫ j).ker)).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e
  letI := conormal_isIso g t ht eΩ E'
  letI := openDifferential_isIso f g j h
  let q := (Scheme.Modules.pullbackComp t j).inv.app f.kaehler ≫
    (Scheme.Modules.pullback t).map (openDifferential f g j h)
  haveI : IsIso q := by dsimp only [q]; infer_instance
  have hn := conormal_naturality f g j t (openDifferential f g j h)
    (openDifferential_D f g j h) e.hom he
  haveI : IsIso ((Scheme.Modules.pullbackComp t j).hom.app (idealModule (t ≫ j).ker) ≫
      conormalHom f (t ≫ j) ≫ q) := by
    change IsIso ((Scheme.Modules.pullbackComp t j).hom.app (idealModule (t ≫ j).ker) ≫
      conormalHom f (t ≫ j) ≫ (Scheme.Modules.pullbackComp t j).inv.app f.kaehler ≫
      (Scheme.Modules.pullback t).map (openDifferential f g j h))
    rw [← hn]
    infer_instance
  haveI : IsIso (conormalHom f (t ≫ j) ≫ q) := IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullbackComp t j).hom.app (idealModule (t ≫ j).ker)) _
  exact IsIso.of_isIso_comp_right (conormalHom f (t ≫ j)) q

section LocalNormalization
variable {R B N : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

/-- The cleared equation on the second and third powers of a local equation
reduces to the first-order identity. The regularity assumption is exactly the
cancellation needed for the fourth power of that equation. -/
lemma cancel_pole_equation (D : Derivation R B N) (a b g : B) (δ : N)
    (hg : Function.Injective (fun v : N => g ^ 4 • v))
    (h : g ^ 3 • (g ^ 2 • D a - a • D (g ^ 2)) =
      (2 * b * (g ^ 2) ^ 2) • δ) :
    g • D a - (2 * a) • D g = (2 * b) • δ := by
  apply hg
  have hd : D (g ^ 2) = (2 * g) • D g := by
    rw [pow_two, D.leibniz]
    module
  rw [hd] at h
  calc
    g ^ 4 • (g • D a - (2 * a) • D g) =
        g ^ 3 • (g ^ 2 • D a - a • ((2 * g) • D g)) := by module
    _ = (2 * b * (g ^ 2) ^ 2) • δ := h
    _ = g ^ 4 • ((2 * b) • δ) := by module

/-- Evaluation at the identity gives the exact sign and coefficient of the
normalized differential; no leading-term asymptotic is used. -/
lemma evaluate_pole_equation {C P : Type u} [CommRing C] [AddCommGroup P]
    [Module C P] (e : B →+* C) (v : N →ₛₗ[e] P)
    (D : Derivation R B N) (a b g : B) (δ : N)
    (hg : Function.Injective (fun w : N => g ^ 4 • w))
    (h : g ^ 3 • (g ^ 2 • D a - a • D (g ^ 2)) =
      (2 * b * (g ^ 2) ^ 2) • δ)
    (hzero : e g = 0) (h2 : IsUnit (2 : C)) :
    e b • v δ = -(e a • v (D g)) := by
  have hv := congrArg v (cancel_pole_equation D a b g δ hg h)
  simp only [map_sub, LinearMap.map_smulₛₗ, map_mul, map_ofNat,
    hzero, zero_smul, zero_sub] at hv
  apply h2.smul_left_cancel.mp
  calc
    (2 : C) • (e b • v δ) = (2 * e b) • v δ := (mul_smul _ _ _).symm
    _ = -((2 * e a) • v (D g)) := hv.symm
    _ = (2 : C) • -(e a • v (D g)) := by module

end LocalNormalization

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaPolygonCohomologyR0131

/-- Both literal coordinate numerators have value one at the identity, at every
finite thickness. In particular their leading coefficients are integral units. -/
lemma numerator_identity (h3 : 3 ≤ r) (odd : Bool) (n : ℕ) :
    markedPoint k n 1 (numerator k odd r n (zeroIndex r hr)) = 1 := by
  have hx : markedPoint k n 1 (coordX k n) = 1 := by
    simpa [markedUnit] using
      ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137.point_x k n 1
  have he : markedPoint k n 1 (equation k r n (zeroIndex r hr)) = 0 := by
    simp [equation, zeroIndex, show ¬ (1 = r) by omega, hx]
  have hn : ∀ a : ℕ, ¬ (a = 0 ∧ 0 + 1 = r) := by intro a; omega
  cases odd <;>
    simp only [ArithmeticThetaAlgebraicCoordinatesR0143.numerator,
      show (zeroIndex r hr).val = 0 from rfl, hn, Bool.false_eq_true,
      ↓reduceIte, degree, map_mul, map_add, map_sub, map_sum, map_pow, he,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0),
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, sub_zero, hx,
      map_one, one_mul]
  rw [AlgebraicIdentityEvaluationR0140.marked_base]
  have htwo : (2 : k) ≠ 0 := by norm_num
  have ht : trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹) * 2 = 1 := by
      rw [← map_ofNat (trunc (PowerSeries k) PowerSeries.X n) 2, ← map_mul]
      rw [← map_ofNat PowerSeries.C 2, ← map_mul, inv_mul_cancel₀ htwo, map_one, map_one]
  simpa only [one_add_one_eq_two] using ht

/-- Realization identifies the actual completed numerator, rather than merely
its generic rational function. -/
lemma coordinate_formal_numerator (h3 : 3 ≤ r) (odd : Bool) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (n : ℕ) :
    (((AlgebraizedThetaSaturationR0138.algebraicFormal k h3 M hM s hs
      (degree odd) φ).val n).val (zeroIndex r hr)) = numerator k odd r n (zeroIndex r hr) := by
  let i := zeroIndex r hr
  obtain ⟨z, hz, hv⟩ := hφ n i
  obtain ⟨z', hz', hv'⟩ := AlgebraizedThetaSaturationR0138.algebraicFormal_realizes
    k h3 M hM s hs (degree odd) φ n i
  letI := NormalizedIdentityFrameR0140.algebraicChart_mono k h3 M hM s hs (degree odd) n
  have hzz : z = z' := mono_app_injective
    (pulledInclusion (NormalizedIdentityFrameR0140.algebraicChart k M n)
      (idealInclusion (s.ker ^ degree odd))) ⊤ (hz.trans hz'.symm)
  dsimp only [pulledInclusion] at hv'
  rw [hzz, hv'] at hv
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm.injective hv

/-- Exact integral identity value of both coordinates in the normalized ideal
power frame. -/
lemma coordinate_frameValue (h3 : 3 ≤ r) (odd : Bool) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (e : IdentityFrame k M s (degree odd))
    (he : NormalizedFrame k h3 M hM s hs (degree odd) e) :
    frameValue k M s (degree odd) e φ = 1 := by
  apply AlgebraizedThetaSaturationR0138.powerSeries_ext
  intro n
  rw [he φ n, coordinate_formal_numerator k h3 odd M hM s hs φ hφ n,
    numerator_identity k h3 odd n, map_one]

/-- The actual identity pullback of a realized coordinate is an isomorphism.
This rules out any vertical factor in its leading numerator. -/
lemma coordinate_pulled_isIso (h3 : 3 ≤ r) (odd : Bool) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ) :
    IsIso (pulledInclusion s φ) := by
  obtain ⟨e, he⟩ := normalized_identity_frame k r hr h3 T M hM s hs (degree odd)
  have h := NormalizedIdentityFrameR0140.frameValue_morphism k M s (degree odd) e φ
  rw [coordinate_frameValue k h3 odd M hM s hs φ hφ e he, map_one] at h
  have h1 : fromSection (SheafOfModules.unit (baseScheme k).ringCatSheaf :
      (baseScheme k).Modules) (1 : Γ(baseScheme k, ⊤)) = 𝟙 (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules) := by
    apply unit_hom_ext
    simp only [fromSection_apply, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, one_smul]
    rfl
  rw [h1] at h
  have hq : pulledInclusion s φ = e.hom := by
    apply (cancel_epi e.inv).mp
    rw [h, e.inv_hom_id]
  rw [hq]
  infer_instance

/-- An actual affine open neighborhood contains the entire integral identity
section and has a frame for the relative differential of the original map. -/
lemma affine_identity_neighborhood (h3 : 3 ≤ r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    ∃ (C : Scheme.{u}) (_ : IsAffine C) (j : C ⟶ M.X) (_ : IsOpenImmersion j)
      (t : baseScheme k ⟶ C), t ≫ j = s ∧
      Nonempty ((SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ (j ≫ M.p).kaehler) := by
  obtain ⟨W, hxW, hW⟩ := AlgebraizedEffectiveCartierR0136.section_relative_one
    k h3 M hM (zeroIndex r hr) 1 s hs
  obtain ⟨t, ht⟩ := IntegralHodgeFrameR0149.section_factors s W hxW
  letI := hW
  have hΩ : Scheme.Modules.IsInvertible (W.ι ≫ M.p).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
        (W.ι ≫ M.p) 1).1
  obtain ⟨V, htV, _, ⟨eV⟩⟩ := hΩ.exists_restrict_iso
    (show t (IsLocalRing.closedPoint (PowerSeries k)) ∈ (⊤ : W.toScheme.Opens) from trivial)
  obtain ⟨t', ht'⟩ := IntegralHodgeFrameR0149.section_factors t V.val htV
  let j : V.val.toScheme ⟶ M.X := V.val.ι ≫ W.ι
  letI : IsAffine V.val.toScheme := V.property
  refine ⟨V.val.toScheme, inferInstance, j, inferInstance, t', ?_, ?_⟩
  · change t' ≫ V.val.ι ≫ W.ι = s
    rw [← Category.assoc, ht', ht]
  · refine ⟨eV.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.val.ι).app (W.ι ≫ M.p).kaehler ≪≫
      IntegralHodgeFrameR0149.restrictKaehlerIso (W.ι ≫ M.p) V.val ≪≫ ?_⟩
    exact eqToIso (congrArg (fun f => f.kaehler)
      (Category.assoc V.val.ι W.ι M.p).symm)

/-- A common affine neighborhood trivializes both the actual relative
cotangent module and the actual ideal of the identity. -/
lemma affine_identity_equation_neighborhood (h3 : 3 ≤ r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    ∃ (C : Scheme.{u}) (_ : IsAffine C) (j : C ⟶ M.X) (_ : IsOpenImmersion j)
      (t : baseScheme k ⟶ C), t ≫ j = s ∧
      Nonempty ((SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ (j ≫ M.p).kaehler) ∧
      Nonempty ((SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅
        (Scheme.Modules.pullback j).obj (idealModule s.ker)) := by
  obtain ⟨C, hC, j, hj, t, ht, ⟨eΩ⟩⟩ := affine_identity_neighborhood k h3 M hM s hs
  letI := hC
  letI := hj
  have hI : Scheme.Modules.IsInvertible (idealModule s.ker) :=
    (AlgebraizedEffectiveCartierR0136.section_invertible k h3 M hM (zeroIndex r hr) 1 s hs).isInvertible_module
  obtain ⟨V, htV, _, ⟨eI⟩⟩ := (hI.pullback j).exists_restrict_iso
    (show t (IsLocalRing.closedPoint (PowerSeries k)) ∈ (⊤ : C.Opens) from trivial)
  obtain ⟨t', ht'⟩ := IntegralHodgeFrameR0149.section_factors t V.val htV
  letI : IsAffine V.val.toScheme := V.property
  refine ⟨V.val.toScheme, inferInstance, V.val.ι ≫ j, inferInstance, t', ?_, ?_, ?_⟩
  · rw [← Category.assoc, ht', ht]
  · letI := openDifferential_isIso (j ≫ M.p) (V.val.ι ≫ (j ≫ M.p)) V.val.ι rfl
    exact ⟨(Scheme.Modules.pullbackUnitIso V.val.ι).symm ≪≫
      (Scheme.Modules.pullback V.val.ι).mapIso eΩ ≪≫
      asIso (openDifferential (j ≫ M.p) (V.val.ι ≫ (j ≫ M.p)) V.val.ι rfl) ≪≫
      eqToIso (congrArg (fun f => f.kaehler) (Category.assoc V.val.ι j M.p).symm)⟩
  · exact ⟨eI.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.val.ι).app
        ((Scheme.Modules.pullback j).obj (idealModule s.ker)) ≪≫
      (Scheme.Modules.pullbackComp V.val.ι j).app (idealModule s.ker)⟩

/-- The conormal map of the actual algebraized identity section is an
isomorphism over the power-series base. -/
lemma integral_conormal_isIso (h3 : 3 ≤ r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    IsIso (conormalHom M.p s) := by
  obtain ⟨C, hC, j, hj, t, ht, ⟨eΩ⟩⟩ := affine_identity_neighborhood k h3 M hM s hs
  subst s
  letI := hC
  letI := hj
  letI := AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM (t ≫ j) hs.1
  letI : IsClosedImmersion t := IsClosedImmersion.of_comp t j
  obtain ⟨eI, _⟩ := normalized_identity_frame k r hr h3 T M hM (t ≫ j) hs 1
  have hE : Nonempty ((SheafOfModules.unit (baseScheme k).ringCatSheaf :
      (baseScheme k).Modules) ≅ (Scheme.Modules.pullback (t ≫ j)).obj
        (idealModule (t ≫ j).ker)) := by
    exact ⟨by simpa only [IdentityFrame, powerModule, pow_one] using eI.symm⟩
  obtain ⟨E⟩ := hE
  obtain ⟨e, he⟩ := ideal_restriction_iso j t (t ≫ j) rfl
  exact conormal_isIso_of_open M.p (j ≫ M.p) j rfl t
    (by rw [← Category.assoc, hs.1]; rfl) eΩ E e he

/-- Generic restriction is injective on maps into a framed integral Hodge module.
The proof uses schematic density of the actual Laurent-series base map. -/
lemma integral_map_injective (M : Model k T) (s : baseScheme k ⟶ M.X)
    (E : IntegralFrame k M s) (L : (baseScheme k).Modules) :
    Function.Injective (fun q : L ⟶ IntegralHodge k M s =>
      (Scheme.Modules.pullback (genericBase k)).map q) := by
  intro q q' h
  apply (cancel_mono E.inv).mp
  letI := GenericDualLocalizationR0140.genericBase_schematic k
  apply GenericDualLocalizationR0140.restriction_injective (genericBase k) L
  simp only [Functor.map_comp, h]

/-- Two integral frames with the prescribed generic restriction coincide. -/
lemma extendsFrame_unique (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (b : GenericComparison k M)
    (δ : Frame k M) (E F : IntegralFrame k M s)
    (hE : ExtendsFrame k M s hs b E δ)
    (hF : ExtendsFrame k M s hs b F δ) : E = F := by
  apply Iso.ext
  apply integral_map_injective k M s E
  apply (cancel_mono (fiberComparison k M s hs b).hom).mp
  exact hE.trans hF.symm

lemma open_pullback_section_bijective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (L : Y.Modules) (U : Y.Opens) (hU : U ≤ j.opensRange) :
    Function.Bijective (fun s : Γ(L, U) => Scheme.Modules.pullbackLocalSection j s) := by
  have he : j ''ᵁ j ⁻¹ᵁ U = U := by
    rw [j.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hi : IsIso (homOfLE (j.image_preimage_le U)) := by
    rw [show homOfLE (j.image_preimage_le U) = eqToHom he from Subsingleton.elim _ _]
    infer_instance
  have hm := ConcreteCategory.bijective_of_isIso
    (L.presheaf.map (homOfLE (j.image_preimage_le U)).op)
  have hn := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app L).app (j ⁻¹ᵁ U))
  convert hn.comp hm using 1
  funext s
  exact P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.PicTanH.pullbackLocalSection_openImmersion j L U s

lemma frame_smul_bijective {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (z : Γ(L,U)) (hz : Scheme.Modules.IsFrameOn z U) :
    Function.Bijective (fun a : Γ(C,U) => a • z) := by
  simpa using hz (le_refl U) (le_refl U)

lemma realized_frame_principal {C : Scheme.{u}} (I : C.IdealSheafData)
    (L : C.Modules) (i : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    (hi : IdealRealization I L i) (U : C.affineOpens)
    (z : Γ(L,U.val)) (hz : Scheme.Modules.IsFrameOn z U.val) :
    IsRegular (show Γ(C,U.val) from i.app U.val z) ∧
      I.ideal U = Ideal.span ({i.app U.val z} : Set Γ(C,U.val)) := by
  letI := hi.1
  have hs := frame_smul_bijective z hz
  have hreg : Function.Injective (fun a : Γ(C,U.val) => a * (show Γ(C,U.val) from i.app U.val z)) := by
    intro a b hab
    apply hs.1
    apply mono_app_injective i U.val
    simpa only [Scheme.Modules.Hom.app_smul, smul_eq_mul] using hab
  refine ⟨?_, ?_⟩
  · exact ⟨fun x y h => hreg (by simpa only [mul_comm] using h), hreg⟩
  · ext a
    change a ∈ (I.ideal U).carrier ↔ _
    rw [← hi.2 U]
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨c, rfl⟩ := hs.2 v
      exact Ideal.mem_span_singleton'.mpr ⟨c, (Scheme.Modules.Hom.app_smul i c z).symm⟩
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
      exact ⟨c • z, by simpa only [Scheme.Modules.Hom.app_smul, smul_eq_mul] using hc⟩

lemma mono_frame_regular {C : Scheme.{u}} {L : C.Modules}
    (i : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules)) [Mono i]
    (U : C.Opens) (z : Γ(L,U)) (hz : Scheme.Modules.IsFrameOn z U) :
    IsRegular (show Γ(C,U) from i.app U z) := by
  have hreg : Function.Injective (fun a : Γ(C,U) => a * (show Γ(C,U) from i.app U z)) := by
    intro a b hab
    apply (frame_smul_bijective z hz).1
    apply mono_app_injective i U
    exact (Scheme.Modules.Hom.app_smul i a z).trans
      (hab.trans (Scheme.Modules.Hom.app_smul i b z).symm)
  exact ⟨fun x y h => hreg (by simpa only [mul_comm] using h), hreg⟩

lemma regular_smul_on_framed {C : Scheme.{u}} {L : C.Modules}
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ L)
    (U : C.Opens) (g : Γ(C,U)) (hg : IsRegular g) :
    Function.Injective (fun z : Γ(L,U) => g • z) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2 x
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2 y
  apply congrArg (Scheme.Modules.Hom.app e.hom U)
  apply hg.left
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).1
  change Scheme.Modules.Hom.app e.hom U (g • a) = Scheme.Modules.Hom.app e.hom U (g • b)
  simpa only [Scheme.Modules.Hom.app_smul] using hxy

lemma relativeD_cancel_pole {F : Type u} [CommRing F] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens)
    (a b g : Γ(C,U)) (δ : Γ(f.kaehler,U))
    (hg : Function.Injective (fun v : Γ(f.kaehler,U) => g^4 • v))
    (h : g^3 • (g^2 • relativeD f U a - a • relativeD f U (g^2)) =
      (2 * b * (g^2)^2) • δ) :
    g • relativeD f U a - (2 * a) • relativeD f U g = (2 * b) • δ := by
  apply hg
  have hd : relativeD f U (g^2) = (2*g) • relativeD f U g := by
    rw [pow_two, relativeD_mul]
    module
  rw [hd] at h
  calc
    g^4 • (g • relativeD f U a - (2*a) • relativeD f U g) =
        g^3 • (g^2 • relativeD f U a - a • ((2*g) • relativeD f U g)) := by module
    _ = (2*b*(g^2)^2) • δ := h
    _ = g^4 • ((2*b) • δ) := by module
lemma frame_unit_smul {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (z : Γ(L,U)) (hz : Scheme.Modules.IsFrameOn z U) (a : Γ(C,U)) (ha : IsUnit a) :
    Scheme.Modules.IsFrameOn (a • z) U := by
  intro W hWU hWU'
  rw [Scheme.Modules.map_smul]
  have hb := hz hWU hWU'
  have hc : IsUnit (C.presheaf.map (homOfLE hWU).op a) := ha.map _
  obtain ⟨v,hv⟩ := hc
  rw [← hv]
  convert hb.comp (Units.mulRight_bijective v) using 1
  funext b
  exact (mul_smul _ _ _).symm

open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

/-- Each power of an actual regular local equation has its own exact ideal
section, and that section is a frame, not only a nonzero element. -/
lemma principal_power_frame {C : Scheme.{u}} (I : C.IdealSheafData)
    (U : C.affineOpens) (g : Γ(C,U.val)) (hg : IsRegular g)
    (hI : I.ideal U = Ideal.span {g}) (n : ℕ) :
    ∃ z : Γ(idealModule (I^n),U.val),
      (idealInclusion (I^n)).app U.val z = g^n ∧ Scheme.Modules.IsFrameOn z U.val := by
  letI : IsAffine U.val.toScheme := U.property
  have hgen : ((I^n).comap U.val.ι).ideal ⟨⊤, isAffineOpen_top U.val.toScheme⟩ =
      Ideal.span {U.val.topIso.inv (g^n)} := by
    rw [ideal_comap_open_top, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      hI, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  obtain ⟨e⟩ := principal_realization_free _ _ _
    (pullback_open_realization U.val.ι (I^n) _ _ (ideal_realization (I^n))) _
    (regular_equiv U.val.topIso.symm.commRingCatIsoToRingEquiv (hg.pow n)) hgen
  obtain ⟨w, hw⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U.val e
  have hIn : (I^n).ideal U = Ideal.span {g^n} := by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI, Ideal.span_singleton_pow]
  have hnmem : g^n ∈ ((I^n).ideal U).carrier := by
    rw [hIn]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [← (ideal_realization (I^n)).2 U] at hnmem
  obtain ⟨z, hz⟩ := hnmem
  obtain ⟨c, hc⟩ := (frame_smul_bijective w hw).2 z
  letI : Mono (idealInclusion (I^n)) := (ideal_realization (I^n)).1
  have hreg := mono_frame_regular (idealInclusion (I^n)) U.val w hw
  have hwmem : (idealInclusion (I^n)).app U.val w ∈ ((I^n).ideal U).carrier := by
    rw [← (ideal_realization (I^n)).2 U]
    exact ⟨w,rfl⟩
  rw [hIn] at hwmem
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hwmem
  have hcg : c * (show Γ(C,U.val) from (idealInclusion (I^n)).app U.val w) = g^n := by
    rw [← hz, ← hc]
    exact (Scheme.Modules.Hom.app_smul (idealInclusion (I^n)) c w).symm
  let q : Γ(C,U.val) := (idealInclusion (I^n)).app U.val w
  change IsRegular q at hreg
  change c*q = g^n at hcg
  change d*g^n = q at hd
  have hdc : d*c = 1 := hreg.right (by
    change (d*c)*q = 1*q
    rw [mul_assoc, hcg, hd, one_mul])
  have hcu : IsUnit c := isUnit_iff_exists_inv.mpr ⟨d, by simpa only [mul_comm] using hdc⟩
  exact ⟨z,hz,hc ▸ frame_unit_smul w hw c hcu⟩

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaAlgebraicCoordinatesR0143

/-- Cancellation of the pole equation on the actual generic open. Every
numerator here is the image of a section of the actual integral ideal power. -/
lemma generic_local_normalization (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3) (δ : Frame k M)
    (hδ : IsGlobalDifferentialFrame k M s X Y δ)
    (U : M.X.Opens) (g : Γ(M.X,U))
    (z : Γ(idealModule s.ker,U)) (hz : Scheme.Modules.IsFrameOn z U)
    (hzg : (idealInclusion s.ker).app U z = g)
    (z₂ : Γ(powerModule k M s 2,U)) (hz₂ : (idealInclusion (s.ker^2)).app U z₂ = g^2)
    (z₃ : Γ(powerModule k M s 3,U)) (hz₃ : (idealInclusion (s.ker^3)).app U z₃ = g^3) :
    let j := genericInclusion k M
    let V := j ⁻¹ᵁ U
    let gg : Γ(genericScheme k M,V) := j.app U g
    let a : Γ(genericScheme k M,V) := j.app U (X.app U z₂)
    let b : Γ(genericScheme k M,V) := j.app U (Y.app U z₃)
    gg • differentialAt k M V a - (2*a) • differentialAt k M V gg =
      (2*b) • Scheme.Modules.Hom.app δ.hom V (1 : Γ(genericScheme k M,V)) := by
  dsimp only
  let j := genericInclusion k M
  let V := j ⁻¹ᵁ U
  letI : IsOpenImmersion j := AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  let i := pulledInclusion j (idealInclusion s.ker)
  letI : Mono i := (pullback_open_realization j s.ker _ _ (ideal_realization s.ker)).1
  have hreg := mono_frame_regular i V (Scheme.Modules.pullbackLocalSection j z)
    (hz.pullbackLocalSection j)
  have hi : i.app V (Scheme.Modules.pullbackLocalSection j z) = j.app U g := by
    rw [pulled_apply, hzg]
  rw [hi] at hreg
  apply relativeD_cancel_pole (genericStructure k M)
  · exact regular_smul_on_framed δ V _ (hreg.pow 4)
  · have hh := hδ V (Scheme.Modules.pullbackLocalSection j z₂)
        (Scheme.Modules.pullbackLocalSection j z₃)
    let ja : Γ(genericScheme k M,V) := (pulledInclusion j (idealInclusion (s.ker^2))).app V
      (Scheme.Modules.pullbackLocalSection j z₂)
    let jb : Γ(genericScheme k M,V) := (pulledInclusion j (idealInclusion (s.ker^3))).app V
      (Scheme.Modules.pullbackLocalSection j z₃)
    let xa : Γ(genericScheme k M,V) := (pulledInclusion j X).app V
      (Scheme.Modules.pullbackLocalSection j z₂)
    let yb : Γ(genericScheme k M,V) := (pulledInclusion j Y).app V
      (Scheme.Modules.pullbackLocalSection j z₃)
    change jb • (ja • differentialAt k M V xa - xa • differentialAt k M V ja) =
      (2*yb*ja^2) • Scheme.Modules.Hom.app δ.hom V (1 : Γ(genericScheme k M,V)) at hh
    have hja : ja = j.app U (g^2) := (pulled_apply j _ U z₂).trans (congrArg (j.app U) hz₂)
    have hjb : jb = j.app U (g^3) := (pulled_apply j _ U z₃).trans (congrArg (j.app U) hz₃)
    have hxa : xa = j.app U (X.app U z₂) := pulled_apply j _ U z₂
    have hyb : yb = j.app U (Y.app U z₃) := pulled_apply j _ U z₃
    simpa only [hja, hjb, hxa, hyb, map_pow, differentialAt, j, V] using hh

lemma unit_section_isUnit {C : Scheme.{u}} (U : C.Opens) (a : Γ(C,U))
    (ha : Scheme.Modules.IsFrameOn
      (show Γ((SheafOfModules.unit C.ringCatSheaf : C.Modules),U) from a) U) : IsUnit a := by
  obtain ⟨c,hc⟩ := (frame_smul_bijective _ ha).2 (1 : Γ(C,U))
  exact isUnit_iff_exists_inv.mpr ⟨c, by simpa only [smul_eq_mul, mul_comm] using hc⟩

/-- A coordinate evaluated on any actual local ideal-power frame has unit
identity value in the power-series base. -/
lemma coordinate_local_value_unit (h3 : 3 ≤ r) (odd : Bool) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (U : M.X.Opens) (z : Γ(powerModule k M s (degree odd),U))
    (hz : Scheme.Modules.IsFrameOn z U) :
    IsUnit (s.app U (φ.app U z)) := by
  letI := coordinate_pulled_isIso k h3 odd M hM s hs φ hφ
  have h := (hz.pullbackLocalSection s).map_iso (asIso (pulledInclusion s φ))
  have hh := unit_section_isUnit (s ⁻¹ᵁ U)
    (show Γ(baseScheme k,s ⁻¹ᵁ U) from (pulledInclusion s φ).app (s ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection s z)) h
  rwa [pulled_apply] at hh

/-- A regular equation exists on one affine neighborhood containing the entire
integral identity. All of its powers admit exact ideal frames on that same open. -/
lemma integral_identity_local_equation (h3 : 3 ≤ r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    ∃ (U : M.X.affineOpens) (g : Γ(M.X,U.val))
      (z : Γ(idealModule s.ker,U.val)),
      s ⁻¹ᵁ U.val = ⊤ ∧
      (idealInclusion s.ker).app U.val z = g ∧
      Scheme.Modules.IsFrameOn z U.val ∧ IsRegular g ∧
      ∀ n : ℕ, ∃ zn : Γ(idealModule (s.ker^n),U.val),
        (idealInclusion (s.ker^n)).app U.val zn = g^n ∧ Scheme.Modules.IsFrameOn zn U.val := by
  have hI : Scheme.Modules.IsInvertible (idealModule s.ker) :=
    (AlgebraizedEffectiveCartierR0136.section_invertible k h3 M hM (zeroIndex r hr) 1 s hs).isInvertible_module
  obtain ⟨U,hxU,_,⟨e⟩⟩ := hI.exists_restrict_iso
    (show s (IsLocalRing.closedPoint (PowerSeries k)) ∈ (⊤ : M.X.Opens) from trivial)
  obtain ⟨z,hz⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U.val
    (((Scheme.Modules.restrictFunctorIsoPullback U.val.ι).app (idealModule s.ker)).symm ≪≫ e)
  obtain ⟨t,ht⟩ := IntegralHodgeFrameR0149.section_factors s U.val hxU
  have hpre : s ⁻¹ᵁ U.val = ⊤ := by
    rw [← ht, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  obtain ⟨hg,hgen⟩ := realized_frame_principal s.ker _ _ (ideal_realization s.ker) U z hz
  refine ⟨U,(idealInclusion s.ker).app U.val z,z,hpre,rfl,hz,hg,?_⟩
  intro n
  exact principal_power_frame s.ker U _ hg hgen n


/-- Regard a local section whose domain is the entire scheme as a global section. -/
def topSection {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (h : U = ⊤) (z : Γ(L,U)) : Γ(L,⊤) := L.presheaf.map (eqToHom h.symm).op z

def topScalar {C : Scheme.{u}} {U : C.Opens} (h : U = ⊤) : Γ(C,U) →+* Γ(C,⊤) :=
  (C.presheaf.map (eqToHom h.symm).op).hom

lemma topSection_map {C : Scheme.{u}} {L N : C.Modules} {U : C.Opens}
    (q : L ⟶ N) (h : U = ⊤) (z : Γ(L,U)) :
    q.app ⊤ (topSection h z) = topSection h (q.app U z) := by
  subst U
  simp [topSection]

lemma topSection_smul {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (h : U = ⊤) (a : Γ(C,U)) (z : Γ(L,U)) :
    topSection h (a • z) = topScalar h a • topSection h z := by
  subst U
  simp [topSection, topScalar]

lemma topSection_frame {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (h : U = ⊤) (z : Γ(L,U)) (hz : Scheme.Modules.IsFrameOn z U) :
    Scheme.Modules.IsFrameOn (topSection h z) ⊤ := by
  subst U
  simpa [topSection] using hz

lemma pullback_topSection {C S : Scheme.{u}} (f : S ⟶ C) {L : C.Modules} {U : C.Opens}
    (h : U = ⊤) (z : Γ(L,U)) (hf : f ⁻¹ᵁ U = ⊤) :
    Scheme.Modules.pullbackLocalSection f (topSection h z) =
      topSection hf (Scheme.Modules.pullbackLocalSection f z) := by
  subst U
  simp [topSection]

lemma pullback_comp_topSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (U : Z.Opens) (z : Γ(L,U))
    (hg : g ⁻¹ᵁ U = ⊤) (hfg : (f ≫ g) ⁻¹ᵁ U = ⊤) :
    ((Scheme.Modules.pullbackComp f g).hom.app L).app ⊤
      (Scheme.Modules.pullbackLocalSection f (topSection hg (Scheme.Modules.pullbackLocalSection g z))) =
        topSection hfg (Scheme.Modules.pullbackLocalSection (f ≫ g) z) := by
  rw [pullback_topSection f hg _ hfg, topSection_map]
  exact congrArg (topSection hfg) (pullback_comp f g L U z)

lemma pullback_comp_inv_topSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (U : Z.Opens) (z : Γ(L,U)) (hfg : (f ≫ g) ⁻¹ᵁ U = ⊤) :
    ((Scheme.Modules.pullbackComp f g).inv.app L).app ⊤
      (topSection hfg (Scheme.Modules.pullbackLocalSection (f ≫ g) z)) =
        topSection hfg (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g z)) := by
  rw [topSection_map, pullback_comp_inv]

lemma pullback_congr_topSection {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (L : Y.Modules) (U : Y.Opens) (z : Γ(L,U))
    (hf : f ⁻¹ᵁ U = ⊤) (hg : g ⁻¹ᵁ U = ⊤) :
    ((Scheme.Modules.pullbackCongr h).hom.app L).app ⊤
      (topSection hf (Scheme.Modules.pullbackLocalSection f z)) =
        topSection hg (Scheme.Modules.pullbackLocalSection g z) := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

lemma squareIso_topSection {X Y A B : Scheme.{u}} (j : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (h : a ≫ j = g ≫ b)
    (L : Y.Modules) (U : Y.Opens) (z : Γ(L,U))
    (hb : b ⁻¹ᵁ U = ⊤) (ha : (a ≫ j) ⁻¹ᵁ U = ⊤) :
    (squareIso j a b g h L).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection g (topSection hb (Scheme.Modules.pullbackLocalSection b z))) =
    topSection ha (Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection j z)) := by
  have hgb : (g ≫ b) ⁻¹ᵁ U = ⊤ := h ▸ ha
  change ((Scheme.Modules.pullbackComp a j).inv.app L).app ⊤
    (((Scheme.Modules.pullbackCongr h.symm).hom.app L).app ⊤
      (((Scheme.Modules.pullbackComp g b).hom.app L).app ⊤
        (Scheme.Modules.pullbackLocalSection g (topSection hb (Scheme.Modules.pullbackLocalSection b z))))) = _
  rw [pullback_comp_topSection g b L U z hb hgb,
    pullback_congr_topSection h.symm L U z hgb ha,
    pullback_comp_inv_topSection]
lemma square_topScalar {X Y A B : Scheme.{u}} (j : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (h : a ≫ j = g ≫ b)
    (U : Y.Opens) (z : Γ(Y,U)) (hb : b ⁻¹ᵁ U = ⊤) (ha : (a ≫ j) ⁻¹ᵁ U = ⊤) :
    topScalar ha (a.app (j ⁻¹ᵁ U) (j.app U z)) =
      g.appTop (topScalar hb (b.app U z)) := by
  change (j.app U ≫ a.appLE (j ⁻¹ᵁ U) ⊤ ha.ge) z =
    (b.appLE U ⊤ hb.ge ≫ g.appTop) z
  rw [← Scheme.Hom.comp_appLE]
  have H := Scheme.Hom.appLE_comp_appLE g b U ⊤ ⊤ hb.ge (le_refl _)
  have htop : g.appLE ⊤ ⊤ (le_refl _) = g.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [htop] at H
  rw [H]
  congr 2
  have hc (v w : A ⟶ Y) (e : v = w) (hv : ⊤ ≤ v ⁻¹ᵁ U) (hw : ⊤ ≤ w ⁻¹ᵁ U) :
      v.appLE U ⊤ hv = w.appLE U ⊤ hw := by subst w; rfl
  exact hc _ _ h _ _

lemma pullFrame_local_one {C S : Scheme.{u}} (p : S ⟶ C) {L : C.Modules}
    (q : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ⟶ L)
    (U : C.Opens) (hU : p ⁻¹ᵁ U = ⊤) :
    topSection hU (Scheme.Modules.pullbackLocalSection p
      (Scheme.Modules.Hom.app q U (1 : Γ(C,U)))) =
      Scheme.Modules.Hom.app (ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.pullFrame p q)
        ⊤ (1 : Γ(S,⊤)) := by
  rw [pullFrame_one]
  have hq : Scheme.Modules.Hom.app q U (1 : Γ(C,U)) =
      L.presheaf.map (homOfLE le_top).op (Scheme.Modules.Hom.app q ⊤ (1 : Γ(C,⊤))) := by
    have hn := ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf q).naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
      (1 : Γ(C,⊤))
    change Scheme.Modules.Hom.app q U (C.presheaf.map (homOfLE le_top).op (1 : Γ(C,⊤))) =
      L.presheaf.map (homOfLE le_top).op (Scheme.Modules.Hom.app q ⊤ (1 : Γ(C,⊤))) at hn
    simpa only [map_one] using hn
  rw [hq, ← Scheme.Modules.map_homOfLE_pullbackLocalSection]
  dsimp only [topSection]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  have hid : (homOfLE (show p ⁻¹ᵁ U ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial)).op ≫
      (eqToHom hU.symm).op = 𝟙 (Opposite.op (⊤ : S.Opens)) := Subsingleton.elim _ _
  rw [hid]
  erw [CategoryTheory.Functor.map_id]
  rfl

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147

lemma squareComparison_topSection {X Y A B : Scheme.{u}} (j : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (h : a ≫ j = g ≫ b)
    (L : Y.Modules) (N : X.Modules) (β : (Scheme.Modules.pullback j).obj L ⟶ N)
    (U : Y.Opens) (z : Γ(L,U)) (w : Γ(N,j ⁻¹ᵁ U))
    (hw : β.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j z) = w)
    (hb : b ⁻¹ᵁ U = ⊤) (ha : (a ≫ j) ⁻¹ᵁ U = ⊤) :
    ((squareIso j a b g h L).hom ≫ (Scheme.Modules.pullback a).map β).app ⊤
      (Scheme.Modules.pullbackLocalSection g (topSection hb (Scheme.Modules.pullbackLocalSection b z))) =
    topSection ha (Scheme.Modules.pullbackLocalSection a w) := by
  change ((Scheme.Modules.pullback a).map β).app ⊤
    ((squareIso j a b g h L).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection g (topSection hb (Scheme.Modules.pullbackLocalSection b z)))) = _
  rw [squareIso_topSection _ _ _ _ _ _ U _ hb ha, topSection_map]
  exact congrArg (topSection ha) ((Scheme.Modules.pullbackLocalSection_app a β
    (Scheme.Modules.pullbackLocalSection j z)).symm.trans
      (congrArg (Scheme.Modules.pullbackLocalSection a) hw))

lemma fiberComparison_D_local (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (b : GenericComparison k M)
    (hb : IsGenericComparison k M b) (U : M.X.Opens) (z : Γ(M.X,U))
    (hU : s ⁻¹ᵁ U = ⊤)
    (hV : (genericPoint k M s hs ≫ genericInclusion k M) ⁻¹ᵁ U = ⊤) :
    (fiberComparison k M s hs b).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericBase k)
        (topSection hU (Scheme.Modules.pullbackLocalSection s (relativeD M.p U z)))) =
    topSection hV (Scheme.Modules.pullbackLocalSection (genericPoint k M s hs)
      (differentialAt k M (genericInclusion k M ⁻¹ᵁ U) ((genericInclusion k M).app U z))) := by
  exact squareComparison_topSection (genericInclusion k M) (genericPoint k M s hs) s (genericBase k)
    (by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericInclusion]) M.p.kaehler (genericStructure k M).kaehler b.hom
    U (relativeD M.p U z) _ (hb U z) hU hV


/-- A checked scalar equation with integral unit coefficients constructs the
exact frame through the given sheaf comparison. -/
lemma frame_from_unit_normalization {S K : Scheme.{u}} (f : K ⟶ S)
    (L : S.Modules) (N : K.Modules)
    (b : (Scheme.Modules.pullback f).obj L ≅ N)
    (δ : (SheafOfModules.unit K.ringCatSheaf : K.Modules) ≅ N)
    (ω : Γ(L,⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (α β : Γ(S,⊤)) (hα : IsUnit α) (hβ : IsUnit β)
    (h : f.appTop β • Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(K,⊤)) =
      -(f.appTop α • Scheme.Modules.Hom.app b.hom ⊤ (Scheme.Modules.pullbackLocalSection f ω))) :
    ∃ E : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ L,
      (Scheme.Modules.pullback f).map E.hom ≫ b.hom = unitPullback f ≫ δ.hom := by
  obtain ⟨ua,hua⟩ := hα
  obtain ⟨ub,hub⟩ := hβ
  let c : Γ(S,⊤) := -(↑ua * ↑ub⁻¹)
  have hc : IsUnit c := (ua.isUnit.mul (ub⁻¹).isUnit).neg
  have hbc : β*c = -α := by
    rw [← hua, ← hub]
    dsimp only [c]
    simp [mul_comm, mul_left_comm]
  obtain ⟨E,hE⟩ := iso_of_global_frame (c • ω) (frame_unit_smul ω hω c hc)
  refine ⟨E, ?_⟩
  letI := unitPullback_isIso f
  apply (cancel_epi (inv (unitPullback f))).mp
  rw [← Category.assoc (inv (unitPullback f)), IsIso.inv_hom_id_assoc]
  apply unit_hom_ext
  change Scheme.Modules.Hom.app b.hom ⊤
    (Scheme.Modules.Hom.app (pullFrame f E.hom) ⊤ (1 : Γ(K,⊤))) =
      Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(K,⊤))
  rw [pullFrame_one, hE ⊤]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
    Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  have hβg : IsUnit (f.appTop β) := (show IsUnit β from ⟨ub,hub⟩).map f.appTop.hom
  apply hβg.smul_left_cancel.mp
  rw [← mul_smul]
  have he : f.appTop β * f.appTop c = -(f.appTop α) := by
    rw [← map_mul, hbc, map_neg]
  change (f.appTop β * f.appTop c) •
    Scheme.Modules.Hom.app b.hom ⊤ (Scheme.Modules.pullbackLocalSection f ω) = _
  rw [he, neg_smul]
  exact h.symm

lemma topSection_sub {C : Scheme.{u}} {L : C.Modules} {U : C.Opens}
    (h : U = ⊤) (x y : Γ(L,U)) : topSection h (x-y) = topSection h x - topSection h y :=
  map_sub _ _ _

/-- Evaluation of the first-order identity, with the exact factor of two. -/
lemma evaluate_first_order {C S : Scheme.{u}} (p : S ⟶ C)
    (L : C.Modules) (U : C.Opens) (hU : p ⁻¹ᵁ U = ⊤)
    (a b g : Γ(C,U)) (Da Dg δ : Γ(L,U))
    (h : g • Da - (2*a) • Dg = (2*b) • δ)
    (hg : topScalar hU (p.app U g) = 0) (h2 : IsUnit (2 : Γ(S,⊤))) :
    topScalar hU (p.app U b) • topSection hU (Scheme.Modules.pullbackLocalSection p δ) =
      -(topScalar hU (p.app U a) • topSection hU (Scheme.Modules.pullbackLocalSection p Dg)) := by
  have hv := congrArg (fun z => topSection hU (Scheme.Modules.pullbackLocalSection p z)) h
  simp only [Scheme.Modules.pullbackLocalSection_sub, Scheme.Modules.pullbackLocalSection_smul,
    topSection_sub, topSection_smul, map_mul, map_ofNat, hg, zero_smul, zero_sub] at hv
  apply h2.smul_left_cancel.mp
  calc
    (2 : Γ(S,⊤)) • (topScalar hU (p.app U b) •
        topSection hU (Scheme.Modules.pullbackLocalSection p δ)) =
      (2 * topScalar hU (p.app U b)) • topSection hU (Scheme.Modules.pullbackLocalSection p δ) :=
        (mul_smul _ _ _).symm
    _ = -((2 * topScalar hU (p.app U a)) • topSection hU (Scheme.Modules.pullbackLocalSection p Dg)) := hv.symm
    _ = (2 : Γ(S,⊤)) • -(topScalar hU (p.app U a) •
        topSection hU (Scheme.Modules.pullbackLocalSection p Dg)) := by module


/-- The exact generic normalization equation in the actual identity Hodge
fiber, with its coefficients taken from the integral base. -/
lemma integral_local_normalization (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k))
    (X : Dual k M s 2) (Y : Dual k M s 3) (δ : Frame k M)
    (hδ : IsGlobalDifferentialFrame k M s X Y δ)
    (b : GenericComparison k M) (hb : IsGenericComparison k M b)
    (U : M.X.Opens) (hU : s ⁻¹ᵁ U = ⊤) (g : Γ(M.X,U))
    (z : Γ(idealModule s.ker,U)) (hz : Scheme.Modules.IsFrameOn z U)
    (hzg : (idealInclusion s.ker).app U z = g)
    (z₂ : Γ(powerModule k M s 2,U)) (hz₂ : (idealInclusion (s.ker^2)).app U z₂ = g^2)
    (z₃ : Γ(powerModule k M s 3,U)) (hz₃ : (idealInclusion (s.ker^3)).app U z₃ = g^3) :
    (genericBase k).appTop (topScalar hU (s.app U (Y.app U z₃))) •
      Scheme.Modules.Hom.app (hodgeFrame k M s hs δ).hom ⊤
        (1 : Γ(Spec (CommRingCat.of (LaurentSeries k)),⊤)) =
    -((genericBase k).appTop (topScalar hU (s.app U (X.app U z₂))) •
      Scheme.Modules.Hom.app (fiberComparison k M s hs b).hom ⊤
        (Scheme.Modules.pullbackLocalSection (genericBase k)
          (topSection hU (Scheme.Modules.pullbackLocalSection s (relativeD M.p U g))))) := by
  let j := genericInclusion k M
  let p := ArithmeticThetaGenericEvaluationR0140.genericPoint k M s hs
  let V := j ⁻¹ᵁ U
  have hsquare : p ≫ j = genericBase k ≫ s := by
    simp [p,j,ArithmeticThetaGenericEvaluationR0140.genericPoint,genericInclusion]
  have hp : (p ≫ j) ⁻¹ᵁ U = ⊤ := by
    rw [hsquare, Scheme.Hom.comp_preimage, hU, Scheme.Hom.preimage_top]
  have hg0 : s.app U g = 0 := by
    rw [← hzg]
    exact ideal_app_zero s U z
  have hg0' : topScalar hp (p.app V (j.app U g)) = 0 := by
    rw [square_topScalar j p s (genericBase k) hsquare U g hU hp, hg0, map_zero, map_zero]
  have h2 : IsUnit (2 : Γ(Spec (CommRingCat.of (LaurentSeries k)),⊤)) := by
    have htwo : IsUnit (2 : LaurentSeries k) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2:k) ≠ 0)).map
        (algebraMap k (LaurentSeries k))
    simpa only [map_ofNat] using htwo.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom
  have hn := generic_local_normalization k M s X Y δ hδ U g z hz hzg z₂ hz₂ z₃ hz₃
  let Ω : (genericScheme k M).Modules := (genericStructure k M).kaehler
  have he := evaluate_first_order p Ω V hp
    (j.app U (X.app U z₂)) (j.app U (Y.app U z₃)) (j.app U g)
    (differentialAt k M V (j.app U (X.app U z₂)))
    (differentialAt k M V (j.app U g))
    (Scheme.Modules.Hom.app δ.hom V (1 : Γ(genericScheme k M,V))) hn hg0' h2
  dsimp only [V] at he
  erw [square_topScalar j p s (genericBase k) hsquare U (Y.app U z₃) hU hp,
    square_topScalar j p s (genericBase k) hsquare U (X.app U z₂) hU hp,
    pullFrame_local_one p δ.hom (j ⁻¹ᵁ U) hp] at he
  erw [← fiberComparison_D_local k M s hs b hb U g hU hp] at he
  exact he

/-- The differential of an actual local identity equation is a frame of the
actual integral identity cotangent sheaf. -/
lemma local_conormal_frame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (U : M.X.Opens) (hU : s ⁻¹ᵁ U = ⊤) (g : Γ(M.X,U))
    (z : Γ(idealModule s.ker,U)) (hz : Scheme.Modules.IsFrameOn z U)
    (hzg : (idealInclusion s.ker).app U z = g) :
    Scheme.Modules.IsFrameOn
      (topSection hU (Scheme.Modules.pullbackLocalSection s (relativeD M.p U g))) ⊤ := by
  letI := integral_conormal_isIso k h3 M hM s hs
  have h := (hz.pullbackLocalSection s).map_iso (asIso (conormalHom M.p s))
  change Scheme.Modules.IsFrameOn ((conormalHom M.p s).app (s ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection s z)) (s ⁻¹ᵁ U) at h
  rw [conormalHom_D, hzg] at h
  exact topSection_frame hU _ h


end ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.extendsFrame_unique
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.conormalHom_D
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.evaluate_pole_equation
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.conormal_isIso
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.affine_identity_neighborhood

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.coordinate_pulled_isIso

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.openDifferential_isIso
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.ideal_restriction_iso
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.pullback_comp

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.conormal_naturality

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.integral_conormal_isIso

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.affine_identity_equation_neighborhood

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.generic_local_normalization
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.integral_identity_local_equation
#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.coordinate_local_value_unit

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.fiberComparison_D_local

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.square_topScalar

#print axioms ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149.frame_from_unit_normalization

namespace ArithmeticThetaIntegralHodgeR0149
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaCompactifiedDifferentialR0145
open NormalizedIntegralHodgeFrameR0149

theorem normalized_integral_hodge_frame : ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (b : ArithmeticThetaIntegralHodgeR0149.GenericComparison k M), ArithmeticThetaIntegralHodgeR0149.IsGenericComparison k M b → ∃! E : ArithmeticThetaIntegralHodgeR0149.IntegralFrame k M s, ArithmeticThetaIntegralHodgeR0149.ExtendsFrame k M s hs.1 b E δ := by
  intro k _ _ r hr h3 T _ M hM s hs X Y hX hY δ hδ b hb
  obtain ⟨U,g,z,hU,hzg,hz,hg,hpow⟩ := integral_identity_local_equation k h3 M hM s hs
  obtain ⟨z₂,hz₂,hf₂⟩ := hpow 2
  obtain ⟨z₃,hz₃,hf₃⟩ := hpow 3
  let α : Γ(baseScheme k,⊤) := topScalar hU (s.app U.val (X.app U.val z₂))
  let β : Γ(baseScheme k,⊤) := topScalar hU (s.app U.val (Y.app U.val z₃))
  let ω : Γ(IntegralHodge k M s,⊤) := topSection hU
    (Scheme.Modules.pullbackLocalSection s (relativeD M.p U.val g))
  have hα : IsUnit α := (coordinate_local_value_unit k h3 false M hM s hs X hX U.val z₂ hf₂).map (topScalar hU)
  have hβ : IsUnit β := (coordinate_local_value_unit k h3 true M hM s hs Y hY U.val z₃ hf₃).map (topScalar hU)
  have hω : Scheme.Modules.IsFrameOn ω ⊤ := local_conormal_frame k h3 M hM s hs U.val hU g z hz hzg
  have hn := integral_local_normalization k M s hs.1 X Y δ hδ b hb U.val hU g z hz hzg z₂ hz₂ z₃ hz₃
  obtain ⟨E,hE⟩ := frame_from_unit_normalization (genericBase k)
    (IntegralHodge k M s) (Hodge k M s hs.1) (fiberComparison k M s hs.1 b)
    (hodgeFrame k M s hs.1 δ) ω hω α β hα hβ hn
  refine ⟨E,hE,?_⟩
  intro E' hE'
  exact extendsFrame_unique k M s hs.1 b δ E' E hE' hE

end ArithmeticThetaIntegralHodgeR0149
#print axioms ArithmeticThetaIntegralHodgeR0149.normalized_integral_hodge_frame
