module

public import GlobalCartierIdealLineR0133
public import MarkedIdealTowerBaseChangeR0133

@[expose] public section

/-! Canonical comparisons for realized Cartier ideals. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace CanonicalCartierLineReductionR0133
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalCartierIdealLineR0133 TopologicalSpace

lemma hom_ext_affine {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U : X.affineOpens, f.app U.1 = g.app U.1) : f = g := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext M.presheaf ⟨N.presheaf, N.isSheaf⟩
    (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens)
  exact h

lemma realization_condition {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) : j ≫ quotientMap I = 0 := by
  apply hom_ext_affine
  intro U
  ext s
  have hs : j.app U.1 s ∈ (I.ideal U).carrier := by
    rw [← hj.2 U]
    exact ⟨s, rfl⟩
  rw [← I.ker_subschemeι_app U] at hs
  exact hs

/-- Every realization is canonically isomorphic, over the structure sheaf,
to the categorical kernel realization. -/
def toKernel {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) : M ⟶ idealModule I :=
  kernel.lift (quotientMap I) j (realization_condition I M j hj)

@[reassoc (attr := simp)]
lemma toKernel_inclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) : toKernel I M j hj ≫ idealInclusion I = j := by
  exact kernel.lift_ι _ _ _

lemma toKernel_isIso {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) : IsIso (toKernel I M j hj) := by
  letI : Mono j := hj.1
  letI : Mono (idealInclusion I) := (ideal_realization I).1
  let φ := toKernel I M j hj
  have he (U : X.Opens) (s : Γ(M, U)) :
      (idealInclusion I).app U (φ.app U s) = j.app U s :=
    ConcreteCategory.congr_hom (congrArg (fun q => Scheme.Modules.Hom.app q U)
      (toKernel_inclusion I M j hj)) s
  let H := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hH : IsIso H := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : X.affineOpens => U.1)
      (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens)
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      apply mono_app_injective j U.1
      exact (he _ _).symm.trans ((congrArg ((idealInclusion I).app U.1) hxy).trans (he _ _))
    · intro z
      have hz : (idealInclusion I).app U.1 z ∈ (I.ideal U).carrier := by
        rw [← (ideal_realization I).2 U]
        exact ⟨z, rfl⟩
      rw [← hj.2 U] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨t, mono_app_injective (idealInclusion I) U.1 ?_⟩
      exact (he _ _).trans ht
  letI := hH
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact inferInstanceAs (IsIso (H.hom.app (Opposite.op U)))

lemma realization_unique_iso {X : Scheme.{u}} (I : X.IdealSheafData)
    (M L : X.Modules)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (l : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (hl : IdealRealization I L l) :
    ∃! e : M ≅ L, e.hom ≫ l = j := by
  letI := toKernel_isIso I M j hj
  letI := toKernel_isIso I L l hl
  letI : Mono l := hl.1
  let e := asIso (toKernel I M j hj) ≪≫ (asIso (toKernel I L l hl)).symm
  have hi : inv (toKernel I L l hl) ≫ l = idealInclusion I := by
    have hh := congrArg (fun q => inv (toKernel I L l hl) ≫ q)
      (toKernel_inclusion I L l hl)
    simpa only [IsIso.inv_hom_id_assoc] using hh.symm
  have he : e.hom ≫ l = j := by
    change (toKernel I M j hj ≫ inv (toKernel I L l hl)) ≫ l = j
    rw [Category.assoc, hi, toKernel_inclusion]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_mono l).mp
  exact he'.trans he.symm

/-- Ideal containment provides the adjoint comparison even without flatness. -/
lemma pushforward_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hIJ : I.comap f ≤ J)
    (M : Y.Modules) (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (hj : IdealRealization I M j) :
    (j ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforward f).map (quotientMap J) = 0 := by
  apply hom_ext_affine
  intro U
  ext s
  have hs : j.app U.1 s ∈ (I.ideal U).carrier := by
    rw [← hj.2 U]
    exact ⟨s, rfl⟩
  have ht := (Scheme.IdealSheafData.le_map_iff_comap_le.mpr hIJ) U hs
  exact Scheme.Hom.ideal_ker_le (J.subschemeι ≫ f) U ht

def adjointComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hIJ : I.comap f ≤ J)
    (M : Y.Modules) (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (hj : IdealRealization I M j) :
    M ⟶ (Scheme.Modules.pushforward f).obj (idealModule J) :=
  kernel.lift ((Scheme.Modules.pushforward f).map (quotientMap J))
    (j ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (pushforward_condition f I J hIJ M j hj) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward f) (quotientMap J)).inv

@[reassoc (attr := simp)]
lemma adjointComparison_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hIJ : I.comap f ≤ J)
    (M : Y.Modules) (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (hj : IdealRealization I M j) :
    adjointComparison f I J hIJ M j hj ≫
      (Scheme.Modules.pushforward f).map (idealInclusion J) =
        j ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  simp [adjointComparison, idealInclusion, PreservesKernel.iso_inv_ι]

def comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hIJ : I.comap f ≤ J)
    (M : Y.Modules) (L : X.Modules) (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (l : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (hl : IdealRealization J L l) :
    (Scheme.Modules.pullback f).obj M ⟶ L := by
  letI := toKernel_isIso J L l hl
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (adjointComparison f I J hIJ M j hj) ≫ inv (toKernel J L l hl)

@[reassoc]
lemma comparison_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hIJ : I.comap f ≤ J)
    (M : Y.Modules) (L : X.Modules) (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (l : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (hl : IdealRealization J L l) :
    comparison f I J hIJ M L j l hj hl ≫ l =
      (Scheme.Modules.pullback f).map j ≫ unitPullback f := by
  letI := toKernel_isIso J L l hl
  have hi : inv (toKernel J L l hl) ≫ l = idealInclusion J := by
    have hh := congrArg (fun q => inv (toKernel J L l hl) ≫ q)
      (toKernel_inclusion J L l hl)
    simpa only [IsIso.inv_hom_id_assoc] using hh.symm
  unfold comparison
  rw [Category.assoc, hi]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    adjointComparison_inclusion, Adjunction.homEquiv_naturality_left]
  change j ≫ _ = j ≫ ((SheafOfModules.pullbackPushforwardAdjunction _).homEquiv _ _)
    (((SheafOfModules.pullbackPushforwardAdjunction _).homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]

local instance unitSectionsCommRing (X : Scheme.{u}) (U : X.Opens) :
    CommRing Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) :=
  inferInstanceAs (CommRing (X.presheaf.obj (Opposite.op U)))

lemma unit_hom_apply {X : Scheme.{u}} {M : X.Modules}
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M)
    (U : X.Opens) (s : Γ(X, U)) :
    (Scheme.Modules.Hom.app φ) U s = s • M.presheaf.map (homOfLE le_top).op ((Scheme.Modules.Hom.app φ) ⊤ (1 : Γ(X, ⊤))) := by
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change (Scheme.Modules.Hom.app φ) U (X.presheaf.map (homOfLE le_top).op 1) =
    M.presheaf.map (homOfLE le_top).op ((Scheme.Modules.Hom.app φ) ⊤ (1 : Γ(X, ⊤))) at hn
  rw [map_one] at hn
  rw [← hn, ← Scheme.Modules.Hom.app_smul]
  congr 1
  exact mul_one s |>.symm

lemma unit_hom_ext {X : Scheme.{u}} {M : X.Modules}
    {φ ψ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M}
    (h : (Scheme.Modules.Hom.app φ) ⊤ (1 : Γ(X, ⊤)) = (Scheme.Modules.Hom.app ψ) ⊤ (1 : Γ(X, ⊤))) : φ = ψ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [unit_hom_apply φ U s, unit_hom_apply ψ U s, h]

lemma unitEnd_isIso {X : Scheme.{u}}
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hφ : Function.Bijective ((Scheme.Modules.Hom.app φ) ⊤)) : IsIso (C := X.Modules) φ := by
  obtain ⟨c, hc⟩ := hφ.2 (1 : Γ(X, ⊤))
  have hc' : (c : Γ(X, ⊤)) * ((Scheme.Modules.Hom.app φ) ⊤ (1 : Γ(X, ⊤)) : Γ(X, ⊤)) = 1 := by
    have ht := unit_hom_apply φ ⊤ (c : Γ(X, ⊤))
    have hid : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_refl _)).op = 𝟙 _ := rfl
    rw [hid, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at ht
    exact ht.symm.trans hc
  let ψ := fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) c
  have hψ : (Scheme.Modules.Hom.app ψ) ⊤ (1 : Γ(X, ⊤)) = c := by simp [ψ, fromSection_apply]
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply unit_hom_ext
    change (Scheme.Modules.Hom.app ψ) ⊤ ((Scheme.Modules.Hom.app φ) ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))
    rw [unit_hom_apply ψ ⊤ _, hψ]
    simpa [mul_comm] using hc'
  · apply unit_hom_ext
    change (Scheme.Modules.Hom.app φ) ⊤ ((Scheme.Modules.Hom.app ψ) ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))
    rw [hψ]
    exact hc

lemma free_hom_isIso_of_top {X : Scheme.{u}} (M : X.Modules)
    (hM : Nonempty (M ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M)
    (hφ : Function.Bijective ((Scheme.Modules.Hom.app φ) ⊤)) : IsIso (C := X.Modules) φ := by
  obtain ⟨e⟩ := hM
  have h : IsIso (C := X.Modules) (φ ≫ e.hom) := unitEnd_isIso _
    ((ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).comp hφ)
  letI := h
  exact IsIso.of_isIso_comp_right φ e.hom

lemma principal_frame {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (M : X.Modules)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (p : Γ(X, ⊤)) (hp : IsRegular p)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span ({p} : Set _))
    (t : Γ(M, ⊤)) (ht : j.app ⊤ t = p) : IsIso (C := X.Modules) (fromSection M t) := by
  letI : Mono j := hj.1
  apply free_hom_isIso_of_top M (principal_realization_free I M j hj p hp hI)
  have he (s : Γ(X, ⊤)) : j.app ⊤ ((fromSection M t).app ⊤ s) = s * p := by
    simpa [ht] using fromSection_image M j t ⊤ s
  constructor
  · intro x y hxy
    apply hp.right
    exact (he x).symm.trans ((congrArg (j.app ⊤) hxy).trans (he y))
  · intro z
    have hz : j.app ⊤ z ∈ (I.ideal ⟨⊤, isAffineOpen_top X⟩).carrier := by
      rw [← hj.2 ⟨⊤, isAffineOpen_top X⟩]
      exact ⟨z, rfl⟩
    rw [hI] at hz
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (α := Γ(X, ⊤))).mp hz
    exact ⟨c, mono_app_injective j ⊤ ((he c).trans hc)⟩

lemma unitPullback_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (unitPullback f) := by
  letI : (Opens.map f.base).Final := by
    constructor
    intro U
    let Z : StructuredArrow U (Opens.map f.base) :=
      StructuredArrow.mk (Y := ⊤) (homOfLE le_top)
    apply isConnected_of_isTerminal _ (x := Z)
    exact IsTerminal.ofUniqueHom (fun V => StructuredArrow.homMk (homOfLE le_top))
      (fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))
  unfold unitPullback
  change IsIso (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom)
  infer_instance

lemma pullback_multiplication {X Y : Scheme.{u}} (f : X ⟶ Y) (p : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map
        (fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) p) ≫
      unitPullback f =
    unitPullback f ≫ fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (f.appTop p) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hu : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (unitPullback f) = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    Equiv.apply_symm_apply _ _
  rw [hu]
  apply Scheme.Modules.hom_ext
  intro U
  ext (s : Γ(Y, U))
  change f.app U (s * Y.presheaf.map (homOfLE le_top).op p) =
    f.app U s * X.presheaf.map (homOfLE le_top).op (f.appTop p)
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) p

lemma homEquiv_conjugate {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (α : F₂ ⟶ F₁)
    {A : C} {B : D} (v : F₁.obj A ⟶ B) :
    a₂.homEquiv _ _ (α.app A ≫ v) =
      a₁.homEquiv _ _ v ≫ (conjugateEquiv a₁ a₂ α).app B := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv]
  rw [Category.assoc, ← (conjugateEquiv a₁ a₂ α).naturality,
    ← Category.assoc, ← Adjunction.homEquiv_unit]

lemma unitPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (unitPullback g) ≫ unitPullback f =
        unitPullback (f ≫ g) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_conjugate, Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv]
  change ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        ((Scheme.Modules.pullback f).map (unitPullback g) ≫ unitPullback f)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  have hu {S T : Scheme.{u}} (h : S ⟶ T) :
      ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _) (unitPullback h) =
        SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    Equiv.apply_symm_apply _ _
  rw [hu, hu, hu]
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

lemma restrict_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      unitPullback f = (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [show (Scheme.Modules.restrictAdjunction f).unit.app _ ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app _) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _ from
        Adjunction.unit_leftAdjointUniq_hom_app _ _ _]
  rw [← Adjunction.homEquiv_unit]
  have hu : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (unitPullback f) = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    Equiv.apply_symm_apply _ _
  rw [hu, Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro U
  ext (s : Γ(Y, U))
  change f.app U s = (f.appIso (f ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op s)
  have hh := congrArg (fun q => q ≫ (f.appIso (f ⁻¹ᵁ U)).hom) (f.app_appIso_inv U)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  exact ConcreteCategory.congr_hom hh s

lemma principal_map_isIso {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (M : X.Modules)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (p : Γ(X, ⊤)) (hp : IsRegular p)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span ({p} : Set _))
    (φ : Scheme.Modules.Hom (SheafOfModules.unit X.ringCatSheaf : X.Modules) M)
    (ht : j.app ⊤ (φ.app ⊤ (1 : Γ(X, ⊤))) = p) :
    IsIso (C := X.Modules) φ := by
  have he : φ = fromSection M (φ.app ⊤ (1 : Γ(X, ⊤))) := by
    apply unit_hom_ext
    simp [fromSection_apply]
  rw [he]
  exact principal_frame I M j hj p hp hI _ ht

/-- The local comparison is an isomorphism whenever its defining equation
remains regular after the given ring map. No flatness is used. -/
lemma affine_comparison_isIso {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) (J : X.IdealSheafData)
    (M : Y.Modules) (L : X.Modules)
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (l : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (hl : IdealRealization J L l)
    (p : Γ(Y, ⊤)) (hp : IsRegular p) (hfp : IsRegular (f.appTop p))
    (hI : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span ({p} : Set _))
    (hJ : J.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span ({f.appTop p} : Set _))
    (q : (Scheme.Modules.pullback f).obj M ⟶ L)
    (hq : q ≫ l = (Scheme.Modules.pullback f).map j ≫ unitPullback f) : IsIso q := by
  letI := unitPullback_isIso f
  obtain ⟨t, ht⟩ : ∃ t, j.app ⊤ t = p := by
    have hpI : p ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩).carrier := by
      rw [hI]
      exact Ideal.subset_span (Set.mem_singleton p)
    rw [← hj.2 ⟨⊤, isAffineOpen_top Y⟩] at hpI
    exact hpI
  let φ := fromSection M t
  letI : IsIso (C := Y.Modules) φ := principal_frame I M j hj p hp hI t ht
  have hφ : φ ≫ j = fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) p := by
    apply unit_hom_ext
    simpa [φ, fromSection_apply] using ht
  let α := inv (unitPullback f) ≫ (Scheme.Modules.pullback f).map φ
  let β := α ≫ q
  have hβ : β ≫ l = fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (f.appTop p) := by
    simp only [β, α, Category.assoc, hq]
    rw [← Category.assoc ((Scheme.Modules.pullback f).map φ), ← CategoryTheory.Functor.map_comp,
      hφ, pullback_multiplication, IsIso.inv_hom_id_assoc]
  have hβiso : IsIso (C := X.Modules) β := by
    apply principal_map_isIso J L l hl (f.appTop p) hfp hJ β
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun v => Scheme.Modules.Hom.app v ⊤) hβ) (1 : Γ(X, ⊤))
    simpa [fromSection_apply] using hh
  letI := hβiso
  exact IsIso.of_isIso_comp_left α q

lemma realization_transport {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (e : M ≅ N)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (l : N ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I M j) (he : e.hom ≫ l = j) : IdealRealization I N l := by
  letI : Mono j := hj.1
  have hl : l = e.inv ≫ j := by rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨?_, ?_⟩
  · rw [hl]
    infer_instance
  · intro U
    rw [← hj.2 U]
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.inv.app U.1 t, ?_⟩
      exact (ConcreteCategory.congr_hom
        (congrArg (fun q => Scheme.Modules.Hom.app q U.1) hl) t).symm
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.app U.1 t, ?_⟩
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => Scheme.Modules.Hom.app q U.1) he) t

def pulledInclusion {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).map j ≫ unitPullback f

lemma pullback_open_realization {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (M : Y.Modules)
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (hj : IdealRealization I M j) :
    IdealRealization (I.comap f) ((Scheme.Modules.pullback f).obj M) (pulledInclusion f j) := by
  apply realization_transport _ ((Scheme.Modules.restrictFunctorIsoPullback f).app M) _ _
    (restrict_realization f I M j hj)
  unfold pulledInclusion
  simp only [Iso.app_hom]
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality,
    Category.assoc, restrict_unit]

lemma unitPullback_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      unitPullback (f ≫ g) =
        (Scheme.Modules.pullback f).map (unitPullback g) ≫ unitPullback f := by
  rw [← unitPullback_comp f g, Iso.hom_inv_id_app_assoc]

lemma pulledInclusion_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (j : M ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)) :
    (Scheme.Modules.pullbackComp f g).hom.app M ≫ pulledInclusion (f ≫ g) j =
      pulledInclusion f (pulledInclusion g j) := by
  unfold pulledInclusion
  rw [← Category.assoc, ← (Scheme.Modules.pullbackComp f g).hom.naturality,
    Category.assoc, unitPullback_comp_hom]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map, Category.assoc]

lemma pulledInclusion_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (j : M ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)) :
    (Scheme.Modules.pullbackComp f g).inv.app M ≫ pulledInclusion f (pulledInclusion g j) =
      pulledInclusion (f ≫ g) j := by
  rw [← pulledInclusion_comp, Iso.inv_hom_id_app_assoc]

lemma pulledInclusion_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    (Scheme.Modules.pullbackCongr h).hom.app M ≫ pulledInclusion g j = pulledInclusion f j := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Transport of pullbacks through an actual commuting square of scheme maps. -/
def squareIso {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) (h : a ≫ f = g ≫ b) (M : Y.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackComp g b).app M ≪≫
    (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp a f).app M).symm

lemma squareIso_inclusion {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) (h : a ≫ f = g ≫ b) (M : Y.Modules)
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    (squareIso f a b g h M).hom ≫ pulledInclusion a (pulledInclusion f j) =
      pulledInclusion g (pulledInclusion b j) := by
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [pulledInclusion_comp_inv, pulledInclusion_congr, pulledInclusion_comp]

lemma square_comparison {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) (h : a ≫ f = g ≫ b) (M : Y.Modules) (L : X.Modules)
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (l : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (q : (Scheme.Modules.pullback f).obj M ⟶ L) (hq : q ≫ l = pulledInclusion f j) :
    ((squareIso f a b g h M).hom ≫ (Scheme.Modules.pullback a).map q) ≫
      pulledInclusion a l = pulledInclusion g (pulledInclusion b j) := by
  rw [pulledInclusion, Category.assoc, ← Category.assoc ((Scheme.Modules.pullback a).map q),
    ← CategoryTheory.Functor.map_comp, hq]
  exact squareIso_inclusion f a b g h M j

lemma isIso_of_pullback_cover {X : Scheme.{u}} {ι : Type*} (U : ι → Scheme.{u})
    (c : ∀ i, U i ⟶ X) (ho : ∀ i, IsOpenImmersion (c i))
    (hc : ∀ x : X, ∃ i z, c i z = x) {M N : X.Modules} (q : M ⟶ N)
    (hq : ∀ i, IsIso ((Scheme.Modules.pullback (c i)).map q)) : IsIso q := by
  letI : ∀ i, IsOpenImmersion (c i) := ho
  let B : (Σ i, (U i).Opens) → X.Opens := fun v => c v.1 ''ᵁ v.2
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨i, z, rfl⟩ := hc x
    refine ⟨B ⟨i, c i ⁻¹ᵁ V⟩, ⟨⟨i, c i ⁻¹ᵁ V⟩, rfl⟩,
      ⟨z, hx, rfl⟩, (c i).image_preimage_le V⟩
  have hrestrict (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (c i)).map q) := by
    letI := hq i
    have he : (Scheme.Modules.restrictFunctor (c i)).map q =
        (Scheme.Modules.restrictFunctorIsoPullback (c i)).hom.app M ≫
          (Scheme.Modules.pullback (c i)).map q ≫
            (Scheme.Modules.restrictFunctorIsoPullback (c i)).inv.app N := by
      rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback (c i)).hom.naturality]
      simp
    rw [he]
    infer_instance
  let H := (SheafOfModules.toSheaf X.ringCatSheaf).map q
  have hH : IsIso H := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro v
    letI := hrestrict v.1
    exact inferInstanceAs (IsIso (((Scheme.Modules.restrictFunctor (c v.1)).map q).app v.2))
  letI := hH
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  exact inferInstanceAs (IsIso (H.hom.app (Opposite.op V)))

open ArithmeticThetaInfinitesimalPolygonR0129

local instance chart_isOpen (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (D.chart i) := D.chart_open i

local instance specA_isAffine (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))

def chartEquation (k : Type u) [Field k] [CharZero k] (n : ℕ) (a b : kˣ) :
    Γ(specA k n, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (pairEquation k n a b)

lemma chartEquation_regular (k : Type u) [Field k] [CharZero k] (n : ℕ) (a b : kˣ) :
    IsRegular (chartEquation k n a b) :=
  regular_equiv (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm
    (local_marked_pair k n a b).1

lemma chartEquation_ideal (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    ((markedIdeal k r n hr D a).comap (D.chart i)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span ({chartEquation k n (a i) (a (next r hr i))} : Set _) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv
  have he : Ideal.map e.toRingHom
      (((markedIdeal k r n hr D a).comap (D.chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.span ({pairEquation k n (a i) (a (next r hr i))} : Set _) :=
    global_marked_ideal_charts k r n hr h3 E hE D a i
  apply_fun Ideal.map e.symm.toRingHom at he
  change _ = Ideal.span ({e.symm (pairEquation k n (a i) (a (next r hr i)))} : Set _)
  simpa [Ideal.map_map, Ideal.map_span, Set.image_singleton] using he

lemma chartEquation_reduction (k : Type u) [Field k] [CharZero k]
    (n N : ℕ) (h : n ≤ N) (a b : kˣ) :
    (chartReduction k n N h).appTop (chartEquation k N a b) = chartEquation k n a b := by
  have hh := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h)))
      (pairEquation k N a b)
  change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
    (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      (pairEquation k N a b)) =
    (chartReduction k n N h).appTop (chartEquation k N a b) at hh
  rw [MarkedIdealTowerBaseChangeR0133.pairEquation_reduction] at hh
  exact hh.symm

lemma tower_comparison_isIso (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr) (a : Fin r → kˣ)
    (n N : ℕ) (h : n ≤ N)
    (M : (T.atlas N).X.Modules) (L : (T.atlas n).X.Modules)
    (j : M ⟶ (SheafOfModules.unit (T.atlas N).X.ringCatSheaf : (T.atlas N).X.Modules))
    (l : L ⟶ (SheafOfModules.unit (T.atlas n).X.ringCatSheaf : (T.atlas n).X.Modules))
    (hj : IdealRealization (markedIdeal k r N hr (T.atlas N) a) M j)
    (hl : IdealRealization (markedIdeal k r n hr (T.atlas n) a) L l)
    (q : (Scheme.Modules.pullback (T.transition n N h)).obj M ⟶ L)
    (hq : q ≫ l = pulledInclusion (T.transition n N h) j) : IsIso q := by
  apply isIso_of_pullback_cover (fun _ : Fin r => specA k n)
    (T.atlas n).chart (T.atlas n).chart_open (T.atlas n).covers q
  intro i
  let f := T.transition n N h
  let cn := (T.atlas n).chart i
  let cN := (T.atlas N).chart i
  let g := chartReduction k n N h
  let e := squareIso f cn cN g ((T.transition_spec n N h).2 i) M
  have hq' : IsIso (e.hom ≫ (Scheme.Modules.pullback cn).map q) := by
    apply affine_comparison_isIso g
      ((markedIdeal k r N hr (T.atlas N) a).comap cN)
      ((markedIdeal k r n hr (T.atlas n) a).comap cn)
      ((Scheme.Modules.pullback cN).obj M) ((Scheme.Modules.pullback cn).obj L)
      (pulledInclusion cN j) (pulledInclusion cn l)
      (pullback_open_realization cN _ M j hj)
      (pullback_open_realization cn _ L l hl)
      (chartEquation k N (a i) (a (next r hr i)))
      (chartEquation_regular k N _ _)
    · rw [chartEquation_reduction]
      exact chartEquation_regular k n _ _
    · exact chartEquation_ideal k r N hr h3 (T.overlap_spec N) (T.atlas N) a i
    · rw [chartEquation_reduction]
      exact chartEquation_ideal k r n hr h3 (T.overlap_spec n) (T.atlas n) a i
    · exact square_comparison f cn cN g ((T.transition_spec n N h).2 i) M L j l q hq
  letI := hq'
  exact IsIso.of_isIso_comp_left e.hom ((Scheme.Modules.pullback cn).map q)

end CanonicalCartierLineReductionR0133
open CategoryTheory AlgebraicGeometry

/-- Every infinitesimal reduction has a unique comparison of the actual ideal
lines, characterized by the inclusions and the canonical pullback of the unit. -/
theorem canonical_cartier_line_reduction :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ),
    ∀ (n N : ℕ) (h : n ≤ N), LineReductionFacts k r hr T a n N h := by
  intro k _ _ r hr h3 T a n N h M L j l hj hl
  let I := markedIdeal k r N hr (T.atlas N) a
  let J := markedIdeal k r n hr (T.atlas n) a
  have hIJ : I.comap (T.transition n N h) ≤ J :=
    le_of_eq (marked_ideal_tower_base_change k r hr h3 T a n N h)
  let q := CanonicalCartierLineReductionR0133.comparison (T.transition n N h)
    I J hIJ M L j l hj hl
  have hq : q ≫ l = (Scheme.Modules.pullback (T.transition n N h)).map j ≫
      unitPullback (T.transition n N h) :=
    CanonicalCartierLineReductionR0133.comparison_inclusion (T.transition n N h)
      I J hIJ M L j l hj hl
  letI := CanonicalCartierLineReductionR0133.tower_comparison_isIso
    k r hr h3 T a n N h M L j l hj hl q hq
  letI : Mono l := hl.1
  refine ⟨asIso q, hq, ?_⟩
  intro e he
  apply Iso.ext
  exact (cancel_mono l).mp (he.trans hq.symm)

end ArithmeticThetaPolygonCartierR0133
