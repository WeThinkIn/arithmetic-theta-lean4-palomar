module

public import GlobalMarkedIdealChartsR0133
public import Mathlib.Algebra.Category.ModuleCat.Kernels

@[expose] public section

/-! Realization of the marked Cartier ideal as a sheaf of modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace GlobalCartierIdealLineR0133
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

/-- The structure map to the structure sheaf of the closed subscheme. -/
def quotientMap {X : Scheme.{u}} (I : X.IdealSheafData) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- The ideal module is the categorical kernel of the actual quotient map. -/
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (quotientMap I)

def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModule I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  kernel.ι (quotientMap I)

lemma ideal_realization {X : Scheme.{u}} (I : X.IdealSheafData) :
    IdealRealization I (idealModule I) (idealInclusion I) := by
  refine ⟨inferInstanceAs (Mono (kernel.ι (quotientMap I))), ?_⟩
  intro U
  let F := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U.1)
  letI : F.Additive := inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op U.1)).Additive)
  let e := PreservesKernel.iso F (quotientMap I) ≪≫
    ModuleCat.kernelIsoKer (F.map (quotientMap I))
  have he : e.inv ≫ F.map (idealInclusion I) =
      ModuleCat.ofHom (F.map (quotientMap I)).hom.ker.subtype := by
    simp [e, idealInclusion, PreservesKernel.iso_inv_ι]
  ext s
  rw [← I.ker_subschemeι_app U]
  change (∃ t, (F.map (idealInclusion I)) t = s) ↔ I.subschemeι.app U.1 s = 0
  constructor
  · rintro ⟨t, rfl⟩
    have h := F.congr_map (kernel.condition (quotientMap I))
    rw [F.map_comp, F.map_zero] at h
    exact ConcreteCategory.congr_hom h t
  · intro hs
    let t : (F.map (quotientMap I)).hom.ker := ⟨s, hs⟩
    refine ⟨e.inv t, ?_⟩
    exact ConcreteCategory.congr_hom he t

/-- A section over the terminal open defines a morphism from the unit. -/
def fromSection {X : Scheme.{u}} (M : X.Modules) (t : Γ(M, ⊤)) :
    Scheme.Modules.Hom (SheafOfModules.unit X.ringCatSheaf : X.Modules) M :=
  M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op t)
    (by
      intro U V f
      change M.presheaf.map f (M.presheaf.map (homOfLE le_top).op t) =
        M.presheaf.map (homOfLE le_top).op t
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl))

lemma fromSection_apply {X : Scheme.{u}} (M : X.Modules) (t : Γ(M, ⊤))
    (U : X.Opens) (s : Γ(X, U)) :
    (fromSection M t).app U s = s • M.presheaf.map (homOfLE le_top).op t := rfl

lemma mono_app_injective {X : Scheme.{u}} {M N : X.Modules} (j : M ⟶ N)
    [Mono j] (U : X.Opens) : Function.Injective (j.app U) := by
  exact (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).map j)).mp inferInstance

lemma fromSection_image {X : Scheme.{u}} (M : X.Modules)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (t : Γ(M, ⊤)) (U : X.Opens) (s : Γ(X, U)) :
    j.app U ((fromSection M t).app U s) =
      s * X.presheaf.map (homOfLE le_top).op (j.app ⊤ t) := by
  rw [fromSection_apply, Scheme.Modules.Hom.app_smul]
  have hn : j.app U (M.presheaf.map (homOfLE le_top).op t) =
      X.presheaf.map (homOfLE le_top).op (j.app ⊤ t) :=
    ConcreteCategory.congr_hom (j.mapPresheaf.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) t
  rw [hn]
  rfl

/-- Restriction of the realized ideal along an open immersion. -/
lemma restrict_realization {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (M : Y.Modules)
    (j : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (h : IdealRealization I M j) :
    IdealRealization (I.comap f) (M.restrict f)
      ((Scheme.Modules.restrictFunctor f).map j ≫ (Scheme.Modules.restrictUnitIso f).hom) := by
  letI : Mono j := h.1
  let l : M.restrict f ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    (Scheme.Modules.restrictFunctor f).map j ≫ (Scheme.Modules.restrictUnitIso f).hom
  have hl (U : X.Opens) (s : Γ(M.restrict f, U)) :
      l.app U s = (f.appIso U).hom (j.app (f ''ᵁ U) s) := rfl
  refine ⟨?_, ?_⟩
  · change Mono l
    constructor
    intro Z g₁ g₂ he
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    apply mono_app_injective j (f ''ᵁ U)
    apply (ConcreteCategory.bijective_of_isIso (f.appIso U).hom).1
    exact ConcreteCategory.congr_hom
      (congrArg (fun q => Scheme.Modules.Hom.app q U) he) s
  · intro U
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    ext s
    change (∃ t, l.app U.1 t = s) ↔
      (f.appIso U.1).inv s ∈ (I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩).carrier
    rw [← h.2 ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [hl]
      exact (ConcreteCategory.congr_hom (f.appIso U.1).hom_inv_id (j.app _ t)).symm
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hl]
      exact (congrArg (fun q : Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).hom q) ht).trans
        (ConcreteCategory.congr_hom (f.appIso U.1).inv_hom_id s)

/-- A principal regular ideal on an affine scheme realizes a free rank-one module. -/
lemma principal_realization_free {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (M : X.Modules)
    (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (h : IdealRealization I M j) (f : Γ(X, ⊤)) (hf : IsRegular f)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span ({f} : Set _)) :
    Nonempty (M ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  letI : Mono j := h.1
  obtain ⟨t, ht⟩ : ∃ t, j.app ⊤ t = f := by
    have hfI : f ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩ := by
      rw [hI]; exact Ideal.subset_span (Set.mem_singleton f)
    exact (show f ∈ Set.range (fun t => j.app ⊤ t) by rw [h.2 ⟨⊤, isAffineOpen_top X⟩]; exact hfI)
  let φ := fromSection M t
  have hφ (U : X.Opens) (s : Γ(X, U)) :
      j.app U (φ.app U s) = s * X.presheaf.map (homOfLE le_top).op f := by
    rw [fromSection_image, ht]
  have hbasic (g : Γ(X, ⊤)) : IsIso (φ.app (X.basicOpen g)) := by
    let U := X.basicOpen g
    let ρ := (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
    letI := (isAffineOpen_top X).isLocalization_basicOpen g
    have hreg : IsRegular (ρ f) :=
      isRegular_iff_mem_nonZeroDivisors.mpr
        (IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers g) Γ(X, U)
          hf.mem_nonZeroDivisors)
    have hIU : I.ideal (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) g) = Ideal.span ({ρ f} : Set _) := by
      rw [← I.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ g, hI,
        Ideal.map_span, Set.image_singleton]
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro s₁ s₂ he
      apply hreg.right
      exact (hφ U s₁).symm.trans ((congrArg (j.app U) he).trans (hφ U s₂))
    · intro z
      have hz : j.app U z ∈ (I.ideal (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) g)).carrier := by
        rw [← h.2 (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) g)]
        exact ⟨z, rfl⟩
      rw [hIU] at hz
      have hz' : (j.app U z : Γ(X, U)) ∈ Ideal.span ({ρ f} : Set _) := hz
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (α := Γ(X, U))).mp hz'
      refine ⟨c, mono_app_injective j U ?_⟩
      exact (hφ U c).trans hc
  let H := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hH : IsIso H := TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen X) hbasic
  letI := hH
  have hφiso : IsIso (C := X.Modules) φ := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    exact inferInstanceAs (IsIso (H.hom.app (Opposite.op U)))
  exact ⟨(asIso (C := X.Modules) φ).symm⟩

lemma regular_equiv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) {f : S} (hf : IsRegular f) : IsRegular (e f) := by
  constructor
  · intro x y h
    apply e.symm.injective
    apply hf.left
    simpa using congrArg e.symm h
  · intro x y h
    apply e.symm.injective
    apply hf.right
    simpa using congrArg e.symm h

local instance chart_open_instance (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (D.chart i) := D.chart_open i

local instance specA_affine (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))

lemma chart_principal (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    ∃ f : D.X.presheaf.obj (Opposite.op ((D.chart i) ''ᵁ ⊤)),
      IsRegular f ∧ (markedIdeal k r n hr D a).ideal
        ⟨(D.chart i) ''ᵁ ⊤, (isAffineOpen_top (specA k n)).image_of_isOpenImmersion
          (D.chart i)⟩ = Ideal.span ({f} : Set _) := by
  letI : IsOpenImmersion (D.chart i) := D.chart_open i
  letI : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  let p := pairEquation k n (a i) (a (next r hr i))
  let e := ((D.chart i).appIso ⊤).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv
  refine ⟨e.symm p, regular_equiv e.symm (local_marked_pair k n _ _).1, ?_⟩
  have h := global_marked_ideal_charts k r n hr h3 E hE D a i
  unfold chartIdeal at h
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  have he : Ideal.map e.toRingHom ((markedIdeal k r n hr D a).ideal
      ⟨(D.chart i) ''ᵁ ⊤, (isAffineOpen_top (specA k n)).image_of_isOpenImmersion
        (D.chart i)⟩) = Ideal.span ({p} : Set _) := by
    rw [show e.toRingHom = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom.comp
      ((D.chart i).appIso ⊤).hom.hom from rfl, ← Ideal.map_map]
    convert h using 1
    exact congrArg (Ideal.map _) (Ideal.map_comap_of_equiv ((D.chart i).appIso ⊤).commRingCatIsoToRingEquiv)
  apply_fun Ideal.map e.symm.toRingHom at he
  simpa [Ideal.map_map, Ideal.map_span, Set.image_singleton] using he

lemma effective_cartier (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) :
    IsEffectiveCartierIdeal (markedIdeal k r n hr D a) := by
  intro x
  obtain ⟨i, z, rfl⟩ := D.covers x
  letI : IsOpenImmersion (D.chart i) := D.chart_open i
  letI : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  refine ⟨⟨(D.chart i) ''ᵁ ⊤,
    (isAffineOpen_top (specA k n)).image_of_isOpenImmersion (D.chart i)⟩,
    ⟨z, trivial, rfl⟩, ?_⟩
  exact chart_principal k r n hr h3 E hE D a i

end GlobalCartierIdealLineR0133

open CategoryTheory AlgebraicGeometry

/-- The global marked divisor has its actual invertible ideal module O(-D). -/
theorem global_cartier_ideal_line :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E) (a : Fin r → kˣ),
      CartierLineFacts k r n hr D a := by
  intro k _ _ r n hr h3 E hE D a
  open GlobalCartierIdealLineR0133 in
    refine ⟨effective_cartier k r n hr h3 E hE D a,
      idealModule (markedIdeal k r n hr D a), idealInclusion (markedIdeal k r n hr D a),
      ideal_realization _, ?_⟩
  intro i
  letI : AlgebraicGeometry.IsOpenImmersion (D.chart i) := D.chart_open i
  letI : AlgebraicGeometry.IsAffine (ArithmeticThetaInfinitesimalPolygonR0129.specA k n) :=
    inferInstanceAs (AlgebraicGeometry.IsAffine
      (AlgebraicGeometry.Spec (CommRingCat.of (ArithmeticThetaInfinitesimalPolygonR0129.A k n))))
  let I := markedIdeal k r n hr D a
  let M := GlobalCartierIdealLineR0133.idealModule I
  let j := GlobalCartierIdealLineR0133.idealInclusion I
  have h := GlobalCartierIdealLineR0133.restrict_realization (D.chart i) I M j
    (GlobalCartierIdealLineR0133.ideal_realization I)
  obtain ⟨f, hf, hI⟩ := GlobalCartierIdealLineR0133.chart_principal k r n hr h3 E hE D a i
  let e := ((D.chart i).appIso ⊤).commRingCatIsoToRingEquiv
  have he : (I.comap (D.chart i)).ideal
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ = Ideal.span ({e f} : Set _) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, hI]
    change Ideal.comap e.symm.toRingHom (Ideal.span ({f} : Set _)) = _
    calc
      _ = Ideal.map e.toRingHom (Ideal.span ({f} : Set _)) :=
        (Ideal.map_comap_of_equiv e).symm
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]; rfl
  obtain ⟨eM⟩ := GlobalCartierIdealLineR0133.principal_realization_free _ _ _ h (e f)
    (GlobalCartierIdealLineR0133.regular_equiv e hf) he
  exact ⟨((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (D.chart i)).app M).symm
    ≪≫ eM⟩

end ArithmeticThetaPolygonCartierR0133
