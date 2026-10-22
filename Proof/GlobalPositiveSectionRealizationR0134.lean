module
public import Mathlib

public import PositiveLineSectionsDefinitionsR0134
public import GlobalPositiveSectionDescentR0134

@[expose] public section

/-! Local frames and descent for the dual of the actual marked ideal power. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace GlobalPositiveSectionRealizationR0134
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

local instance chart_isOpen (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (D.chart i) := D.chart_open i

local instance specA_isAffine (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))

/-- Restriction to an open immersion preserves every ideal power, including zero. -/
lemma comap_pow_open {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (d : ℕ) : (I ^ d).comap f = (I.comap f) ^ d := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  let e := (f.appIso U.1).commRingCatIsoToRingEquiv
  change Ideal.comap e.symm.toRingHom (_ ^ d) = (Ideal.comap e.symm.toRingHom _) ^ d
  exact (Ideal.map_comap_of_equiv e).symm.trans
    ((Ideal.map_pow _ _ _).trans (congrArg (fun J => J^d) (Ideal.map_comap_of_equiv e)))

local instance unitSectionsCommRing (X : Scheme.{u}) (U : X.Opens) :
    CommRing Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) :=
  inferInstanceAs (CommRing (X.presheaf.obj (Opposite.op U)))

lemma affine_pullback_inv {S T : CommRingCat.{u}} (f : S ⟶ T) (x : S) :
    (Scheme.ΓSpecIso T).hom ((Spec.map f).appTop ((Scheme.ΓSpecIso S).inv x)) = f x := by
  rw [ArithmeticThetaPolygonCohomologyR0131.PolygonGlobalFunctionsR0131.affine_pullback]
  exact congrArg f ((Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.apply_symm_apply x)

/-- Endomorphisms of the structure module commute. -/
lemma unit_end_comm {X : Scheme.{u}}
    (f g : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) : f ≫ g = g ≫ f := by
  apply unit_hom_ext
  change (Scheme.Modules.Hom.app g) ⊤ ((Scheme.Modules.Hom.app f) ⊤ (1 : Γ(X, ⊤))) =
    (Scheme.Modules.Hom.app f) ⊤ ((Scheme.Modules.Hom.app g) ⊤ (1 : Γ(X, ⊤)))
  rw [unit_hom_apply g ⊤ ((Scheme.Modules.Hom.app f) ⊤ (1 : Γ(X, ⊤)))]
  conv_rhs => rw [unit_hom_apply f]
  simpa using mul_comm ((Scheme.Modules.Hom.app f) ⊤ (1 : Γ(X, ⊤))) ((Scheme.Modules.Hom.app g) ⊤ (1 : Γ(X, ⊤)))

/-- Cross evaluation in a free rank-one module, without fraction fields. -/
lemma frame_cross {X : Scheme.{u}} {M : X.Modules}
    (α β : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) [IsIso α]
    (j q : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    (α ≫ q) ≫ (β ≫ j) = (β ≫ q) ≫ (α ≫ j) := by
  calc
    (α ≫ q) ≫ (β ≫ j) = (α ≫ q) ≫ ((β ≫ inv α) ≫ (α ≫ j)) := by simp
    _ = (β ≫ inv α) ≫ ((α ≫ q) ≫ (α ≫ j)) := by
      rw [← Category.assoc, unit_end_comm (α ≫ q) (β ≫ inv α), Category.assoc]
    _ = (β ≫ q) ≫ (α ≫ j) := by simp

lemma multiplication_eq {X : Scheme.{u}} (s p t q : Γ(X, ⊤))
    (h : CategoryStruct.comp (obj := X.Modules)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) s)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) p) =
      CategoryStruct.comp (obj := X.Modules)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) t)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) q)) :
    s * p = t * q := by
  have hv := ConcreteCategory.congr_hom
    (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) h) (1 : Γ(X, ⊤))
  change (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) p).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) s).app ⊤ (1 : Γ(X, ⊤))) =
    (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) q).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) t).app ⊤ (1 : Γ(X, ⊤))) at hv
  simpa [fromSection_apply] using hv

/-- Cross multiplication detects equality because the denominator is a genuine ideal inclusion. -/
lemma frame_cross_cancel {X : Scheme.{u}} {M : X.Modules}
    (α β : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M)
    [IsIso α] [IsIso β]
    (j q v : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Mono j]
    (h : (α ≫ q) ≫ (β ≫ j) = (β ≫ v) ≫ (α ≫ j)) : q = v := by
  apply (cancel_epi α).mp
  apply (cancel_mono (β ≫ j)).mp
  exact h.trans (frame_cross α β j v).symm

/-- Equality of multiplication maps is the literal product equality in global sections. -/
lemma multiplication_eq_iff {X : Scheme.{u}} (s p t q : Γ(X, ⊤)) :
    CategoryStruct.comp (obj := X.Modules)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) s)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) p) =
      CategoryStruct.comp (obj := X.Modules)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) t)
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) q) ↔ s * p = t * q := by
  refine ⟨multiplication_eq s p t q, ?_⟩
  intro h
  apply unit_hom_ext
  change (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) p).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) s).app ⊤ (1 : Γ(X, ⊤))) =
    (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) q).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) t).app ⊤ (1 : Γ(X, ⊤)))
  simpa [fromSection_apply] using h

/-- Pull back a frame using the canonical pullback of the structure module. -/
def pullFrame {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ (Scheme.Modules.pullback f).obj M :=
  (letI := unitPullback_isIso f; inv (unitPullback f)) ≫
    (Scheme.Modules.pullback f).map α

lemma pullFrame_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) [IsIso α] :
    IsIso (pullFrame f α) := by
  unfold pullFrame
  infer_instance

lemma pullFrame_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M)
    (q : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (s : Γ(Y, ⊤))
    (h : α ≫ q = fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) s) :
    pullFrame f α ≫ pulledInclusion f q =
      fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) (f.appTop s) := by
  letI := unitPullback_isIso f
  change (inv (unitPullback f) ≫ (Scheme.Modules.pullback f).map α) ≫
    ((Scheme.Modules.pullback f).map q ≫ unitPullback f) = _
  rw [Category.assoc, ← Category.assoc ((Scheme.Modules.pullback f).map α),
    ← CategoryTheory.Functor.map_comp, h, pullback_multiplication, IsIso.inv_hom_id_assoc]

/-- Frame evaluations and cross multiplication glue two maps across a genuine module isomorphism. -/
lemma frame_maps_glue {X Y Z : Scheme.{u}} (L : Z ⟶ X) (R : Z ⟶ Y)
    {M : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback R).obj N ≅ (Scheme.Modules.pullback L).obj M)
    (α : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M)
    (β : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ N)
    [IsIso α] [IsIso β]
    (j q : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (j' v : N ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    [Mono (pulledInclusion L j)]
    (he : e.hom ≫ pulledInclusion L j = pulledInclusion R j')
    (p s : Γ(X, ⊤)) (p' s' : Γ(Y, ⊤))
    (hαj : α ≫ j = fromSection (SheafOfModules.unit X.ringCatSheaf) p)
    (hβj : β ≫ j' = fromSection (SheafOfModules.unit Y.ringCatSheaf) p')
    (hαq : α ≫ q = fromSection (SheafOfModules.unit X.ringCatSheaf) s)
    (hβv : β ≫ v = fromSection (SheafOfModules.unit Y.ringCatSheaf) s')
    (hcross : L.appTop s * R.appTop p' = R.appTop s' * L.appTop p) :
    e.hom ≫ pulledInclusion L q = pulledInclusion R v := by
  let α' := pullFrame L α
  let β' := pullFrame R β ≫ e.hom
  let J := pulledInclusion L j
  let Q := pulledInclusion L q
  let V := e.inv ≫ pulledInclusion R v
  letI : IsIso α' := pullFrame_isIso L α
  letI : IsIso (pullFrame R β) := pullFrame_isIso R β
  letI : IsIso β' := inferInstanceAs (IsIso (pullFrame R β ≫ e.hom))
  have hαJ : α' ≫ J = fromSection (SheafOfModules.unit Z.ringCatSheaf)
      (L.appTop p) := pullFrame_evaluation L α j p hαj
  have hβJ : β' ≫ J = fromSection (SheafOfModules.unit Z.ringCatSheaf)
      (R.appTop p') := by
    change (pullFrame R β ≫ e.hom) ≫ pulledInclusion L j = _
    rw [Category.assoc, he]
    exact pullFrame_evaluation R β j' p' hβj
  have hαQ : α' ≫ Q = fromSection (SheafOfModules.unit Z.ringCatSheaf)
      (L.appTop s) := pullFrame_evaluation L α q s hαq
  have hβV : β' ≫ V = fromSection (SheafOfModules.unit Z.ringCatSheaf)
      (R.appTop s') := by
    change (pullFrame R β ≫ e.hom) ≫ (e.inv ≫ _) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact pullFrame_evaluation R β v s' hβv
  have hQV : Q = V := by
    apply frame_cross_cancel α' β' J Q V
    rw [hαQ, hβJ, hβV, hαJ]
    exact (multiplication_eq_iff _ _ _ _).mpr hcross
  change e.hom ≫ Q = _
  rw [hQV]
  exact Iso.hom_inv_id_assoc e _

variable (k : Type u) [Field k] [CharZero k]
variable (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
variable {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
variable (D : Atlas k r n hr E) (a : Fin r → kˣ) (d : ℕ)

/-- The equation is transported through the actual affine global-section isomorphism. -/
def localEquation (i : Fin r) : Γ(specA k n, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k r n hr a i)^d)

lemma localEquation_regular (i : Fin r) : IsRegular (localEquation k r n hr a d i) := by
  apply regular_equiv (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm
  exact ((local_marked_pair k n (a i) (a (next r hr i))).1).pow d

include h3 hE

lemma power_chart_ideal (i : Fin r) :
    (((markedIdeal k r n hr D a)^d).comap (D.chart i)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span ({localEquation k r n hr a d i} : Set _) := by
  rw [comap_pow_open]
  change (((markedIdeal k r n hr D a).comap (D.chart i)).ideal
    ⟨⊤, isAffineOpen_top _⟩)^d = _
  rw [chartEquation_ideal k r n hr h3 hE D a i, Ideal.span_singleton_pow]
  congr 2
  exact (map_pow (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom _ d).symm

/-- The canonical categorical kernel has the required generator on each chart. -/
lemma local_generator (i : Fin r) :
    ∃ t : Γ((Scheme.Modules.pullback (D.chart i)).obj (powerIdealModule k D a d), ⊤),
      (pulledInclusion (D.chart i) (idealInclusion ((markedIdeal k r n hr D a)^d))).app ⊤ t =
        localEquation k r n hr a d i := by
  have h := pullback_open_realization (D.chart i) ((markedIdeal k r n hr D a)^d)
    (powerIdealModule k D a d) (idealInclusion _) (ideal_realization _)
  have hp : localEquation k r n hr a d i ∈
      ((((markedIdeal k r n hr D a)^d).comap (D.chart i)).ideal
        ⟨⊤, isAffineOpen_top _⟩).carrier := by
    rw [power_chart_ideal k r n hr h3 hE D a d i]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [← h.2 ⟨⊤, isAffineOpen_top _⟩] at hp
  exact hp

def localGenerator (i : Fin r) :
    Γ((Scheme.Modules.pullback (D.chart i)).obj (powerIdealModule k D a d), ⊤) :=
  (local_generator k r n hr h3 hE D a d i).choose

lemma localGenerator_spec (i : Fin r) :
    (pulledInclusion (D.chart i) (idealInclusion ((markedIdeal k r n hr D a)^d))).app ⊤
      (localGenerator k r n hr h3 hE D a d i) = localEquation k r n hr a d i :=
  (local_generator k r n hr h3 hE D a d i).choose_spec

/-- The specified generator is a frame, not merely a section of the kernel. -/
lemma localGenerator_frame (i : Fin r) : IsIso (C := (specA k n).Modules)
    (fromSection _ (localGenerator k r n hr h3 hE D a d i)) := by
  apply principal_frame
    (((markedIdeal k r n hr D a)^d).comap (D.chart i)) _
    (pulledInclusion (D.chart i) (idealInclusion ((markedIdeal k r n hr D a)^d)))
    (pullback_open_realization (D.chart i) _ _ _ (ideal_realization _))
    (localEquation k r n hr a d i) (localEquation_regular k r n hr a d i)
    (power_chart_ideal k r n hr h3 hE D a d i)
  exact localGenerator_spec k r n hr h3 hE D a d i

omit h3 hE in
/-- Morphisms of module sheaves are determined on any actual open cover. -/
lemma hom_ext_pullback_cover {X : Scheme.{u}} {ι : Type*} (U : ι → Scheme.{u})
    (c : ∀ i, U i ⟶ X) (ho : ∀ i, IsOpenImmersion (c i))
    (hc : ∀ x : X, ∃ i z, c i z = x) {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (c i)).map f =
      (Scheme.Modules.pullback (c i)).map g) : f = g := by
  letI : ∀ i, IsOpenImmersion (c i) := ho
  let B : (Σ i, (U i).Opens) → X.Opens := fun v => c v.1 ''ᵁ v.2
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨i, z, rfl⟩ := hc x
    exact ⟨B ⟨i, c i ⁻¹ᵁ V⟩, ⟨⟨i, c i ⁻¹ᵁ V⟩, rfl⟩,
      ⟨z, hx, rfl⟩, (c i).image_preimage_le V⟩
  have hr (i : ι) : (Scheme.Modules.restrictFunctor (c i)).map f =
      (Scheme.Modules.restrictFunctor (c i)).map g := by
    apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback (c i)).hom.app N)).mp
    rw [(Scheme.Modules.restrictFunctorIsoPullback (c i)).hom.naturality,
      (Scheme.Modules.restrictFunctorIsoPullback (c i)).hom.naturality, h i]
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB
  intro v
  exact congrArg (fun q => Scheme.Modules.Hom.app q v.2) (hr v.1)

/-- Evaluation at the prescribed local generator determines a local dual map. -/
lemma local_hom_ext (i : Fin r)
    {φ ψ : (Scheme.Modules.pullback (D.chart i)).obj (powerIdealModule k D a d) ⟶
      (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)}
    (h : φ.app ⊤ (localGenerator k r n hr h3 hE D a d i) =
      ψ.app ⊤ (localGenerator k r n hr h3 hE D a d i)) : φ = ψ := by
  let F := fromSection _ (localGenerator k r n hr h3 hE D a d i)
  letI : IsIso (C := (specA k n).Modules) F := localGenerator_frame k r n hr h3 hE D a d i
  apply (cancel_epi F).mp
  apply unit_hom_ext
  simpa [F, fromSection_apply] using h

/-- The concrete numerator obtained from an actual global sheaf morphism. -/
def numerator (φ : GlobalDualSections k D a d) (i : Fin r) : A k n :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
    ((pulledInclusion (D.chart i) φ).app ⊤ (localGenerator k r n hr h3 hE D a d i))

lemma numerator_injective : Function.Injective (numerator k r n hr h3 hE D a d) := by
  intro φ ψ h
  apply hom_ext_pullback_cover (fun _ : Fin r => specA k n)
    D.chart D.chart_open D.covers
  intro i
  letI := unitPullback_isIso (D.chart i)
  apply (cancel_mono (unitPullback (D.chart i))).mp
  apply local_hom_ext k r n hr h3 hE D a d i
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective (congrFun h i)

/-- The generator condition in the frozen statement is equivalent to exact evaluation. -/
lemma realizes_iff (s : Sections k r n hr E a d) (φ : GlobalDualSections k D a d) :
    Realizes k D a d s φ ↔ numerator k r n hr h3 hE D a d φ = s.val := by
  constructor
  · intro h
    funext i
    obtain ⟨t, ht, hφ⟩ := h i
    have hj := pullback_open_realization (D.chart i) ((markedIdeal k r n hr D a)^d)
      (powerIdealModule k D a d) (idealInclusion _) (ideal_realization _)
    letI := hj.1
    have he : t = localGenerator k r n hr h3 hE D a d i :=
      mono_app_injective (pulledInclusion (D.chart i) (idealInclusion _)) ⊤
        (ht.trans (localGenerator_spec k r n hr h3 hE D a d i).symm)
    unfold numerator
    rw [← he]
    change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
      (((Scheme.Modules.pullback (D.chart i)).map φ ≫ unitPullback (D.chart i)).app ⊤ t) = _
    rw [hφ]
    exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _
  · intro h i
    refine ⟨localGenerator k r n hr h3 hE D a d i,
      localGenerator_spec k r n hr h3 hE D a d i, ?_⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective
    exact (congrFun h i).trans
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

lemma realizes_unique (s : Sections k r n hr E a d) {φ ψ : GlobalDualSections k D a d}
    (hφ : Realizes k D a d s φ) (hψ : Realizes k D a d s ψ) : φ = ψ := by
  apply numerator_injective k r n hr h3 hE D a d
  exact ((realizes_iff k r n hr h3 hE D a d s φ).mp hφ).trans
    ((realizes_iff k r n hr h3 hE D a d s ψ).mp hψ).symm

lemma frame_inclusion (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D a d i) ≫
      pulledInclusion (D.chart i) (idealInclusion ((markedIdeal k r n hr D a)^d)) =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          (localEquation k r n hr a d i) := by
  apply unit_hom_ext
  convert localGenerator_spec k r n hr h3 hE D a d i using 1 <;>
    simp [fromSection_apply] <;> rfl

lemma frame_evaluation (φ : GlobalDualSections k D a d) (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D a d i) ≫
      pulledInclusion (D.chart i) φ =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
            (numerator k r n hr h3 hE D a d φ i)) := by
  apply unit_hom_ext
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, fromSection_apply]
  simpa [numerator] using
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm_apply_apply
      ((pulledInclusion (D.chart i) φ).app ⊤ (localGenerator k r n hr h3 hE D a d i))).symm

lemma numerator_compatible (φ : GlobalDualSections k D a d) :
    Compatible k r n hr E a d (numerator k r n hr h3 hE D a d φ) := by
  intro i
  let α := fromSection _ (localGenerator k r n hr h3 hE D a d i)
  let β := fromSection _ (localGenerator k r n hr h3 hE D a d (next r hr i))
  letI : IsIso (C := (specA k n).Modules) α := localGenerator_frame k r n hr h3 hE D a d i
  let L := leftLeg k n E
  let R := rightLeg k n
  let e := squareIso (D.chart i) L (D.chart (next r hr i)) R
    (D.adjacent i).w (powerIdealModule k D a d)
  let α' := pullFrame L α
  let β' := pullFrame R β ≫ e.hom
  let J := pulledInclusion L (pulledInclusion (D.chart i)
    (idealInclusion ((markedIdeal k r n hr D a)^d)))
  let Q := pulledInclusion L (pulledInclusion (D.chart i) φ)
  letI : IsIso α' := pullFrame_isIso L α
  have h := frame_cross α' β' J Q
  have he (q : GlobalDualSections k D a d) :
      e.hom ≫ pulledInclusion L (pulledInclusion (D.chart i) q) =
        pulledInclusion R (pulledInclusion (D.chart (next r hr i)) q) :=
    squareIso_inclusion (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w _ q
  have hαJ : α' ≫ J = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (L.appTop (localEquation k r n hr a d i)) :=
    pullFrame_evaluation L α _ _ (frame_inclusion k r n hr h3 hE D a d i)
  have hβJ : β' ≫ J = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (R.appTop (localEquation k r n hr a d (next r hr i))) := by
    change (pullFrame R β ≫ e.hom) ≫ J = _
    rw [Category.assoc, he]
    exact pullFrame_evaluation R β _ _ (frame_inclusion k r n hr h3 hE D a d _)
  have hαQ : α' ≫ Q = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (L.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k r n hr h3 hE D a d φ i))) :=
    pullFrame_evaluation L α _ _ (frame_evaluation k r n hr h3 hE D a d φ i)
  have hβQ : β' ≫ Q = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (R.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k r n hr h3 hE D a d φ (next r hr i)))) := by
    change (pullFrame R β ≫ e.hom) ≫ Q = _
    rw [Category.assoc, he]
    exact pullFrame_evaluation R β _ _ (frame_evaluation k r n hr h3 hE D a d φ _)
  rw [hαQ, hβJ, hβQ, hαJ] at h
  have hv := multiplication_eq _ _ _ _ h
  have hv' := congrArg (fun z : Γ(specB k n true, ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom z) hv
  change (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
      (L.appTop _ * R.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
      (R.appTop _ * L.appTop _) at hv'
  simp only [map_mul] at hv'
  have hn {S T : CommRingCat.{u}} (f : S ⟶ T) (x : S) :
      (Scheme.ΓSpecIso T).hom ((Spec.map f).appTop ((Scheme.ΓSpecIso S).inv x)) = f x := by
    rw [ArithmeticThetaPolygonCohomologyR0131.PolygonGlobalFunctionsR0131.affine_pullback]
    exact congrArg f ((Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.apply_symm_apply x)
  dsimp only [L, R, leftLeg, rightLeg, localEquation] at hv'
  erw [hn, hn, hn, hn] at hv'
  simp only [map_pow] at hv'
  exact hv'

/-- The actual sheaf morphism determines a compatible numerator tuple. -/
def toSections (φ : GlobalDualSections k D a d) : Sections k r n hr E a d :=
  ⟨numerator k r n hr h3 hE D a d φ, numerator_compatible k r n hr h3 hE D a d φ⟩

lemma toSections_realizes (φ : GlobalDualSections k D a d) :
    Realizes k D a d (toSections k r n hr h3 hE D a d φ) φ :=
  (realizes_iff k r n hr h3 hE D a d _ φ).mpr rfl

lemma toSections_injective : Function.Injective (toSections k r n hr h3 hE D a d) := by
  intro φ ψ h
  exact numerator_injective k r n hr h3 hE D a d (congrArg Subtype.val h)

/-- An arbitrary numerator gives a local linear map by the inverse of the proven frame. -/
def localDual (b : A k n) (i : Fin r) :
    (Scheme.Modules.pullback (D.chart i)).obj (powerIdealModule k D a d) ⟶
      (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) := by
  let F := fromSection _ (localGenerator k r n hr h3 hE D a d i)
  letI : IsIso (C := (specA k n).Modules) F := localGenerator_frame k r n hr h3 hE D a d i
  exact inv F ≫ fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b)

lemma frame_localDual (b : A k n) (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D a d i) ≫
      localDual k r n hr h3 hE D a d b i =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b) := by
  letI := localGenerator_frame k r n hr h3 hE D a d i
  simp [localDual]

lemma localDual_value (b : A k n) (i : Fin r) :
    (localDual k r n hr h3 hE D a d b i).app ⊤ (localGenerator k r n hr h3 hE D a d i) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun q => Scheme.Modules.Hom.app q ⊤) (frame_localDual k r n hr h3 hE D a d b i))
    (1 : Γ(specA k n, ⊤))
  simpa [fromSection_apply] using h

set_option maxHeartbeats 100000 in
lemma compatible_on_overlap (s : Sections k r n hr E a d) (i : Fin r) :
    (leftLeg k n E).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val i)) *
        (rightLeg k n).appTop (localEquation k r n hr a d (next r hr i)) =
      (rightLeg k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val (next r hr i))) *
        (leftLeg k n E).appTop (localEquation k r n hr a d i) := by
  apply (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).commRingCatIsoToRingEquiv.injective
  simp only [map_mul]
  dsimp only [leftLeg, rightLeg, localEquation]
  erw [affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true))]
  simp only [map_pow]
  exact s.property i

set_option maxHeartbeats 1600000 in
/-- Adjacent local maps agree over the prescribed actual intersection. -/
lemma localDual_adjacent (s : Sections k r n hr E a d) (i : Fin r) :
    CategoryStruct.comp (obj := (specB k n true).Modules)
      (squareIso (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n)
        (D.adjacent i).w (powerIdealModule k D a d)).hom
      (pulledInclusion (leftLeg k n E) (localDual k r n hr h3 hE D a d (s.val i) i)) =
      pulledInclusion (rightLeg k n)
        (localDual k r n hr h3 hE D a d (s.val (next r hr i)) (next r hr i)) := by
  let α := fromSection _ (localGenerator k r n hr h3 hE D a d i)
  let β := fromSection _ (localGenerator k r n hr h3 hE D a d (next r hr i))
  letI : IsIso (C := (specA k n).Modules) α := localGenerator_frame k r n hr h3 hE D a d i
  letI : IsIso (C := (specA k n).Modules) β := localGenerator_frame k r n hr h3 hE D a d _
  let L := leftLeg k n E
  let R := rightLeg k n
  have hci := pullback_open_realization (D.chart i) ((markedIdeal k r n hr D a)^d)
    (powerIdealModule k D a d) (idealInclusion _) (ideal_realization _)
  have hj := pullback_open_realization L _ _ _ hci
  letI := hj.1
  exact frame_maps_glue L R
    (squareIso (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w (powerIdealModule k D a d)) α β
    (pulledInclusion (D.chart i) (idealInclusion ((markedIdeal k r n hr D a)^d)))
    (localDual k r n hr h3 hE D a d (s.val i) i)
    (pulledInclusion (D.chart (next r hr i)) (idealInclusion ((markedIdeal k r n hr D a)^d)))
    (localDual k r n hr h3 hE D a d (s.val (next r hr i)) (next r hr i))
    (squareIso_inclusion (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w _ (idealInclusion ((markedIdeal k r n hr D a)^d)))
    (localEquation k r n hr a d i)
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val i))
    (localEquation k r n hr a d (next r hr i))
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val (next r hr i)))
    (frame_inclusion k r n hr h3 hE D a d i)
    (frame_inclusion k r n hr h3 hE D a d (next r hr i))
    (frame_localDual k r n hr h3 hE D a d (s.val i) i)
    (frame_localDual k r n hr h3 hE D a d (s.val (next r hr i)) (next r hr i))
    (compatible_on_overlap k r n hr h3 hE a d s i)

/-- Every compatible numerator tuple descends to a global morphism of the canonical ideal power. -/
lemma exists_realizes (s : Sections k r n hr E a d) :
    ∃ φ : GlobalDualSections k D a d, Realizes k D a d s φ := by
  let q := fun i => localDual k r n hr h3 hE D a d (s.val i) i
  obtain ⟨φ, hφ⟩ := GlobalPositiveSectionDescentR0134.glue_local_maps
    (fun _ : Fin r => specA k n) D.chart D.chart_open D.covers (powerIdealModule k D a d) q (by
      intro i j V hi hj m
      by_cases hij : i = j
      · subst j
        rfl
      have hadj (i : Fin r) (V : D.X.Opens)
          (hi : V ≤ (D.chart i).opensRange) (hj : V ≤ (D.chart (next r hr i)).opensRange)
          (m : Γ(powerIdealModule k D a d, V)) :
          GlobalPositiveSectionDescentR0134.localValue (D.chart i) (q i) V hi m =
            GlobalPositiveSectionDescentR0134.localValue (D.chart (next r hr i)) (q (next r hr i)) V hj m := by
        apply GlobalPositiveSectionDescentR0134.localValue_square
          (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n)
          (D.adjacent i).w (powerIdealModule k D a d) (q i) (q (next r hr i))
          (localDual_adjacent k r n hr h3 hE D a d s i) V hi hj
        rw [GlobalPositiveSectionDescentR0134.square_range
          (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n) (D.adjacent i)]
        exact le_inf hi hj
      by_cases hn : next r hr i = j
      · subst j
        exact hadj i V hi hj m
      by_cases hm : next r hr j = i
      · subst i
        exact (hadj j V hj hi m).symm
      apply GlobalPositiveSectionDescentR0134.section_eq_of_empty V
      apply le_antisymm _ bot_le
      intro x hx
      exact (Set.disjoint_left.mp (D.disjoint i j hij hn hm)) (hi hx) (hj hx))
  refine ⟨φ, ?_⟩
  intro i
  refine ⟨localGenerator k r n hr h3 hE D a d i,
    localGenerator_spec k r n hr h3 hE D a d i, ?_⟩
  change (pulledInclusion (D.chart i) φ).app ⊤ _ = _
  rw [hφ i]
  exact localDual_value k r n hr h3 hE D a d (s.val i) i

lemma toSections_surjective : Function.Surjective (toSections k r n hr h3 hE D a d) := by
  intro s
  obtain ⟨φ, hφ⟩ := exists_realizes k r n hr h3 hE D a d s
  refine ⟨φ, Subtype.ext ?_⟩
  exact (realizes_iff k r n hr h3 hE D a d s φ).mp hφ

end GlobalPositiveSectionRealizationR0134

/-- Concrete compatible numerators are precisely actual global sections of the dual ideal power. -/
theorem global_positive_section_realization :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (a : Fin r → kˣ), ∀ (D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E) (d : ℕ),
    ∃ e : ArithmeticThetaPositiveLineR0134.Sections k r n hr E a d ≃
      ArithmeticThetaPositiveLineR0134.GlobalDualSections k D a d,
    ∀ s, ArithmeticThetaPositiveLineR0134.Realizes k D a d s (e s) := by
  intro k _ _ r n hr h3 E hE a D d
  let F := GlobalPositiveSectionRealizationR0134.toSections k r n hr h3 hE D a d
  have hF : Function.Bijective F :=
    ⟨GlobalPositiveSectionRealizationR0134.toSections_injective k r n hr h3 hE D a d,
      GlobalPositiveSectionRealizationR0134.toSections_surjective k r n hr h3 hE D a d⟩
  let e := (Equiv.ofBijective F hF).symm
  refine ⟨e, ?_⟩
  intro s
  apply (GlobalPositiveSectionRealizationR0134.realizes_iff k r n hr h3 hE D a d s (e s)).mpr
  exact congrArg Subtype.val ((Equiv.ofBijective F hF).apply_symm_apply s)

end ArithmeticThetaPositiveLineR0134
