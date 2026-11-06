module

public import LegendreLevelAtlasDefinitionsR0176
public import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field
public import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
public import Theorems.Thm_AlgebraicGeometry_Scheme_finite_flat_and_locally_eq_comp_of_free_of_quotient
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective

@[expose] public section

/-! The affine quotient of a scheme-theoretically free involution. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176.AffineFreeSignQuotient
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X : Scheme.{u}} (σ : X ⟶ X) (hsq : σ ≫ σ = 𝟙 X)

def involutionIso : X ≅ X := ⟨σ, σ, hsq, hsq⟩

abbrev Sign := Multiplicative (ZMod 2)

def signAction : Sign →* Aut X where
  toFun g := if g = 1 then Iso.refl X else involutionIso σ hsq
  map_one' := by simp; rfl
  map_mul' g h := by
    change Multiplicative (Fin 2) at g h
    fin_cases g <;> fin_cases h <;> apply Iso.ext <;>
      norm_num [involutionIso, Aut.Aut_mul_def, hsq]
    rw [if_pos (by decide)]
    rfl

lemma signAction_generator :
    (signAction σ hsq (Multiplicative.ofAdd (1 : ZMod 2))).hom = σ := by
  simp [signAction, involutionIso]

lemma signAction_invariant {T : Scheme.{u}} (a : X ⟶ T) (ha : σ ≫ a = a)
    (g : Sign) : (signAction σ hsq g).hom ≫ a = a := by
  change (if g = 1 then Iso.refl X else involutionIso σ hsq).hom ≫ a = a
  split_ifs <;> simp_all [involutionIso]

lemma signAction_admissible [IsAffine X] :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ g : Sign, (signAction σ hsq g).hom ⁻¹ᵁ U = U := by
  intro x
  exact ⟨⊤, isAffineOpen_top X, trivial, fun _ => rfl⟩

/-- Empty equalizer gives freeness on every nonempty test scheme. -/
lemma no_fixed_test_map (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u}))
    {T : Scheme.{u}} [Nonempty T] (a : T ⟶ X) : a ≫ σ ≠ a := by
  intro ha
  letI := hfree
  let b := equalizer.lift a (ha.trans (Category.comp_id a).symm)
  obtain ⟨t⟩ := ‹Nonempty T›
  exact isEmptyElim (b t)

lemma signAction_free (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u}))
    (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ X) (g : Sign)
    (ha : a ≫ (signAction σ hsq g).hom = a) : g = 1 := by
  by_contra hg
  have he : (signAction σ hsq g).hom = σ := by
    simp [signAction, hg, involutionIso]
  rw [he] at ha
  exact no_fixed_test_map σ hfree a ha

/-- Quotient geometry before identifying its coordinate ring and its degree. -/
structure GeometricQuotient where
  target : Scheme.{u}
  affine : IsAffine target
  map : X ⟶ target
  invariant : σ ≫ map = map
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  universal : ∀ (T : Scheme.{u}) (a : X ⟶ T), σ ≫ a = a →
    ∃! b : target ⟶ T, map ≫ b = a
  locally_orbit : ∀ {T : Scheme.{u}} (a b : T ⟶ X), a ≫ map = b ≫ map →
    ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      (U.ι ≫ b = U.ι ≫ a ∨ U.ι ≫ b = U.ι ≫ a ≫ σ)

include hsq in
/-- The library quotient is constructed from the action on the whole affine
scheme. The invariant open equal to the whole source proves affineness of its
target, even for an empty or disconnected source. -/
theorem geometricQuotient_nonempty [IsAffine X]
    (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u})) :
    Nonempty (GeometricQuotient σ) := by
  let ρ := signAction σ hsq
  have hadm := signAction_admissible σ hsq
  obtain ⟨Y, q, hq, hint, haff, hsurj, hfib, hinj, hrange, hopen, huniv⟩ :=
    Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant ρ hadm
  obtain ⟨hfinite, hflat, hetale, hfp, hlocal, hfree'⟩ :=
    Scheme.finite_flat_and_locally_eq_comp_of_free_of_quotient
      ρ hadm q hq haff hsurj hfib hinj hrange (signAction_free σ hsq hfree)
  obtain ⟨V, hV, hpre⟩ := hopen ⊤ (isAffineOpen_top X) (fun _ => rfl)
  have hVtop : V = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, hx⟩ := hsurj y
    have hm : x ∈ q ⁻¹ᵁ V := by rw [hpre]; trivial
    change q x ∈ V at hm
    simpa only [show q x = y from hx] using hm
  haveI : IsAffine (⊤ : Y.Opens).toScheme := hVtop ▸ hV
  have hY : IsAffine Y := IsAffine.of_isIso Y.topIso.inv
  refine ⟨{
    target := Y
    affine := hY
    map := q
    invariant := ?_
    finite := hfinite
    etale := hetale
    surjective := ⟨hsurj⟩
    universal := ?_
    locally_orbit := ?_ }⟩
  · simpa only [ρ, signAction_generator] using hq (Multiplicative.ofAdd (1 : ZMod 2))
  · intro T a ha
    exact huniv T a (signAction_invariant σ hsq a ha)
  · intro T a b hab t
    obtain ⟨g, U, ht, he⟩ := hlocal a b hab t
    refine ⟨U, ht, ?_⟩
    by_cases hg : g = 1
    · left
      simpa [ρ, signAction, hg] using he
    · right
      simpa [ρ, signAction, hg, involutionIso] using he

attribute [instance] GeometricQuotient.affine GeometricQuotient.finite
  GeometricQuotient.etale GeometricQuotient.surjective

namespace GeometricQuotient
variable {σ} (Q : GeometricQuotient σ)

def diagonalBranch : X ⟶ pullback Q.map Q.map :=
  pullback.lift (𝟙 X) (𝟙 X) rfl

def signBranch : X ⟶ pullback Q.map Q.map :=
  pullback.lift (𝟙 X) σ (by simp [Q.invariant])

@[simp] lemma diagonalBranch_fst : Q.diagonalBranch ≫ pullback.fst Q.map Q.map = 𝟙 X :=
  pullback.lift_fst _ _ _
@[simp] lemma diagonalBranch_snd : Q.diagonalBranch ≫ pullback.snd Q.map Q.map = 𝟙 X :=
  pullback.lift_snd _ _ _
@[simp] lemma signBranch_fst : Q.signBranch ≫ pullback.fst Q.map Q.map = 𝟙 X :=
  pullback.lift_fst _ _ _
@[simp] lemma signBranch_snd : Q.signBranch ≫ pullback.snd Q.map Q.map = σ :=
  pullback.lift_snd _ _ _

instance : IsOpenImmersion Q.diagonalBranch :=
  (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    (pullback.fst Q.map Q.map) Q.diagonalBranch Q.diagonalBranch_fst).1
instance : IsOpenImmersion Q.signBranch :=
  (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    (pullback.fst Q.map Q.map) Q.signBranch Q.signBranch_fst).1

lemma branches_disjoint (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u})) :
    Disjoint (Set.range Q.diagonalBranch) (Set.range Q.signBranch) := by
  apply Scheme.isEmpty_pullback_iff.mp
  constructor
  intro t
  let T := pullback Q.diagonalBranch Q.signBranch
  letI : Nonempty T := ⟨t⟩
  let a : T ⟶ X := pullback.fst Q.diagonalBranch Q.signBranch
  let b : T ⟶ X := pullback.snd Q.diagonalBranch Q.signBranch
  have h := pullback.condition (f := Q.diagonalBranch) (g := Q.signBranch)
  have hab : a = b := by
    simpa only [Category.assoc, diagonalBranch_fst, signBranch_fst, Category.comp_id]
      using congrArg (fun f => f ≫ pullback.fst Q.map Q.map) h
  have habσ : a = b ≫ σ := by
    simpa only [Category.assoc, diagonalBranch_snd, signBranch_snd, Category.comp_id]
      using congrArg (fun f => f ≫ pullback.snd Q.map Q.map) h
  exact no_fixed_test_map σ hfree b (habσ.symm.trans hab)

def relationMap : X ⨿ X ⟶ pullback Q.map Q.map :=
  coprod.desc Q.diagonalBranch Q.signBranch

lemma relationMap_openImmersion (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u})) :
    IsOpenImmersion Q.relationMap := by
  have hd := Q.branches_disjoint hfree
  apply IsOpenImmersion.of_openCover_source _ (coprodOpenCover.{u,u} X X)
  · intro x y he
    obtain ⟨x | x, rfl⟩ := (coprodMk X X).surjective x
    <;> obtain ⟨y | y, rfl⟩ := (coprodMk X X).surjective y
    · simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, relationMap, coprod.inl_desc] at he
      exact congrArg (fun z => coprodMk X X (.inl z)) (Q.diagonalBranch.injective he)
    · simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
        relationMap, coprod.inl_desc, coprod.inr_desc] at he
      exact (Set.disjoint_iff_forall_ne.mp hd ⟨x, rfl⟩ ⟨y, rfl⟩ he).elim
    · simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
        relationMap, coprod.inl_desc, coprod.inr_desc] at he
      exact (Set.disjoint_iff_forall_ne.mp hd ⟨y, rfl⟩ ⟨x, rfl⟩ he.symm).elim
    · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, relationMap, coprod.inr_desc] at he
      exact congrArg (fun z => coprodMk X X (.inr z)) (Q.signBranch.injective he)
  · rintro (i | i) <;> dsimp [coprodOpenCover, relationMap] <;> simp only [coprod.inl_desc,
      coprod.inr_desc] <;> infer_instance

lemma relationMap_surjective : Surjective Q.relationMap := by
  constructor
  intro t
  obtain ⟨U, ht, he | he⟩ := Q.locally_orbit
    (pullback.fst Q.map Q.map) (pullback.snd Q.map Q.map) pullback.condition t
  · have hf : U.ι ≫ pullback.fst Q.map Q.map ≫ Q.diagonalBranch = U.ι := by
      apply pullback.hom_ext <;> simp only [Category.assoc, diagonalBranch_fst,
        diagonalBranch_snd, Category.comp_id]
      exact he.symm
    refine ⟨(coprod.inl : X ⟶ X ⨿ X) (pullback.fst Q.map Q.map t), ?_⟩
    have hx := congrArg (fun f => f ⟨t, ht⟩) hf
    change Q.diagonalBranch (pullback.fst Q.map Q.map t) = t at hx
    change (coprod.inl ≫ Q.relationMap) (pullback.fst Q.map Q.map t) = t
    simpa only [relationMap, coprod.inl_desc] using hx
  · have hf : U.ι ≫ pullback.fst Q.map Q.map ≫ Q.signBranch = U.ι := by
      apply pullback.hom_ext <;> simp only [Category.assoc, signBranch_fst,
        signBranch_snd, Category.comp_id]
      exact he.symm
    refine ⟨(coprod.inr : X ⟶ X ⨿ X) (pullback.fst Q.map Q.map t), ?_⟩
    have hx := congrArg (fun f => f ⟨t, ht⟩) hf
    change Q.signBranch (pullback.fst Q.map Q.map t) = t at hx
    change (coprod.inr ≫ Q.relationMap) (pullback.fst Q.map Q.map t) = t
    simpa only [relationMap, coprod.inr_desc] using hx

/-- The entire orbit relation is an isomorphism of schemes. -/
def relationIso (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u})) :
    X ⨿ X ≅ pullback Q.map Q.map := by
  letI := Q.relationMap_openImmersion hfree
  letI := Q.relationMap_surjective
  letI : IsIso Q.relationMap :=
    (isIso_iff_isOpenImmersion_and_surjective Q.relationMap).mpr ⟨inferInstance, inferInstance⟩
  exact asIso Q.relationMap

end GeometricQuotient

/-- The fold map on two copies of an affine scheme has constant rank two. -/
lemma fold_finrank [IsAffine X] (x : X) :
    (coprod.desc (𝟙 X) (𝟙 X)).finrank x = 2 := by
  letI : Nonempty X := ⟨x⟩
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let R : Type u := Γ(X, ⊤)
  haveI : Nontrivial R := inferInstance
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))
  haveI : Flat f := Flat.SpecMap_iff.mpr (by
    change (algebraMap R (R × R)).Flat
    rw [RingHom.flat_algebraMap_iff]; infer_instance)
  haveI : IsFinite f := (IsFinite.SpecMap_iff _).mpr (by
    change (algebraMap R (R × R)).Finite
    rw [RingHom.finite_algebraMap]; infer_instance)
  let e : X ⨿ X ≅ Spec (CommRingCat.of (R × R)) :=
    coprod.mapIso X.isoSpec X.isoSpec ≪≫ asIso (coprodSpec R R)
  have he : e.hom ≫ f = coprod.desc (𝟙 X) (𝟙 X) ≫ X.isoSpec.hom := by
    apply coprod.hom_ext <;>
      simp only [e, Iso.trans_hom, coprod.mapIso_hom, asIso_hom, Category.assoc,
        coprod.inl_map_assoc, coprod.inr_map_assoc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
        Category.id_comp]
    · rw [coprodSpec_inl_assoc]
      change X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.fst R R)) ≫ f = _
      dsimp only [f]
      rw [← Spec.map_comp]
      have hh : CommRingCat.ofHom (algebraMap R (R × R)) ≫
          CommRingCat.ofHom (RingHom.fst R R) = 𝟙 (CommRingCat.of R) := rfl
      rw [hh, Spec.map_id]
      exact Category.comp_id X.isoSpec.hom
    · rw [coprodSpec_inr_assoc]
      change X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.snd R R)) ≫ f = _
      dsimp only [f]
      rw [← Spec.map_comp]
      have hh : CommRingCat.ofHom (algebraMap R (R × R)) ≫
          CommRingCat.ofHom (RingHom.snd R R) = 𝟙 (CommRingCat.of R) := rfl
      rw [hh, Spec.map_id]
      exact Category.comp_id X.isoSpec.hom
  have hp : IsPullback e.hom (coprod.desc (𝟙 X) (𝟙 X)) f X.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨he⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hp]
  change (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))).finrank _ = 2
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rw [Module.finrank_prod, Module.finrank_self]
  norm_num

namespace GeometricQuotient
variable {σ} (Q : GeometricQuotient σ)

lemma degree [IsAffine X] (hfree : IsEmpty (equalizer σ (𝟙 X) : Scheme.{u}))
    (y : Q.target) : Q.map.finrank y = 2 := by
  obtain ⟨x, rfl⟩ := Q.map.surjective y
  have he : (Q.relationIso hfree).hom ≫ pullback.fst Q.map Q.map =
      coprod.desc (𝟙 X) (𝟙 X) := by
    apply coprod.hom_ext <;>
      simp [relationIso, relationMap]
  rw [← Scheme.Hom.finrank_pullback_fst,
    ← Scheme.Hom.finrank_comp_left_of_isIso (Q.relationIso hfree).hom, he]
  exact fold_finrank x

/-- Transport to an affine presentation, retaining the same quotient map. -/
def transport {Y : Scheme.{u}} [IsAffine Y] (e : Q.target ≅ Y) :
    GeometricQuotient σ where
  target := Y
  affine := inferInstance
  map := Q.map ≫ e.hom
  invariant := by rw [← Category.assoc, Q.invariant]
  finite := inferInstance
  etale := inferInstance
  surjective := inferInstance
  universal := by
    intro T a ha
    obtain ⟨b, hb, hu⟩ := Q.universal T a ha
    refine ⟨e.inv ≫ b, by simpa using hb, ?_⟩
    intro c hc
    have heq : e.hom ≫ c = b := hu _ (by simpa only [Category.assoc] using hc)
    rw [← heq, e.inv_hom_id_assoc]
  locally_orbit := by
    intro T a b hab
    exact Q.locally_orbit a b ((cancel_mono e.hom).mp (by
      simpa only [Category.assoc] using hab))

end GeometricQuotient
end ArithmeticThetaLegendreAtlasR0176.AffineFreeSignQuotient

namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171
open AffineFreeSignQuotient

/-- The actual invariant affine quotient of a free involution, including its
full orbit relation, constant degree and categorical universal property. -/
theorem affine_free_sign_quotient :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) [IsAffine X]
      (p : X ⟶ Base k) [SmoothOfRelativeDimension 1 p] (σ : X ⟶ X),
      σ ≫ p = p → σ ≫ σ = 𝟙 X →
      IsEmpty (equalizer σ (𝟙 X) : Scheme.{u}) → Nonempty (SignQuotient k p σ) := by
  intro k _ _ X _ p _ σ hover hsq hfree
  obtain ⟨Q⟩ := geometricQuotient_nonempty σ hsq hfree
  obtain ⟨b, hb, _⟩ := Q.universal (Base k) p hover
  let R : Type u := Γ(Q.target, ⊤)
  let φ : k →+* R := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop).hom
  letI : Algebra k R := φ.toAlgebra
  let e : Q.target ≅ Base R := Q.target.isoSpec
  let Q' := Q.transport e
  let f : Base R ⟶ Base k := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have he : e.hom ≫ f = b := by
    change Q.target.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop) = b
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hp : Q'.map ≫ f = p := by
    change (Q.map ≫ e.hom) ≫ f = p
    rw [Category.assoc, he, hb]
  haveI : SmoothOfRelativeDimension 1 (Q'.map ≫ f) := hp ▸ inferInstance
  have hsmooth : SmoothOfRelativeDimension 1 f := by
    cases isEmpty_or_nonempty X with
    | inl hx =>
      letI := hx
      haveI : IsEmpty (Base R) := ⟨fun y => by
        obtain ⟨x, _⟩ := Q'.map.surjective y
        exact isEmptyElim x⟩
      exact ⟨fun x => isEmptyElim x⟩
    | inr hx =>
      letI := hx
      exact (SmoothOfRelativeDimension.of_comp_of_surjective_of_field f Q'.map 1 0).1
  refine ⟨{
    ring := R
    q := Q'.map
    over_eq := hp
    invariant := Q'.invariant
    finite := Q'.finite
    etale := Q'.etale
    surjective := Q'.surjective
    degree := Q'.degree hfree
    smooth := hsmooth
    relation := Q'.relationIso hfree
    left_fst := ?_
    left_snd := ?_
    right_fst := ?_
    right_snd := ?_
    universal := Q'.universal }⟩
  all_goals simp [GeometricQuotient.relationIso, GeometricQuotient.relationMap]

end ArithmeticThetaLegendreAtlasR0176
