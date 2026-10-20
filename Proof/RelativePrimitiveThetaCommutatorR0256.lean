module

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
public import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_monoidalV2
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
public import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support
public import RelativeThetaRelationsDefinitionsR0256
public import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw

@[expose] public section

/-! Structural scalar preparation for the relative primitive commutator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u

namespace ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open RelativeMidpointSymmetricThetaLift
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

/-- Structural scalars are exactly all global units, including on an empty base. -/
lemma scalar_bijective : Function.Bijective (scalar E) := by
  let f := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ E.projection.appTop).hom
  have hf := RelativeNormalizedThetaInversion.constants_bijective E
  constructor
  · intro a b h
    apply Units.ext
    exact hf.1 (congrArg Units.val h)
  · intro s
    obtain ⟨a, ha⟩ := hf.2 (s : Γ(E.curve, ⊤))
    obtain ⟨b, hb⟩ := hf.2 (↑s⁻¹ : Γ(E.curve, ⊤))
    have hab : a * b = 1 := hf.1 (by
      change f (a * b) = f 1
      rw [map_mul, map_one, ha, hb, Units.mul_inv])
    refine ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ?_⟩
    exact Units.ext ha

/-- Two actual lifts over the same map differ by a unique structural unit. -/
lemma existsUnique_scaled (m : ℕ) (f : E.curve ⟶ E.curve)
    (α β : Lift E m f) : ∃! c : Rˣ, α = scaled E m c β := by
  obtain ⟨s, hs⟩ := aut_scalar (RelativeNormalizedThetaInversion.line_invertible E m)
    (β.symm ≪≫ α)
  obtain ⟨c, hc⟩ := (scalar_bijective E).2 s
  have heq : α = scaled E m c β := by
    unfold scaled
    rw [hc, hs]
    simp
  refine ⟨c, heq, ?_⟩
  intro d hd
  apply (scalar_bijective E).1
  apply Units.ext
  apply smulHom_injective (RelativeNormalizedThetaInversion.line_invertible E m)
  have h := congrArg Iso.hom (hd.symm.trans heq)
  exact (cancel_epi β.hom).mp h

/-- The actual doubled translations commute on the entire curve. -/
lemma translations_commute (P Q : point E) :
    translation E P ≫ translation E Q = translation E Q ≫ translation E P := by
  let a := E.law.nsmul (𝟙 _) 2 P
  let b := E.law.nsmul (𝟙 _) 2 Q
  let ca : SchemeHomOver E.projection E.projection :=
    ⟨E.projection ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let cb : SchemeHomOver E.projection E.projection :=
    ⟨E.projection ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  let i : SchemeHomOver E.projection E.projection :=
    ⟨𝟙 E.curve, Category.id_comp _⟩
  change (E.law.mul E.projection i ca).val ≫ E.law.translate b =
    (E.law.mul E.projection i cb).val ≫ E.law.translate a
  rw [point_translate, point_translate]
  change (E.law.mul E.projection (E.law.mul E.projection i ca) cb).val =
    (E.law.mul E.projection (E.law.mul E.projection i cb) ca).val
  rw [E.law.mul_assoc, E.law.mul_assoc, E.commutative E.projection ca cb]

/-- Existence and uniqueness of the scalar uses no torsion or level hypothesis.
Its order and fibrewise primitivity require additional geometric arguments. -/
lemma existsUnique_commutator (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) :
    ∃! c : Rˣ, Commutator E m P Q α β c := by
  let h := translations_commute E P Q
  obtain ⟨c, hc, hu⟩ := existsUnique_scaled E m _
    (compose E m _ _ α β) (changeMap E m h (compose E m _ _ β α))
  refine ⟨c, ⟨h, hc⟩, ?_⟩
  rintro d ⟨h', hd⟩
  exact hu d hd

#print axioms scalar_bijective
#print axioms existsUnique_scaled
#print axioms translations_commute
#print axioms existsUnique_commutator

open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180

/-- Doubling the given full 2m-level produces an actual full m-level.
The disjointness assertion is retained over the whole base. -/
def doubledLevel (m : ℕ) (M : FamilyLevel R E (2 * m)) : FamilyLevel R E m where
  x := E.law.nsmul (𝟙 _) 2 M.x
  y := E.law.nsmul (𝟙 _) 2 M.y
  killed_x := RelativeDoubledTorsionThetaLiftR0255.doubled_killed E m M.x M.killed_x
  killed_y := RelativeDoubledTorsionThetaLiftR0255.doubled_killed E m M.y M.killed_y
  avoids := by
    intro i j hij
    have hi : 2 * i.val < 2 * m := by omega
    have hj : 2 * j.val < 2 * m := by omega
    have hn : 2 * i.val ≠ 0 ∨ 2 * j.val ≠ 0 := by omega
    have h := M.avoids ⟨2 * i.val, hi⟩ ⟨2 * j.val, hj⟩ hn
    letI := sectionGroup E
    simpa only [nsmul_pow, ← pow_mul] using h

/-- Unit tests reduce to nonvanishing in all field-valued fibres. This does
not replace a ring equality by an equality only on reduced fibres. -/
lemma isUnit_iff_field_nonzero (a : R) :
    IsUnit a ↔ ∀ (k : Type u) [Field k] (f : R →+* k), f a ≠ 0 := by
  constructor
  · intro ha k _ f
    exact (ha.map f).ne_zero
  · intro h
    by_contra ha
    obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits ha
    letI := hI
    letI := Ideal.Quotient.field I
    exact h (R ⧸ I) (Ideal.Quotient.mk I) ((Ideal.Quotient.eq_zero_iff_mem).mpr haI)

/-- The exact global period equation is retained alongside all fibre tests. -/
lemma primitiveUnit_iff_field_tests (m : ℕ) (c : Rˣ) :
    PrimitiveUnit m c ↔ c ^ m = 1 ∧
      ∀ (k : Type u) [Field k] (f : R →+* k) (i : Fin m),
        i.val ≠ 0 → f (c : R) ^ i.val ≠ 1 := by
  constructor
  · rintro ⟨hp, hu⟩
    refine ⟨hp, ?_⟩
    intro k _ f i hi
    have h := (isUnit_iff_field_nonzero ((c : R) ^ i.val - 1)).mp (hu i hi) k f
    simpa only [map_sub, map_pow, map_one, sub_ne_zero] using h
  · rintro ⟨hp, hu⟩
    refine ⟨hp, ?_⟩
    intro i hi
    apply (isUnit_iff_field_nonzero _).mpr
    intro k _ f
    simpa only [map_sub, map_pow, map_one, sub_ne_zero] using hu k f i hi

#print axioms doubledLevel
#print axioms isUnit_iff_field_nonzero
#print axioms primitiveUnit_iff_field_tests

lemma pullback_scalar (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection)
    (c : Rˣ) : Units.map f.appTop.hom.toMonoidHom (scalar E c) = scalar E c := by
  apply Units.ext
  change f.appTop (E.projection.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) =
    E.projection.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf]

lemma scaled_mul (m : ℕ) {f : E.curve ⟶ E.curve} (c d : Rˣ) (α : Lift E m f) :
    scaled E m c (scaled E m d α) = scaled E m (c * d) α := by
  apply Iso.ext
  change (α.hom ≫ smulHom (scalar E d : Γ(E.curve, ⊤)) _) ≫
    smulHom (scalar E c : Γ(E.curve, ⊤)) _ =
    α.hom ≫ smulHom (scalar E (c * d) : Γ(E.curve, ⊤)) _
  rw [Category.assoc, ← smulHom_mul]
  simp only [scalar, Units.coe_map, Units.val_mul, map_mul]

lemma scaled_injective (m : ℕ) {f : E.curve ⟶ E.curve} (c : Rˣ) :
    Function.Injective (fun α : Lift E m f => scaled E m c α) := by
  intro α β h
  apply Iso.ext
  exact (cancel_mono (smulIso (scalar E c) (thetaLine E m)).hom).mp (congrArg Iso.hom h)

lemma changeMap_scaled (m : ℕ) {f g : E.curve ⟶ E.curve} (h : f = g)
    (c : Rˣ) (α : Lift E m g) :
    changeMap E m h (scaled E m c α) = scaled E m c (changeMap E m h α) := by
  apply Iso.ext
  exact (Category.assoc _ _ _).symm

lemma compose_scaled_left (m : ℕ) (f g : E.curve ⟶ E.curve)
    (α : Lift E m f) (β : Lift E m g) (c : Rˣ) :
    compose E m f g (scaled E m c α) β = scaled E m c (compose E m f g α β) := by
  apply Iso.ext
  simp only [compose, scaled, Iso.trans_hom, Category.assoc]

lemma compose_scaled_right (m : ℕ) (f g : E.curve ⟶ E.curve)
    (hf : f ≫ E.projection = E.projection)
    (α : Lift E m f) (β : Lift E m g) (c : Rˣ) :
    compose E m f g α (scaled E m c β) = scaled E m c (compose E m f g α β) := by
  unfold compose scaled
  rw [Functor.mapIso_trans, pullback_mapIso_smulIso, pullback_scalar E f hf c]
  apply Iso.ext
  simp only [Iso.trans_hom, smulIso, Category.assoc, smulHom_comp]

/-- Changing either lift by an arbitrary structural unit does not change
the commutator, as an equality of sheaf isomorphisms. -/
lemma commutator_scaled (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (a b c : Rˣ) :
    Commutator E m P Q (scaled E m a α) (scaled E m b β) c ↔
      Commutator E m P Q α β c := by
  have hp := RelativeDoubledTorsionThetaLiftR0255.translation_over E P
  have hq := RelativeDoubledTorsionThetaLiftR0255.translation_over E Q
  unfold Commutator
  simp only [compose_scaled_left, compose_scaled_right E m _ _ hp,
    compose_scaled_right E m _ _ hq, changeMap_scaled, scaled_mul]
  have habc : c * (a * b) = (b * a) * c := by ac_rfl
  simp only [habc, ← scaled_mul]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, scaled_injective E m a (scaled_injective E m b hh)⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, congrArg (fun δ => scaled E m b (scaled E m a δ)) hh⟩

#print axioms commutator_scaled

/-- The scalar comparison is independent of every choice of the two lifts. -/
lemma commutator_independent (m : ℕ) (P Q : point E)
    (α α' : Lift E m (translation E P)) (β β' : Lift E m (translation E Q))
    (c : Rˣ) : Commutator E m P Q α β c ↔ Commutator E m P Q α' β' c := by
  obtain ⟨a, ha, _⟩ := existsUnique_scaled E m _ α α'
  obtain ⟨b, hb, _⟩ := existsUnique_scaled E m _ β β'
  rw [ha, hb]
  exact commutator_scaled E m P Q α' β' a b c

/-- The canonical scalar is constructed from the actual sheaf compositions. -/
def commutatorUnit (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) : Rˣ :=
  (existsUnique_commutator E m P Q α β).exists.choose

lemma commutatorUnit_spec (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) :
    Commutator E m P Q α β (commutatorUnit E m P Q α β) :=
  (existsUnique_commutator E m P Q α β).exists.choose_spec

lemma commutator_iff (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) (c : Rˣ) :
    Commutator E m P Q α β c ↔ c = commutatorUnit E m P Q α β := by
  constructor
  · intro hc
    exact (existsUnique_commutator E m P Q α β).unique hc (commutatorUnit_spec E m P Q α β)
  · rintro rfl
    exact commutatorUnit_spec E m P Q α β

#print axioms commutator_independent
#print axioms commutatorUnit_spec
#print axioms commutator_iff

/-! A universe-polymorphic total category for the actual line sheaf. The
library's theta-group specialization is restricted to universe zero; the
underlying pseudofunctor and Grothendieck construction are polymorphic. -/
namespace LinePair
open CategoryTheory.Bicategory

def fibration : Pseudofunctor (LocallyDiscrete (Scheme.{u}ᵒᵖ)) Cat.{u, u+1} :=
  (Scheme.Modules.pseudofunctor.{u}).comp Adj.forget₁

abbrev obj {X : Scheme.{u}} (M : X.Modules) :
    Pseudofunctor.CoGrothendieck fibration := ⟨X, M⟩

lemma mapComp_inv_app {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp a b).hom.app M := by
  simp [fibration, Pseudofunctor.comp_mapComp]
  exact Category.id_comp _

lemma mapId_inv_app (X : Scheme.{u}) (M : X.Modules) :
    (fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackId X).inv.app M := by
  simp [fibration, Pseudofunctor.comp_mapId]

lemma congr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

variable {X : Scheme.{u}} (M : X.Modules)

def toAut (e : X ≅ X) (α : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    Aut (obj M) :=
  Pseudofunctor.CoGrothendieck.isoMk (X := obj M) (Y := obj M) e α.symm

@[simp] lemma toAut_base (e : X ≅ X) (α : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (toAut M e α).hom.base = e.hom := rfl

@[simp] lemma toAut_fiber (e : X ≅ X) (α : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (toAut M e α).hom.fiber = α.inv := rfl

lemma toAut_trans (e₁ e₂ e₃ : X ≅ X) (h : e₃.hom = e₁.hom ≫ e₂.hom)
    (α : (Scheme.Modules.pullback e₁.hom).obj M ≅ M)
    (β : (Scheme.Modules.pullback e₂.hom).obj M ≅ M) :
    toAut M e₃ ((Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp e₁.hom e₂.hom).app M).symm ≪≫
      (Scheme.Modules.pullback e₁.hom).mapIso β ≪≫ α) =
        toAut M e₁ α ≪≫ toAut M e₂ β := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.trans_hom, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
    toAut_fiber, toAut_base]
  change _ = (α.inv ≫ (Scheme.Modules.pullback e₁.hom).map β.inv ≫
    (fibration.mapComp e₂.hom.op.toLoc e₁.hom.op.toLoc).inv.toNatTrans.app M) ≫ _
  simp only [mapComp_inv_app, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Iso.app_inv, Iso.app_hom, Category.assoc, congr_inv]

lemma toAut_refl (e : X ≅ X) (h : e.hom = 𝟙 X) :
    toAut M e ((Scheme.Modules.pullbackCongr h).app M ≪≫
      (Scheme.Modules.pullbackId X).app M) = Iso.refl _ := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.refl_hom, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, toAut_fiber]
  change _ = (fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app M ≫ _
  simp only [mapId_inv_app, Iso.trans_inv, Iso.app_inv, congr_inv]

lemma toAut_injective (e : X ≅ X) : Function.Injective (toAut M e) := by
  intro α β h
  have h₁ := Pseudofunctor.CoGrothendieck.Hom.congr (congrArg Iso.hom h)
  simp only [toAut_fiber, toAut_base, eqToHom_refl, Category.comp_id] at h₁
  have h₂ : α.symm = β.symm := Iso.ext h₁
  simpa using congrArg Iso.symm h₂

end LinePair

#print axioms LinePair.toAut_trans
#print axioms LinePair.toAut_refl
#print axioms LinePair.toAut_injective

lemma pullback_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (p : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (f ≫ 𝟙 Y)).obj M) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
      (Scheme.Modules.pullbackComp f (𝟙 Y)).hom.app M = eqToHom p := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToHom_app] at h
  erw [Category.comp_id ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M))] at h
  rw [← cancel_mono ((Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app M ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M))]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, h, eqToHom_trans, eqToHom_refl]

set_option synthInstance.maxHeartbeats 100000 in
lemma pullback_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (𝟙 X ≫ f)).obj M) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app M = eqToHom q := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at h
  erw [Category.comp_id ((Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj M))] at h
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (𝟙 X) f).inv.app M ≫
    (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj M))]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, h, eqToHom_trans, eqToHom_refl]

lemma compose_identity_right (m : ℕ) (f : E.curve ⟶ E.curve) (α : Lift E m f) :
    changeMap E m (Category.comp_id f).symm
      (compose E m f (𝟙 _) α (identityLift E m)) = α := by
  apply Iso.ext_inv
  simp only [changeMap, compose, identityLift, Iso.symm_hom, Iso.trans_inv,
    Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc]
  rw [reassoc_of% (pullback_right_unit f (thetaLine E m) (by rw [Category.comp_id])), LinePair.congr_inv,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

lemma compose_identity_left (m : ℕ) (f : E.curve ⟶ E.curve) (α : Lift E m f) :
    changeMap E m (Category.id_comp f).symm
      (compose E m (𝟙 _) f (identityLift E m) α) = α := by
  apply Iso.ext_inv
  simp only [changeMap, compose, identityLift, Iso.symm_hom, Iso.trans_inv,
    Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc]
  have hn := (Scheme.Modules.pullbackId E.curve).inv.naturality α.inv
  rw [Functor.id_map] at hn
  rw [← reassoc_of% hn, reassoc_of% (pullback_left_unit f (thetaLine E m) (by rw [Category.id_comp])),
    LinePair.congr_inv, eqToHom_trans, eqToHom_refl, Category.comp_id]

abbrev scalarAut (m : ℕ) (c : Rˣ) : Aut (LinePair.obj (thetaLine E m)) :=
  LinePair.toAut (thetaLine E m) (Iso.refl _) (scaled E m c (identityLift E m))

lemma toAut_scaled_right (m : ℕ) (e : Aut E.curve)
    (he : e.hom ≫ E.projection = E.projection) (α : Lift E m e.hom) (c : Rˣ) :
    LinePair.toAut _ e (scaled E m c α) = LinePair.toAut _ e α ≪≫ scalarAut E m c := by
  rw [← LinePair.toAut_trans _ e (Iso.refl _) e (Category.comp_id _).symm]
  change LinePair.toAut _ e (scaled E m c α) =
    LinePair.toAut _ e (changeMap E m (Category.comp_id _).symm
      (compose E m _ _ α (scaled E m c (identityLift E m))))
  rw [compose_scaled_right E m _ _ he, changeMap_scaled, compose_identity_right]

lemma toAut_scaled_left (m : ℕ) (e : Aut E.curve)
    (α : Lift E m e.hom) (c : Rˣ) :
    LinePair.toAut _ e (scaled E m c α) = scalarAut E m c ≪≫ LinePair.toAut _ e α := by
  rw [← LinePair.toAut_trans _ (Iso.refl _) e e (Category.id_comp _).symm]
  change LinePair.toAut _ e (scaled E m c α) =
    LinePair.toAut _ e (changeMap E m (Category.id_comp _).symm
      (compose E m _ _ (scaled E m c (identityLift E m)) α))
  rw [compose_scaled_left, changeMap_scaled, compose_identity_left]

lemma scalarAut_commute (m : ℕ) (e : Aut E.curve)
    (he : e.hom ≫ E.projection = E.projection) (α : Lift E m e.hom) (c : Rˣ) :
    Commute (scalarAut E m c) (LinePair.toAut _ e α) := by
  change LinePair.toAut _ e α ≪≫ scalarAut E m c = scalarAut E m c ≪≫ LinePair.toAut _ e α
  rw [← toAut_scaled_right E m e he, ← toAut_scaled_left]

lemma scalarAut_injective (m : ℕ) : Function.Injective (scalarAut E m) := by
  intro c d h
  have hh := LinePair.toAut_injective _ (Iso.refl E.curve) h
  apply (scalar_bijective E).1
  apply Units.ext
  apply smulHom_injective (RelativeNormalizedThetaInversion.line_invertible E m)
  exact (cancel_epi (identityLift E m).hom).mp (congrArg Iso.hom hh)

lemma scalarAut_mul (m : ℕ) (c d : Rˣ) :
    scalarAut E m (c * d) = scalarAut E m c * scalarAut E m d := by
  rw [scalarAut, ← scaled_mul, toAut_scaled_right E m (Iso.refl _) (Category.id_comp _)]
  rfl

lemma scalarAut_one (m : ℕ) : scalarAut E m 1 = 1 := by
  have h : scaled E m 1 (identityLift E m) = identityLift E m := by
    apply Iso.ext
    simp [scaled, scalar, smulIso, smulHom_one]
  rw [scalarAut, h]
  have hu : (Scheme.Modules.pullbackCongr (rfl : (𝟙 E.curve) = 𝟙 E.curve)).app (thetaLine E m) ≪≫
      (Scheme.Modules.pullbackId E.curve).app (thetaLine E m) = identityLift E m := by
    apply Iso.ext
    simp [Scheme.Modules.pullbackCongr, Iso.app_hom, identityLift]
  have hh := LinePair.toAut_refl (thetaLine E m) (Iso.refl E.curve) rfl
  rw [hu] at hh
  exact hh

#print axioms scalarAut_commute
#print axioms scalarAut_mul
#print axioms scalarAut_one

def scalarAutHom (m : ℕ) : Rˣ →* Aut (LinePair.obj (thetaLine E m)) where
  toFun := scalarAut E m
  map_one' := scalarAut_one E m
  map_mul' := scalarAut_mul E m

lemma toAut_changeMap (m : ℕ) (e e' : E.curve ≅ E.curve) (h : e.hom = e'.hom)
    (α : Lift E m e'.hom) :
    LinePair.toAut _ e (changeMap E m h α) = LinePair.toAut _ e' α := by
  have he : e = e' := Iso.ext h
  subst e'
  congr 1

lemma aut_pow_succ_hom (e : Aut E.curve) (n : ℕ) :
    (e ^ (n+1)).hom = (e ^ n).hom ≫ e.hom := by
  rw [pow_succ', Aut.Aut_mul_def, Iso.trans_hom]

/-- Iterated lifts retain the actual pullback compositions and their coherence. -/
def powerLift (m : ℕ) (e : Aut E.curve) (α : Lift E m e.hom) :
    (n : ℕ) → Lift E m (e ^ n).hom
  | 0 => identityLift E m
  | n+1 => changeMap E m (aut_pow_succ_hom E e n)
      (compose E m _ _ (powerLift m e α n) α)

lemma toAut_powerLift (m : ℕ) (e : Aut E.curve) (α : Lift E m e.hom) (n : ℕ) :
    LinePair.toAut _ (e ^ n) (powerLift E m e α n) = (LinePair.toAut _ e α) ^ n := by
  induction n with
  | zero =>
    change LinePair.toAut _ (Iso.refl _) (identityLift E m) = 1
    have h := scalarAut_one E m
    have hu : scaled E m 1 (identityLift E m) = identityLift E m := by
      apply Iso.ext
      simp [scaled, scalar, smulIso, smulHom_one]
    simpa only [scalarAut, hu] using h
  | succ n ih =>
    change LinePair.toAut _ (e ^ (n+1))
      ((Scheme.Modules.pullbackCongr (aut_pow_succ_hom E e n)).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso α ≪≫ powerLift E m e α n) = _
    rw [LinePair.toAut_trans, ih, pow_succ', Aut.Aut_mul_def]

/-- A torsion base automorphism forces its lifted power to be structural scalar. -/
lemma power_is_scalar (m : ℕ) (e : Aut E.curve) (α : Lift E m e.hom)
    (n : ℕ) (hn : e ^ n = 1) :
    ∃ c : Rˣ, (LinePair.toAut _ e α) ^ n = scalarAut E m c := by
  have hh : (𝟙 E.curve) = (e ^ n).hom := (congrArg Iso.hom hn).symm
  let β := changeMap E m hh (powerLift E m e α n)
  obtain ⟨c, hc, _⟩ := existsUnique_scaled E m (𝟙 _) β (identityLift E m)
  refine ⟨c, ?_⟩
  rw [← toAut_powerLift]
  rw [← toAut_changeMap E m (Iso.refl _) (e ^ n) hh]
  exact congrArg (LinePair.toAut _ (Iso.refl _)) hc

lemma translate_mul (P Q : point E) :
    E.law.translate P ≫ E.law.translate Q = E.law.translate (E.law.mul (𝟙 _) P Q) := by
  let i : SchemeHomOver E.projection E.projection := GoodReductionJacobian.RelativeGroupLaw.idPoint
  let ca : SchemeHomOver E.projection E.projection :=
    ⟨E.projection ≫ P.val, by rw [Category.assoc, P.property, Category.comp_id]⟩
  let cb : SchemeHomOver E.projection E.projection :=
    ⟨E.projection ≫ Q.val, by rw [Category.assoc, Q.property, Category.comp_id]⟩
  change (E.law.mul E.projection i ca).val ≫ E.law.translate Q = _
  rw [point_translate, E.law.mul_assoc]
  change (E.law.mul E.projection i (E.law.mul E.projection ca cb)).val = _
  have h := E.law.mul_natural (𝟙 _) E.projection E.projection (Category.comp_id _) P Q
  have hc : E.law.mul E.projection ca cb =
      ⟨E.projection ≫ (E.law.mul (𝟙 _) P Q).val, by
        rw [Category.assoc, (E.law.mul (𝟙 _) P Q).property, Category.comp_id]⟩ := h.symm
  rw [hc]
  rfl

/-- Translation by an actual section, with its actual inverse section. -/
def rawTranslationIso (P : point E) : Aut E.curve where
  hom := E.law.translate P
  inv := E.law.translate (E.law.inv (𝟙 _) P)
  hom_inv_id := by rw [translate_mul, E.law.mul_inv_cancel, E.law.translate_one]
  inv_hom_id := by rw [translate_mul, E.law.inv_mul_cancel, E.law.translate_one]

lemma rawTranslationIso_pow (P : point E) (n : ℕ) :
    rawTranslationIso E P ^ n = rawTranslationIso E (E.law.nsmul (𝟙 _) n P) := by
  induction n with
  | zero =>
    apply Iso.ext
    exact (E.law.translate_one).symm
  | succ n ih =>
    apply Iso.ext
    rw [aut_pow_succ_hom, ih]
    change E.law.translate (E.law.nsmul (𝟙 _) n P) ≫ E.law.translate P = _
    rw [translate_mul, E.law.nsmul_succ]
    rfl

abbrev translationIso (P : point E) : Aut E.curve :=
  rawTranslationIso E (E.law.nsmul (𝟙 _) 2 P)

lemma translationIso_period (m : ℕ) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E) : translationIso E P ^ m = 1 := by
  rw [translationIso, rawTranslationIso_pow]
  have hh := RelativeDoubledTorsionThetaLiftR0255.doubled_killed E m P hP
  rw [RelativeDoubledTorsionThetaLiftR0255.killed_iff] at hh
  rw [hh]
  apply Iso.ext
  exact E.law.translate_one

lemma central_twist_power {G : Type*} [Group G] (A B C : G)
    (h : B * A = C * A * B) (hc : Commute C A) (n : ℕ) :
    B * A ^ n = C ^ n * (A ^ n * B) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := hc.pow_right n
    calc
      B * A ^ (n+1) = C ^ n * (A ^ n * (B * A)) := by
        rw [pow_succ, ← mul_assoc, ih]
        simp only [mul_assoc]
      _ = C ^ n * (A ^ n * (C * (A * B))) := by rw [h, mul_assoc]
      _ = C ^ (n+1) * (A ^ (n+1) * B) := by
        rw [← mul_assoc (A ^ n) C, ← hn.eq]
        simp only [pow_succ, mul_assoc]

lemma central_twist_period {G : Type*} [Group G] (A B C : G)
    (h : B * A = C * A * B) (hc : Commute C A) (n : ℕ) (hn : Commute (A ^ n) B) :
    C ^ n = 1 := by
  have hh := central_twist_power A B C h hc n
  rw [← hn.eq] at hh
  exact (mul_right_cancel (show C ^ n * (A ^ n * B) = 1 * (A ^ n * B) by
    rw [one_mul]; exact hh.symm))

#print axioms power_is_scalar
#print axioms translationIso_period
#print axioms central_twist_period

lemma toAut_compose (m : ℕ) (e f : Aut E.curve)
    (α : Lift E m e.hom) (β : Lift E m f.hom) :
    LinePair.toAut _ (e ≪≫ f) (compose E m e.hom f.hom α β) =
      LinePair.toAut _ e α ≪≫ LinePair.toAut _ f β := by
  have h := LinePair.toAut_trans (thetaLine E m) e f (e ≪≫ f) rfl α β
  have hh : changeMap E m (rfl : (e ≪≫ f).hom = e.hom ≫ f.hom)
      (compose E m e.hom f.hom α β) = compose E m e.hom f.hom α β := by
    apply Iso.ext_inv
    simp only [changeMap, Iso.trans_inv, Iso.app_inv, LinePair.congr_inv,
      eqToHom_refl, Category.comp_id]
  change LinePair.toAut _ (e ≪≫ f) (changeMap E m rfl (compose E m _ _ α β)) = _ at h
  rw [hh] at h
  exact h

lemma commutator_aut_relation (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) (c : Rˣ)
    (hc : Commutator E m P Q α β c) :
    LinePair.toAut _ (translationIso E Q) β * LinePair.toAut _ (translationIso E P) α =
      scalarAut E m c * LinePair.toAut _ (translationIso E P) α *
        LinePair.toAut _ (translationIso E Q) β := by
  obtain ⟨h, hc⟩ := hc
  let e := translationIso E P
  let f := translationIso E Q
  have he : (e ≪≫ f).hom ≫ E.projection = E.projection := by
    change (translation E P ≫ translation E Q) ≫ E.projection = E.projection
    rw [Category.assoc, RelativeDoubledTorsionThetaLiftR0255.translation_over,
      RelativeDoubledTorsionThetaLiftR0255.translation_over]
  have hh := congrArg (LinePair.toAut (thetaLine E m) (e ≪≫ f)) hc
  have h' : e.hom ≫ f.hom = f.hom ≫ e.hom := h
  change LinePair.toAut _ (e ≪≫ f) (compose E m e.hom f.hom α β) =
    LinePair.toAut _ (e ≪≫ f) (scaled E m c
      (changeMap E m h' (compose E m f.hom e.hom β α))) at hh
  rw [toAut_compose E m e f α β, toAut_scaled_right E m (e ≪≫ f) he,
    toAut_changeMap E m (e ≪≫ f) (f ≪≫ e) h', toAut_compose E m f e β α] at hh
  simpa only [Aut.Aut_mul_def, Iso.trans_assoc] using hh

/-- The commutator satisfies its global period equation over any base ring.
No reducedness or fibrewise equality is used. -/
lemma commutator_pow_eq_one (m n : ℕ) (P Q : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*n) = zero E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) (c : Rˣ)
    (hc : Commutator E m P Q α β c) : c ^ n = 1 := by
  let A := LinePair.toAut (thetaLine E m) (translationIso E P) α
  let B := LinePair.toAut (thetaLine E m) (translationIso E Q) β
  let C := scalarAut E m c
  have hrel : B * A = C * A * B := commutator_aut_relation E m P Q α β c hc
  have hCA : Commute C A := scalarAut_commute E m (translationIso E P)
    (RelativeDoubledTorsionThetaLiftR0255.translation_over E P) α c
  obtain ⟨d, hd⟩ := power_is_scalar E m (translationIso E P) α n
    (translationIso_period E n P hP)
  have hn : Commute (A ^ n) B := by
    change Commute ((LinePair.toAut _ (translationIso E P) α) ^ n) B
    rw [hd]
    exact scalarAut_commute E m (translationIso E Q)
      (RelativeDoubledTorsionThetaLiftR0255.translation_over E Q) β d
  have hCn := central_twist_period A B C hrel hCA n hn
  apply scalarAut_injective E m
  change (scalarAutHom E m) (c ^ n) = (scalarAutHom E m) 1
  rw [map_pow, map_one]
  exact hCn

lemma commutatorUnit_period (m : ℕ) (M : FamilyLevel R E (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y)) :
    commutatorUnit E m M.x M.y α β ^ m = 1 :=
  commutator_pow_eq_one E m m M.x M.y M.killed_x α β _
    (commutatorUnit_spec E m M.x M.y α β)

#print axioms commutator_aut_relation
#print axioms commutator_pow_eq_one
#print axioms commutatorUnit_period

/-- Geometric fibres suffice for the unit tests. The period equation is still
an equality in the original ring, not merely after passage to fields. -/
lemma primitiveUnit_iff_geometric_tests (m : ℕ) (c : Rˣ) :
    PrimitiveUnit m c ↔ c ^ m = 1 ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (f : R →+* k) (i : Fin m),
        i.val ≠ 0 → f (c : R) ^ i.val ≠ 1 := by
  rw [primitiveUnit_iff_field_tests]
  constructor
  · rintro ⟨hp, ht⟩
    exact ⟨hp, fun k _ _ f i hi => ht k f i hi⟩
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    intro k _ f i hi heq
    have h := ht (AlgebraicClosure k) ((algebraMap k (AlgebraicClosure k)).comp f) i hi
    apply h
    change algebraMap k (AlgebraicClosure k) (f (c : R)) ^ i.val = 1
    rw [← map_pow, heq, map_one]

/-- For the actual level basis, only the nontrivial geometric powers remain;
scalar existence, uniqueness and the global period have already been proved. -/
lemma primitive_commutator_iff_geometric_tests (m : ℕ) (M : FamilyLevel R E (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y)) :
    (∃! c : Rˣ, Commutator E m M.x M.y α β c ∧ PrimitiveUnit m c) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (f : R →+* k) (i : Fin m),
        i.val ≠ 0 → f (commutatorUnit E m M.x M.y α β : R) ^ i.val ≠ 1 := by
  constructor
  · rintro ⟨c, ⟨hc, hp⟩, _⟩
    rw [(commutator_iff E m M.x M.y α β c).mp hc] at hp
    exact ((primitiveUnit_iff_geometric_tests m _).mp hp).2
  · intro ht
    refine ⟨commutatorUnit E m M.x M.y α β,
      ⟨commutatorUnit_spec E m M.x M.y α β,
        (primitiveUnit_iff_geometric_tests m _).mpr
          ⟨commutatorUnit_period E m M α β, ht⟩⟩, ?_⟩
    intro d hd
    exact (commutator_iff E m M.x M.y α β d).mp hd.1

#print axioms primitiveUnit_iff_geometric_tests
#print axioms primitive_commutator_iff_geometric_tests

/-- The combination is made with the given scheme-valued group law. -/
def levelCombination {m : ℕ} (M : FamilyLevel R E m) (ij : Fin m × Fin m) : point E :=
  E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) ij.1.val M.x)
    (E.law.nsmul (𝟙 _) ij.2.val M.y)

def levelCombinationAt {T : Scheme.{u}} (t : T ⟶ base (R := R))
    {m : ℕ} (M : FamilyLevel R E m) (ij : Fin m × Fin m) :
    SchemeHomOver t E.projection :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (levelCombination E M ij)

/-- Full-level disjointness implies distinct combinations on every nonempty
scheme-valued fibre, without assuming a pairing or a chosen primitive root. -/
lemma levelCombinationAt_injective {T : Scheme.{u}} [Nonempty T]
    (t : T ⟶ base (R := R)) {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E m) :
    Function.Injective (levelCombinationAt E t M) := by
  intro a b hab
  by_contra hn
  have hne : a.1.val ≠ b.1.val ∨ a.2.val ≠ b.2.val := by
    by_contra h
    push_neg at h
    exact hn (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  have hd := coordinate_disjoint E hm M a.1.val a.2.val b.1.val b.2.val
    a.1.isLt a.2.isLt b.1.isLt b.2.isLt hne
  obtain ⟨x⟩ := ‹Nonempty T›
  have hh := congrArg (fun z : SchemeHomOver t E.projection => z.val x) hab
  exact (Set.disjoint_left.mp hd) ⟨t x, rfl⟩ ⟨t x, hh.symm⟩

/-- Translate the actual level grid by an arbitrary point of the test scheme. -/
def translatedCombination {T : Scheme.{u}} (t : T ⟶ base (R := R))
    (z : SchemeHomOver t E.projection) {m : ℕ} (M : FamilyLevel R E m)
    (ij : Fin m × Fin m) : SchemeHomOver t E.projection :=
  E.law.mul t z (levelCombinationAt E t M ij)

lemma translatedCombination_injective {T : Scheme.{u}} [Nonempty T]
    (t : T ⟶ base (R := R)) (z : SchemeHomOver t E.projection)
    {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E m) :
    Function.Injective (translatedCombination E t z M) := by
  intro a b hab
  apply levelCombinationAt_injective E t hm M
  letI := E.law.pointGroup t
  exact mul_left_cancel hab

def twoRowIndex {m : ℕ} (hm : 0 < m) (i : Fin m) (bj : Bool × Fin m) : Fin m × Fin m :=
  (if bj.1 then i else ⟨0, hm⟩, bj.2)

lemma twoRowIndex_injective {m : ℕ} (hm : 0 < m) (i : Fin m) (hi : i.val ≠ 0) :
    Function.Injective (twoRowIndex hm i) := by
  rintro ⟨a, j⟩ ⟨b, l⟩ h
  cases a <;> cases b <;> simp_all [twoRowIndex, Fin.ext_iff]

/-- Two rows of the doubled full-level grid remain disjoint after translation.
The first-coordinate offset is the actual nonzero index i, not a formal label. -/
def translatedTwoRows {T : Scheme.{u}} (t : T ⟶ base (R := R))
    (z : SchemeHomOver t E.projection) {m : ℕ} (hm : 0 < m)
    (M : FamilyLevel R E (2*m)) (i : Fin m) : Bool × Fin m → SchemeHomOver t E.projection :=
  translatedCombination E t z (doubledLevel E m M) ∘ twoRowIndex hm i

lemma translatedTwoRows_injective {T : Scheme.{u}} [Nonempty T]
    (t : T ⟶ base (R := R)) (z : SchemeHomOver t E.projection)
    {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E (2*m)) (i : Fin m) (hi : i.val ≠ 0) :
    Function.Injective (translatedTwoRows E t z hm M i) :=
  (translatedCombination_injective E t z hm (doubledLevel E m M)).comp
    (twoRowIndex_injective hm i hi)

/-- Any finite collection containing both actual translated rows has at least
2m elements. A degree-m zero divisor will contradict this bound. -/
lemma translatedTwoRows_card_le {T : Scheme.{u}} [Nonempty T]
    (t : T ⟶ base (R := R)) (z : SchemeHomOver t E.projection)
    {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E (2*m)) (i : Fin m) (hi : i.val ≠ 0)
    (F : Finset (SchemeHomOver t E.projection))
    (hF : ∀ bj, translatedTwoRows E t z hm M i bj ∈ F) : 2*m ≤ F.card := by
  classical
  have hsub : Finset.univ.image (translatedTwoRows E t z hm M i) ⊆ F := by
    intro x hx
    obtain ⟨bj, _, rfl⟩ := Finset.mem_image.mp hx
    exact hF bj
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (translatedTwoRows_injective E t z hm M i hi)] at hcard
  simpa using hcard

#print axioms levelCombinationAt_injective
#print axioms translatedTwoRows_injective
#print axioms translatedTwoRows_card_le
/-- Commuting operators on a nonzero finite-dimensional space over an
algebraically closed field have an actual common nonzero eigenvector. -/
lemma exists_common_eigenvector {k V : Type u} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (A B : Module.End k V) (hAB : Commute A B) :
    ∃ (a b : k) (v : V), v ≠ 0 ∧ A v = a • v ∧ B v = b • v := by
  obtain ⟨a, ha⟩ := A.exists_eigenvalue
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  let W := A.eigenspace a
  have hW : ∀ w ∈ W, B w ∈ W := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    calc
      A (B w) = B (A w) := congrArg (fun f : Module.End k V => f w) hAB.eq
      _ = a • B w := by rw [hw, map_smul]
  letI : Nontrivial W := ⟨⟨⟨v, hv.1⟩, 0, by
    intro h
    exact hv.2 (congrArg Subtype.val h)⟩⟩
  obtain ⟨b, hb⟩ := Module.End.exists_eigenvalue (B.restrict hW)
  obtain ⟨w, hw⟩ := hb.exists_hasEigenvector
  refine ⟨a, b, w.val, ?_, Module.End.mem_eigenspace_iff.mp w.property, ?_⟩
  · intro h
    exact hw.2 (Subtype.ext h)
  · exact congrArg Subtype.val hw.apply_eq_smul

/-- Injective operators have nonzero eigenvalues, so their common eigensection
is scaled by units. -/
lemma exists_common_unit_eigenvector {k V : Type u} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (A B : Module.End k V) (hAB : Commute A B)
    (hA : Function.Injective A) (hB : Function.Injective B) :
    ∃ (a b : kˣ) (v : V), v ≠ 0 ∧ A v = (a : k) • v ∧ B v = (b : k) • v := by
  obtain ⟨a, b, v, hv, ha, hb⟩ := exists_common_eigenvector A B hAB
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact hv (hA (ha.trans A.map_zero.symm))
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_smul] at hb
    exact hv (hB (hb.trans B.map_zero.symm))
  exact ⟨Units.mk0 a ha0, Units.mk0 b hb0, v, hv, ha, hb⟩

#print axioms exists_common_eigenvector
#print axioms exists_common_unit_eigenvector
namespace Sections
variable {X : Scheme.{u}}
def act (f : X ⟶ X) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (s : Γ(L, ⊤)) : Γ(L, ⊤) :=
  α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f s)

lemma act_comp (f g : X ⟶ X) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) (s : Γ(L, ⊤)) :
    act (f ≫ g) (((Scheme.Modules.pullbackComp f g).app L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ α) s = act f α (act g β s) := by
  let e := (Scheme.Modules.pullbackComp f g).app L
  have h := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection f g L ⊤ s
  have he : e.inv.app ⊤ (Scheme.Modules.pullbackLocalSection (f ≫ g) s) =
      Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s) := by
    have hh := congrArg (fun v => e.inv.app ⊤ v) h
    change e.inv.app ⊤ (e.hom.app ⊤ _) = _ at hh
    change (e.hom ≫ e.inv).app ⊤ _ = _ at hh
    rw [e.hom_inv_id] at hh
    exact hh.symm
  simp only [act, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [he, Scheme.Modules.pullbackLocalSection_app]
  rfl

lemma base_scalar_fixed (k : Type u) [CommRing k] (p : X ⟶ Spec (.of k))
    (f : X ⟶ X) (hf : f ≫ p = p) (a : k) :
    f.appTop (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) =
      p.appTop ((Scheme.ΓSpecIso (.of k)).inv a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf]

def actLinear (k : Type u) [CommRing k] (p : X ⟶ Spec (.of k))
    (f : X ⟶ X) (hf : f ≫ p = p) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module k Γ(L, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
    Module.End k Γ(L, ⊤) := by
  letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module k Γ(L, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
  refine { toFun := act f α, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    simp only [act, Scheme.Modules.pullbackLocalSection_add, map_add]
  · intro a s
    change α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f
      ((((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) a) • s)) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) a) • act f α s
    rw [Scheme.Modules.pullbackLocalSection_smul]
    have h := base_scalar_fixed k p f hf a
    change f.app ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) a) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) a at h
    rw [h, Scheme.Modules.Hom.app_smul]
    rfl
lemma act_bijective (f : X ⟶ X) [IsIso f] {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L) : Function.Bijective (act f α) := by
  let e := CategoryTheory.Equivalence.mk (Scheme.Modules.pullback f) (Scheme.Modules.pullback (inv f))
    ((Scheme.Modules.pullbackComp (inv f) f ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp f (inv f) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f) ≪≫ Scheme.Modules.pullbackId X)
  letI : (Scheme.Modules.pullback f).IsEquivalence := e.isEquivalence_functor
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) := inferInstance
  haveI : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app ⊤) := inferInstance
  haveI : IsIso (α.hom.app ⊤) := inferInstance
  exact (ConcreteCategory.bijective_of_isIso (α.hom.app ⊤)).comp
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app ⊤))

lemma act_changeMap {f g : X ⟶ X} (h : f = g) {L : X.Modules}
    (α : (Scheme.Modules.pullback g).obj L ≅ L) (s : Γ(L, ⊤)) :
    act f ((Scheme.Modules.pullbackCongr h).app L ≪≫ α) s = act g α s := by
  subst g
  rfl

#print axioms act_comp
#print axioms actLinear
end Sections

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
lemma sectionAct_scaled (m : ℕ) {f : E.curve ⟶ E.curve}
    (α : Lift E m f) (c : Rˣ) (s : Γ(thetaLine E m, ⊤)) :
    Sections.act f (scaled E m c α) s = (scalar E c : Γ(E.curve, ⊤)) • Sections.act f α s := by
  change resTop (scalar E c : Γ(E.curve, ⊤)) ⊤ • Sections.act f α s = _
  congr 1
  exact congrArg (fun g : Γ(E.curve, ⊤) → Γ(E.curve, ⊤) => g (scalar E c))
    (show (fun x => resTop x ⊤) = id by funext x; simp [resTop])

lemma sectionAct_commutator (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Rˣ) (hc : Commutator E m P Q α β c) (s : Γ(thetaLine E m, ⊤)) :
    Sections.act (translation E P) α (Sections.act (translation E Q) β s) =
      (scalar E c : Γ(E.curve, ⊤)) •
        Sections.act (translation E Q) β (Sections.act (translation E P) α s) := by
  obtain ⟨h, hc⟩ := hc
  rw [← Sections.act_comp, ← Sections.act_comp]
  change Sections.act _ (compose E m _ _ α β) s =
    (scalar E c : Γ(E.curve, ⊤)) • Sections.act _ (compose E m _ _ β α) s
  rw [hc, sectionAct_scaled]
  congr 1
  exact Sections.act_changeMap h _ s

#print axioms Sections.act_bijective
#print axioms sectionAct_commutator
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

def fieldFrame {k : Type u} [Field k] (E : EllipticFamily k) : FramedCurve k := by
  letI := E.proper
  letI := E.smooth
  letI := E.connected
  let e := (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    k (RelativeNormalizedThetaInversion.hodge E) (RelativeNormalizedThetaInversion.hodge_invertible E)).some
  exact {
    target := E.curve
    structureMap := E.projection
    law := E.law
    geometry := { smooth := inferInstance, proper := E.proper
                  connectedFibres := E.projection.isConnected_preimage_singleton
                  hasGroupLaw := ⟨E.law⟩ }
    dimension := E.smooth
    hodge := ⟨e.symm⟩ }

/-- The Hodge factor is removed by an actual field-valued line isomorphism. -/
def fieldLineIso {k : Type u} [Field k] (E : EllipticFamily k) (m : ℕ) :
    thetaLine E m ≅ ((zero E).ker ^ m).invModule := by
  let H := (RelativeNormalizedThetaInversion.hodge E).tensorPow m
  let e := (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    k H ((RelativeNormalizedThetaInversion.hodge_invertible E).tensorPow m)).some
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback E.projection).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso E.projection)) ≪≫ ρ_ _

/-- A line isomorphism acts linearly for the specified structural map. -/
def sectionsIso {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) {L M : X.Modules} (e : L ≅ M) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p M ⊤
    Γ(L, ⊤) ≃ₗ[k] Γ(M, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p M ⊤
  exact {
    toFun := e.hom.app ⊤
    invFun := e.inv.app ⊤
    left_inv := by
      intro x
      change (e.hom ≫ e.inv).app ⊤ x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := by
      intro x
      change (e.inv ≫ e.hom).app ⊤ x = x
      rw [e.inv_hom_id]
      rfl
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => Scheme.Modules.Hom.app_smul e.hom _ x }

lemma field_sections_finite {k : Type u} [Field k] [Algebra ℚ k]
    (E : EllipticFamily k) (m : ℕ) (hm : 0 < m) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
    Module.Finite k Γ(thetaLine E m, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
  let Q := fieldFrame E
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (((zero E).ker ^ m).invModule) ⊤
  letI : Module.Finite k Γ(((zero E).ker ^ m).invModule, ⊤) :=
    (ArithmeticThetaLocalWeierstrassR0203.NoetherianPositiveCohomology.positive_sections_baseChange
      k Q m hm).1.1
  exact Module.Finite.equiv (sectionsIso E.projection (fieldLineIso E m)).symm

lemma field_sections_finrank {k : Type u} [Field k] [IsAlgClosed k] [Algebra ℚ k]
    (E : EllipticFamily k) (m : ℕ) (hm : 0 < m) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
    Module.finrank k Γ(thetaLine E m, ⊤) = m := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
  let N := ((zero E).ker ^ m).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection N ⊤
  have hr := ArithmeticThetaLocalWeierstrassR0203.NoetherianPositiveCohomology.positive_sections_geometric_rank
    k (fieldFrame E) m hm k
  exact (sectionsIso E.projection (fieldLineIso E m)).finrank_eq.trans
    ((TensorProduct.lid k Γ(N, ⊤)).finrank_eq.symm.trans hr)

#print axioms field_sections_finrank
#print axioms fieldLineIso
#print axioms sectionsIso
#print axioms field_sections_finite
#print axioms fieldFrame

universe v
lemma linear_twist_pow {k : Type u} [CommRing k] {V : Type v}
    [AddCommGroup V] [Module k V] (A B : Module.End k V) (c : k)
    (h : A * B = c • (B * A)) (n : ℕ) : A ^ n * B = c ^ n • (B * A ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h, smul_mul_assoc,
      smul_smul, ← pow_succ, mul_assoc, ← pow_succ']

lemma linear_twist_pow_commute {k : Type u} [CommRing k] {V : Type v}
    [AddCommGroup V] [Module k V] (A B : Module.End k V) (c : k)
    (h : A * B = c • (B * A)) (n : ℕ) (hn : c ^ n = 1) : Commute (A ^ n) B := by
  show A ^ n * B = B * A ^ n
  rw [linear_twist_pow A B c h, hn, one_smul]
#print axioms linear_twist_pow
#print axioms linear_twist_pow_commute
def thetaAct {k : Type u} [CommRing k] (E : EllipticFamily k) (m : ℕ)
    (P : point E) (α : Lift E m (translation E P)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
    Module.End k Γ(thetaLine E m, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
  refine { toFun := Sections.act _ α, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    simp only [Sections.act, Scheme.Modules.pullbackLocalSection_add, map_add]
  · intro a s
    change α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection (translation E P)
      ((E.projection.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv a)) • s)) =
      (E.projection.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv a)) • Sections.act _ α s
    have htop : E.projection.appLE ⊤ ⊤ le_top = E.projection.appTop := by
      simp [Scheme.Hom.appLE]
    rw [htop]
    letI : Algebra k Γ(E.curve, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ E.projection.appTop).hom.toAlgebra
    letI : Module k Γ(thetaLine E m, ⊤) := Module.compHom _ (algebraMap k Γ(E.curve, ⊤))
    exact (Sections.actLinear k E.projection (translation E P)
      (RelativeDoubledTorsionThetaLiftR0255.translation_over E P) α).map_smul a s


lemma thetaAct_relation {k : Type u} [CommRing k] (E : EllipticFamily k) (m : ℕ)
    (P Q : point E) (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : kˣ) (hc : Commutator E m P Q α β c) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
    thetaAct E m P α * thetaAct E m Q β = (c : k) • (thetaAct E m Q β * thetaAct E m P α) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
  ext s
  change Sections.act _ α (Sections.act _ β s) =
    (E.projection.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv (c : k))) •
      Sections.act _ β (Sections.act _ α s)
  have htop : E.projection.appLE ⊤ ⊤ le_top = E.projection.appTop := by
    simp [Scheme.Hom.appLE]
  rw [htop]
  exact sectionAct_commutator E m P Q α β c hc s

/-- A lower commutator period supplies a common nonzero eigensection of the
actual theta line; no representation or section space is supplied as data. -/
lemma exists_theta_eigensection {k : Type u} [Field k] [IsAlgClosed k] [Algebra ℚ k]
    (E : EllipticFamily k) (m : ℕ) (hm : 0 < m) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : kˣ) (hc : Commutator E m P Q α β c) (i : ℕ) (hi : (c : k) ^ i = 1) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
    ∃ (a b : kˣ) (s : Γ(thetaLine E m, ⊤)), s ≠ 0 ∧
      (thetaAct E m P α ^ i) s = (a : k) • s ∧ thetaAct E m Q β s = (b : k) • s := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤
  letI := field_sections_finite E m hm
  letI : Nontrivial Γ(thetaLine E m, ⊤) := Module.finrank_pos_iff.mp
    (by rw [field_sections_finrank E m hm]; exact hm)
  letI : IsIso (translation E P) := (translationIso E P).isIso_hom
  letI : IsIso (translation E Q) := (translationIso E Q).isIso_hom
  have hA : Function.Injective (thetaAct E m P α) := (Sections.act_bijective _ α).1
  have hB : Function.Injective (thetaAct E m Q β) := (Sections.act_bijective _ β).1
  have hAi : Function.Injective (thetaAct E m P α ^ i) := by
    rw [Module.End.coe_pow]
    exact hA.iterate i
  exact exists_common_unit_eigenvector _ _
    (linear_twist_pow_commute _ _ (c : k) (thetaAct_relation E m P Q α β c hc) i hi) hAi hB
#print axioms thetaAct_relation
#print axioms exists_theta_eigensection

lemma field_line_cohomology {k : Type u} [Field k] [Algebra ℚ k]
    (E : EllipticFamily k) (m : ℕ) (hm : 0 < m) (L : E.curve.Modules)
    (eL : L ≅ ((zero E).ker ^ m).invModule) (𝒱 : E.curve.TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf E.projection L).H1 ∧
      Module.finrank k (𝒱.sectionsOf E.projection L).H0 = m := by
  let p := E.projection
  let N := ((zero E).ker ^ m).invModule
  let φ : pullback p (𝟙 _) ≅ E.curve := asIso (pullback.fst p (𝟙 _))
  have hφ : φ.hom ≫ p = pullback.snd p (𝟙 _) := by
    change pullback.fst p (𝟙 _) ≫ p = pullback.snd p (𝟙 _)
    simpa only [Category.comp_id] using pullback.condition (f := p) (g := 𝟙 _)
  obtain ⟨𝒲, _, _, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd p (𝟙 _)) p φ hφ 𝒱 L
      ((Scheme.Modules.pullback (pullback.fst p (𝟙 _))).obj N)
      ((Scheme.Modules.pullback (pullback.fst p (𝟙 _))).mapIso eL.symm)
  have h := ArithmeticThetaLocalWeierstrassR0203.NoetherianPositiveCohomology.origin_fibre_positive_cohomology
    k (fieldFrame E) m hm k (𝟙 _) 𝒲
  letI : Subsingleton (𝒲.sectionsOf (pullback.snd p (𝟙 _))
    ((Scheme.Modules.pullback (pullback.fst p (𝟙 _))).obj N)).H1 := h.1
  exact ⟨e1.symm.toEquiv.subsingleton, e0.finrank_eq.symm.trans h.2⟩

lemma field_theta_cohomology {k : Type u} [Field k] [Algebra ℚ k]
    (E : EllipticFamily k) (m : ℕ) (hm : 0 < m) (𝒱 : E.curve.TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf E.projection (thetaLine E m)).H1 ∧
      Module.finrank k (𝒱.sectionsOf E.projection (thetaLine E m)).H0 = m :=
  field_line_cohomology E m hm _ (fieldLineIso E m) 𝒱

lemma field_unit_cohomology {k : Type u} [Field k] [IsAlgClosed k]
    (E : EllipticFamily k) (𝒱 : E.curve.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf E.projection (𝟙_ E.curve.Modules)).H1 = 1 ∧
      Module.finrank k (𝒱.sectionsOf E.projection (𝟙_ E.curve.Modules)).H0 = 1 := by
  letI := E.proper
  letI := E.smooth
  letI : GeometricallyIntegral E.projection := (fieldFrame E).geometry.geometricallyIntegral_of_commRing
  letI : IsIntegral E.curve := GeometricallyIntegral.isIntegral_of_subsingleton E.projection
  exact 𝒱.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one k E.projection 1
    (FibreCohomology.group_curveModel_genus E.projection E.law)

#print axioms field_theta_cohomology
#print axioms field_unit_cohomology

/-- The actual fibre product carries the base change of the given group law. -/
def baseChangedFamily {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R)) : EllipticFamily A := by
  letI := E.proper
  letI := E.smooth
  letI := E.connected
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact {
    curve := pullback E.projection x
    projection := pullback.snd E.projection x
    law := E.law.baseChange x
    commutative := GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange x E.commutative
    proper := inferInstance
    smooth := MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    connected := inferInstance }

#print axioms baseChangedFamily

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

lemma baseChanged_zero {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R)) :
    zero (baseChangedFamily E x) ≫ pullback.fst E.projection x = x ≫ zero E := by
  change (pullback.lift _ _ _) ≫ pullback.fst E.projection x = _
  rw [pullback.lift_fst]
  have h := E.law.one_natural (𝟙 _) ((𝟙 (Spec (.of A))) ≫ x) x (by simp)
  exact (congrArg Subtype.val h).symm

lemma baseChanged_zero_ideal {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R)) :
    (zero E).ker.comap (pullback.fst E.projection x) = (zero (baseChangedFamily E x)).ker := by
  exact ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.ideal_comap
    (RelativeNormalizedThetaInversion.relativeFamily E)
    (RelativeNormalizedThetaInversion.relativeFamily (baseChangedFamily E x))
    x (pullback.fst E.projection x) (IsPullback.of_hasPullback E.projection x) (baseChanged_zero E x)

def baseChanged_originPowerIso {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R)) (m : ℕ) :
    (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (((zero E).ker ^ m).invModule) ≅
      ((zero (baseChangedFamily E x)).ker ^ m).invModule := by
  let π := pullback.fst E.projection x
  let e := idealPullbackIso π ((zero E).ker ^ m) ((zero (baseChangedFamily E x)).ker ^ m)
    ((RelativeNormalizedThetaInversion.zero_cartier E).pow m)
    ((RelativeNormalizedThetaInversion.zero_cartier (baseChangedFamily E x)).pow m)
    (by rw [comap_power, baseChanged_zero_ideal])
  letI := dualComparison_isIso π ((zero E).ker ^ m).module
    ((RelativeNormalizedThetaInversion.zero_cartier E).pow m).isInvertible_module
  exact asIso (dualComparison π _) ≪≫
    ((MonoidalClosed.internalHom (C := (baseChangedFamily E x).curve.Modules)).mapIso e.symm.op).app
      (𝟙_ (baseChangedFamily E x).curve.Modules)

/-- The original line restricted to a field fibre is compared to the actual
origin ideal on that fibre. The base Hodge factor is transported and trivialized. -/
def fibreLineIso {R k : Type u} [CommRing R] [Field k] (E : EllipticFamily R)
    (x : Spec (.of k) ⟶ Spec (.of R)) (m : ℕ) :
    (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m) ≅
      ((zero (baseChangedFamily E x)).ker ^ m).invModule := by
  let π := pullback.fst E.projection x
  let p := pullback.snd E.projection x
  let H := (RelativeNormalizedThetaInversion.hodge E).tensorPow m
  let eH := (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    k ((Scheme.Modules.pullback x).obj H)
    (((RelativeNormalizedThetaInversion.hodge_invertible E).tensorPow m).pullback x)).some
  let e : (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback E.projection).obj H) ≅
      𝟙_ (baseChangedFamily E x).curve.Modules :=
    (Scheme.Modules.pullbackComp π E.projection).app H ≪≫
      (Scheme.Modules.pullbackCongr (pullback.condition (f := E.projection) (g := x))).app H ≪≫
      ((Scheme.Modules.pullbackComp p x).app H).symm ≪≫
      (Scheme.Modules.pullback p).mapIso eH ≪≫ Scheme.Modules.pullbackTensorUnitObjIso p
  exact Scheme.Modules.pullbackTensorObjIso π _ _ ≪≫
    (baseChanged_originPowerIso E x m ⊗ᵢ e) ≪≫ ρ_ _

#print axioms baseChanged_zero_ideal
#print axioms baseChanged_originPowerIso
#print axioms fibreLineIso
/-- Every nonzero section of the original theta line on an actual geometric
fibre has an effective zero divisor of exactly degree m. -/
lemma fibre_zero_divisor {R k : Type u} [CommRing R] [Field k] [IsAlgClosed k] [Algebra ℚ k]
    (E : EllipticFamily R) (x : Spec (.of k) ⟶ Spec (.of R)) (m : ℕ) (hm : 0 < m)
    (s : 𝟙_ (pullback E.projection x).Modules ⟶
      (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m))
    (hs : s ≠ 0) :
    ∃ D : RelEffCartierDiv E.projection m x,
      D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m) ≅ D.lineBundle,
        s ≫ e.hom = D.I.invModuleSection := by
  let F := baseChangedFamily E x
  let L := (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)
  letI : IsProper (pullback.snd E.projection x) := F.proper
  letI : SmoothOfRelativeDimension 1 (pullback.snd E.projection x) := F.smooth
  letI : GeometricallyIntegral (pullback.snd E.projection x) :=
    (fieldFrame F).geometry.geometricallyIntegral_of_commRing
  obtain ⟨𝒱, _⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed k
    (pullback.snd E.projection x) ((zero F) (IsLocalRing.closedPoint k))
  have hp := field_line_cohomology F m hm L (fibreLineIso E x m) 𝒱
  have hu := field_unit_cohomology F 𝒱
  letI : Subsingleton (𝒱.sectionsOf F.projection L).H1 := hp.1
  apply RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre x
    ((RelativeNormalizedThetaInversion.line_invertible E m).pullback _) s hs 𝒱 m
  change (Module.finrank k (𝒱.sectionsOf F.projection L).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf F.projection L).H1 =
    (Module.finrank k (𝒱.sectionsOf F.projection (𝟙_ F.curve.Modules)).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf F.projection (𝟙_ F.curve.Modules)).H1 + m
  rw [hp.2, hu.1, hu.2, Module.finrank_zero_of_subsingleton]
  simp

#print axioms fibre_zero_divisor

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

lemma pullbackSection_top {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (σ : 𝟙_ Y.Modules ⟶ L) :
    (Scheme.Modules.pullbackSection f σ).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      Scheme.Modules.pullbackLocalSection f (σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  let e := Scheme.Modules.pullbackUnitIso f
  have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2 f ⊤ 1
  simp only [map_one] at h
  have hi : e.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      Scheme.Modules.pullbackLocalSection f (Scheme.Modules.toUnitSection ⊤ 1) := by
    have hh := congrArg (fun v => e.inv.app ⊤ v) h
    change (e.hom ≫ e.inv).app ⊤ _ = _ at hh
    rw [e.hom_inv_id] at hh
    exact hh.symm
  change ((Scheme.Modules.pullback f).map σ).app ⊤
    (e.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) = _
  rw [hi]
  exact (Scheme.Modules.pullbackLocalSection_app f σ (Scheme.Modules.toUnitSection ⊤ 1)).symm

/-- A unit eigensection has an invariant actual zero ideal under the lifted map. -/
lemma eigen_zero_ideal_invariant {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (σ : 𝟙_ X.Modules ⟶ L)
    (u : Γ(X, ⊤)) (hu : IsUnit u)
    (hσ : Sections.act f α (σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) =
      u • σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    (Scheme.Modules.zeroSchemeIdeal σ).comap f = Scheme.Modules.zeroSchemeIdeal σ := by
  rw [hL.comap_zeroSchemeIdeal_monoidalV2]
  rw [← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2
    (Scheme.Modules.pullbackSection f σ) α.hom]
  apply (hL.zeroSchemeIdeal_eq_of_app_eq_smul σ _ u hu ?_).symm
  change α.hom.app ⊤ ((Scheme.Modules.pullbackSection f σ).app ⊤
    (Scheme.Modules.toUnitSection ⊤ 1)) = _
  rw [pullbackSection_top]
  exact hσ

lemma eigen_zero_support_invariant {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (σ : 𝟙_ X.Modules ⟶ L)
    (u : Γ(X, ⊤)) (hu : IsUnit u)
    (hσ : Sections.act f α (σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) =
      u • σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    f.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal σ).support : Set X) =
      ((Scheme.Modules.zeroSchemeIdeal σ).support : Set X) := by
  have h := congrArg (fun I : X.IdealSheafData => (I.support : Set X))
    (eigen_zero_ideal_invariant hL f α σ u hu hσ)
  simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] using h
#print axioms pullbackSection_top
#print axioms eigen_zero_ideal_invariant
#print axioms eigen_zero_support_invariant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
variable {R k : Type u} [CommRing R] [Field k] [IsAlgClosed k] (E : EllipticFamily R)
    (x : Spec (.of k) ⟶ Spec (.of R))

def fibrePoint (z : SchemeHomOver x E.projection) :
    SchemeHomOver (𝟙 (Spec (.of k))) (pullback.snd E.projection x) :=
  ⟨pullback.lift z.val (𝟙 _) (by simpa using z.property), pullback.lift_snd _ _ _⟩

def fibrePointAt (z : SchemeHomOver x E.projection) : (pullback E.projection x : Scheme.{u}) :=
  (fibrePoint E x z).val (IsLocalRing.closedPoint k)

lemma fibrePointAt_injective : Function.Injective (fibrePointAt E x) := by
  letI : IsProper (pullback.snd E.projection x) := (baseChangedFamily E x).proper
  intro z w h
  have hh : (fibrePoint E x z).val = (fibrePoint E x w).val :=
    ext_of_apply_closedPoint_eq (pullback.snd E.projection x)
      (fibrePoint E x z).property (fibrePoint E x w).property h
  apply Subtype.ext
  have he := congrArg (fun g => g ≫ pullback.fst E.projection x) hh
  simpa only [fibrePoint, pullback.lift_fst] using he

/-- Counting is on the actual geometric fibre, not on the original curve's
topological points. -/
lemma fibre_two_rows_card {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E (2*m))
    (i : Fin m) (hi : i.val ≠ 0) (z : SchemeHomOver x E.projection) :
    letI := Classical.decEq (pullback E.projection x : Scheme.{u})
    let F := Finset.univ.image (fibrePointAt E x ∘ translatedTwoRows E x z hm M i)
    F.card = 2*m := by
  classical
  have hinj := (fibrePointAt_injective E x).comp (translatedTwoRows_injective E x z hm M i hi)
  dsimp only
  rw [Finset.card_image_of_injective _ hinj]
  simp

lemma fibre_two_rows_not_subset_zero_divisor {m : ℕ} (hm : 0 < m)
    (M : FamilyLevel R E (2*m)) (i : Fin m) (hi : i.val ≠ 0)
    (z : SchemeHomOver x E.projection) (D : RelEffCartierDiv E.projection m x) :
    ¬ ∀ bj, fibrePointAt E x (translatedTwoRows E x z hm M i bj) ∈ D.I.support := by
  classical
  intro h
  let F := Finset.univ.image (fibrePointAt E x ∘ translatedTwoRows E x z hm M i)
  have hb : F.card ≤ m := D.card_le_of_subset_support F (by
    intro y hy
    obtain ⟨bj, _, rfl⟩ := Finset.mem_image.mp hy
    exact h bj)
  have hc : F.card = 2*m := fibre_two_rows_card E x hm M i hi z
  omega
#print axioms fibrePointAt_injective
#print axioms fibre_two_rows_not_subset_zero_divisor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255

lemma divisor_exists_fibre_point {R k : Type u} [CommRing R] [Field k] [IsAlgClosed k]
    (E : EllipticFamily R) (x : Spec (.of k) ⟶ Spec (.of R)) {m : ℕ} (hm : 0 < m)
    (D : RelEffCartierDiv E.projection m x) :
    ∃ z : SchemeHomOver x E.projection, fibrePointAt E x z ∈ D.I.support := by
  let q := D.I.subschemeι ≫ pullback.snd E.projection x
  letI : IsFinite q := D.isFinite
  letI : Flat q := D.flat
  letI : LocallyOfFinitePresentation q := D.locallyOfFinitePresentation
  letI : Surjective q := q.one_le_finrank_iff_surjective.mp (by
    intro t
    change 1 ≤ (D.I.subschemeι ≫ pullback.snd E.projection x).finrank t
    rw [D.finrank_eq]
    omega)
  obtain ⟨v, _⟩ := q.surjective (IsLocalRing.closedPoint k)
  letI : Nonempty D.I.subscheme := ⟨v⟩
  letI : JacobsonSpace D.I.subscheme := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨w, _, hw⟩ := nonempty_inter_closedPoints
    (X := D.I.subscheme) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let p := pointOfClosedPoint q w hw
  have hp : p ≫ q = 𝟙 _ := pointOfClosedPoint_comp q w hw
  let z : SchemeHomOver x E.projection :=
    ⟨p ≫ D.I.subschemeι ≫ pullback.fst E.projection x, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc]
      change (p ≫ q) ≫ x = x
      rw [hp, Category.id_comp]⟩
  refine ⟨z, ?_⟩
  have hz : (fibrePoint E x z).val = p ≫ D.I.subschemeι := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd E.projection x = _
      rw [pullback.lift_snd]
      exact hp.symm
  change (fibrePoint E x z).val (IsLocalRing.closedPoint k) ∈ D.I.support
  rw [hz]
  have hmem : D.I.subschemeι (p (IsLocalRing.closedPoint k)) ∈ Set.range D.I.subschemeι :=
    ⟨p (IsLocalRing.closedPoint k), rfl⟩
  rw [D.I.range_subschemeι] at hmem
  exact hmem
#print axioms divisor_exists_fibre_point

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
namespace Sections
variable {X : Scheme.{u}} {L : X.Modules}

def sectionHom (s : Γ(L, ⊤)) : 𝟙_ X.Modules ⟶ L := fromSection L s

lemma fromSection_top (s : Γ(L, ⊤)) :
    (sectionHom s).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = s := by
  change (fromSection L s).app ⊤ (1 : Γ(X, ⊤)) = s
  rw [fromSection_apply, one_smul]
  change L.presheaf.map (𝟙 _) s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma fromSection_ne_zero (s : Γ(L, ⊤)) (hs : s ≠ 0) : sectionHom s ≠ 0 := by
  intro h
  have hh := congrArg (fun σ : 𝟙_ X.Modules ⟶ L =>
    σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) h
  rw [fromSection_top] at hh
  exact hs hh

def zeroSupport (s : Γ(L, ⊤)) : Set X := (Scheme.Modules.zeroSchemeIdeal (sectionHom s)).support

lemma zeroIdeal_act (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (s : Γ(L, ⊤)) :
    Scheme.Modules.zeroSchemeIdeal (sectionHom (act f α s)) =
      (Scheme.Modules.zeroSchemeIdeal (sectionHom s)).comap f := by
  have h := hL.zeroSchemeIdeal_eq_of_app_eq_smul
    (sectionHom (act f α s)) (Scheme.Modules.pullbackSection f (sectionHom s) ≫ α.hom)
    1 isUnit_one (by
      change α.hom.app ⊤ ((Scheme.Modules.pullbackSection f (sectionHom s)).app ⊤
        (Scheme.Modules.toUnitSection ⊤ 1)) = _
      rw [pullbackSection_top, fromSection_top, fromSection_top, one_smul]
      rfl)
  rw [h, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2,
    ← hL.comap_zeroSchemeIdeal_monoidalV2]

lemma zeroSupport_act (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (s : Γ(L, ⊤)) :
    zeroSupport (act f α s) = f.base ⁻¹' zeroSupport s := by
  change ((Scheme.Modules.zeroSchemeIdeal (sectionHom (act f α s))).support : Set X) = _
  rw [zeroIdeal_act hL f α s, Scheme.IdealSheafData.support_comap]
  rfl

lemma zeroSupport_iterate (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (n : ℕ) (s : Γ(L, ⊤)) :
    zeroSupport ((act f α)^[n] s) = (f.base^[n]) ⁻¹' zeroSupport s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', zeroSupport_act hL f α, ih]
    ext z
    simp only [Set.mem_preimage, Function.iterate_succ_apply]

lemma zeroSupport_smul (hL : Scheme.Modules.IsInvertible L) (u : Γ(X, ⊤))
    (hu : IsUnit u) (s : Γ(L, ⊤)) : zeroSupport (u • s) = zeroSupport s := by
  have h := hL.zeroSchemeIdeal_eq_of_app_eq_smul (sectionHom s) (sectionHom (u • s)) u hu
    (by rw [fromSection_top, fromSection_top])
  exact congrArg (fun I : X.IdealSheafData => (I.support : Set X)) h.symm

lemma eigen_zeroSupport_iterate (hL : Scheme.Modules.IsInvertible L) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (n : ℕ) (s : Γ(L, ⊤))
    (u : Γ(X, ⊤)) (hu : IsUnit u) (hs : (act f α)^[n] s = u • s) :
    (f.base^[n]) ⁻¹' zeroSupport s = zeroSupport s := by
  rw [← zeroSupport_iterate hL f α n s, hs, zeroSupport_smul hL u hu]
#print axioms fromSection_ne_zero
#print axioms zeroSupport_iterate
#print axioms eigen_zeroSupport_iterate
end Sections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
variable {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R))

def fibreEnd (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection) :
    pullback E.projection x ⟶ pullback E.projection x :=
  pullback.map E.projection x E.projection x f (𝟙 _) (𝟙 _)
    (by simpa using hf.symm) (by simp)

lemma fibreEnd_fst (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection) :
    fibreEnd E x f hf ≫ pullback.fst E.projection x = pullback.fst E.projection x ≫ f := by
  simp [fibreEnd]

lemma fibreEnd_snd (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection) :
    fibreEnd E x f hf ≫ pullback.snd E.projection x = pullback.snd E.projection x := by
  simp [fibreEnd]

lemma fibreEnd_id : fibreEnd E x (𝟙 _) (Category.id_comp _) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [fibreEnd]

lemma fibreEnd_comp (f g : E.curve ⟶ E.curve)
    (hf : f ≫ E.projection = E.projection) (hg : g ≫ E.projection = E.projection)
    (hfg : (f ≫ g) ≫ E.projection = E.projection) :
    fibreEnd E x (f ≫ g) hfg = fibreEnd E x f hf ≫ fibreEnd E x g hg := by
  apply pullback.hom_ext <;> simp [Category.assoc, fibreEnd]

lemma fibreEnd_isIso (f : E.curve ⟶ E.curve) [IsIso f]
    (hf : f ≫ E.projection = E.projection) : IsIso (fibreEnd E x f hf) := by
  unfold fibreEnd
  infer_instance

lemma fibrePoint_end {k : Type u} [Field k]
    (y : Spec (.of k) ⟶ Spec (.of R)) (z : SchemeHomOver y E.projection)
    (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection) :
    (fibrePoint E y (show SchemeHomOver y E.projection from
      ⟨z.val ≫ f, by rw [Category.assoc, hf, z.property]⟩)).val =
      (fibrePoint E y z).val ≫ fibreEnd E y f hf := by
  apply pullback.hom_ext <;> simp [fibrePoint, fibreEnd, Category.assoc]

#print axioms fibreEnd_comp
#print axioms fibreEnd_isIso
#print axioms fibrePoint_end

namespace PullbackLifts
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
variable {X Y : Scheme.{u}}

lemma iso_paste {C : Type*} [Category C] {A B C' D E : C}
    (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D) (d : A ≅ E) (e : E ≅ D)
    (h : b.inv ≫ a.inv ≫ d.hom = c.hom ≫ e.inv) :
    a ≪≫ b ≪≫ c = d ≪≫ e := by
  apply Iso.ext_inv
  apply (cancel_epi c.hom).mp
  apply (cancel_mono d.hom).mp
  simpa only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h

def squareNat (c : Y ⟶ X) (f : X ⟶ X) (f' : Y ⟶ Y) (h : c ≫ f = f' ≫ c) :
    Scheme.Modules.pullback c ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback c :=
  (Scheme.Modules.pullbackComp c f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp f' c).symm).symm

lemma pullbackCongr_refl {U V : Scheme.{u}} (f : U ⟶ V) :
    Scheme.Modules.pullbackCongr (rfl : f = f) = Iso.refl (Scheme.Modules.pullback f) := rfl

lemma square_paste (c : Y ⟶ X) (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (hfg : c ≫ (f ≫ g) = (f' ≫ g') ≫ c) (L : X.Modules) :
    (Scheme.Modules.pullback f').mapIso ((squareNat c g g' hg).app L) ≪≫
      (squareNat c f f' hf).app ((Scheme.Modules.pullback g).obj L) ≪≫
      (Scheme.Modules.pullback c).mapIso ((Scheme.Modules.pullbackComp f g).app L) =
    (Scheme.Modules.pullbackComp f' g').app ((Scheme.Modules.pullback c).obj L) ≪≫
      (squareNat c (f ≫ g) (f' ≫ g') hfg).app L := by
  have hp := Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    f g (f ≫ g) rfl c c c f' g' (f' ≫ g') rfl hf hg hfg L
  apply iso_paste
  simpa only [squareNat, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv,
    pullbackCongr_refl, Iso.trans_refl, Iso.app_hom, Functor.mapIso_hom] using hp

def compLift (f g : X ⟶ X) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    (Scheme.Modules.pullback (f ≫ g)).obj L ≅ L :=
  ((Scheme.Modules.pullbackComp f g).app L).symm ≪≫ (Scheme.Modules.pullback f).mapIso β ≪≫ α

def lift (c : Y ⟶ X) (f : X ⟶ X) (f' : Y ⟶ Y) (hf : c ≫ f = f' ≫ c)
    {L : X.Modules} (α : (Scheme.Modules.pullback f).obj L ≅ L) :
    (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback c).obj L) ≅
      (Scheme.Modules.pullback c).obj L :=
  (squareNat c f f' hf).app L ≪≫ (Scheme.Modules.pullback c).mapIso α

lemma lift_comp (c : Y ⟶ X) (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (hfg : c ≫ (f ≫ g) = (f' ≫ g') ≫ c) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    lift c (f ≫ g) (f' ≫ g') hfg (compLift f g α β) =
      compLift f' g' (lift c f f' hf α) (lift c g g' hg β) := by
  have hn := (squareNat c f f' hf).hom.naturality β.hom
  dsimp only [Functor.comp_map] at hn
  let C := (Scheme.Modules.pullback c).mapIso ((Scheme.Modules.pullbackComp f g).app L)
  let D := (Scheme.Modules.pullbackComp f' g').app ((Scheme.Modules.pullback c).obj L)
  have hp := congrArg (fun e => D.inv ≫ e.hom ≫ C.inv) (square_paste c f g f' g' hf hg hfg L)
  change D.inv ≫
    (((Scheme.Modules.pullback f').mapIso ((squareNat c g g' hg).app L)).hom ≫
      ((squareNat c f f' hf).app ((Scheme.Modules.pullback g).obj L)).hom ≫ C.hom) ≫ C.inv =
    D.inv ≫ (D.hom ≫ ((squareNat c (f ≫ g) (f' ≫ g') hfg).app L).hom) ≫ C.inv at hp
  have hp' : D.inv ≫ ((Scheme.Modules.pullback f').mapIso ((squareNat c g g' hg).app L)).hom ≫
      ((squareNat c f f' hf).app ((Scheme.Modules.pullback g).obj L)).hom =
      ((squareNat c (f ≫ g) (f' ≫ g') hfg).app L).hom ≫ C.inv := by
    simpa only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hp
  apply Iso.ext
  simp only [lift, compLift, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% hn]
  have hp'' := hp'
  dsimp only [C, D, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hp''
  rw [reassoc_of% hp'']

open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift

lemma lift_scaled (c : Y ⟶ X) (f : X ⟶ X) (f' : Y ⟶ Y) (hf : c ≫ f = f' ≫ c)
    {L : X.Modules} (α : (Scheme.Modules.pullback f).obj L ≅ L) (u : Γ(X, ⊤)ˣ) :
    lift c f f' hf (α ≪≫ smulIso u L) =
      lift c f f' hf α ≪≫
        smulIso (Units.map c.appTop.hom.toMonoidHom u) ((Scheme.Modules.pullback c).obj L) := by
  unfold lift
  rw [Functor.mapIso_trans, pullback_mapIso_smulIso]
  exact (Iso.trans_assoc _ _ _).symm

lemma lift_changeMap (c : Y ⟶ X) {f g : X ⟶ X} {f' g' : Y ⟶ Y}
    (h : f = g) (h' : f' = g') (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    {L : X.Modules} (α : (Scheme.Modules.pullback g).obj L ≅ L) :
    lift c f f' hf ((Scheme.Modules.pullbackCongr h).app L ≪≫ α) =
      (Scheme.Modules.pullbackCongr h').app ((Scheme.Modules.pullback c).obj L) ≪≫
        lift c g g' hg α := by
  subst g
  subst g'
  apply Iso.ext
  simp [lift, Scheme.Modules.pullbackCongr]

/-- Arbitrary pullback through actual commuting squares preserves the scalar
commutator as an equality of sheaf isomorphisms. -/
lemma lift_commutation (c : Y ⟶ X) (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (h : f ≫ g = g ≫ f) (h' : f' ≫ g' = g' ≫ f')
    {L : X.Modules} (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) (u : Γ(X, ⊤)ˣ)
    (hαβ : compLift f g α β = (Scheme.Modules.pullbackCongr h).app L ≪≫
      compLift g f β α ≪≫ smulIso u L) :
    compLift f' g' (lift c f f' hf α) (lift c g g' hg β) =
      (Scheme.Modules.pullbackCongr h').app ((Scheme.Modules.pullback c).obj L) ≪≫
        compLift g' f' (lift c g g' hg β) (lift c f f' hf α) ≪≫
          smulIso (Units.map c.appTop.hom.toMonoidHom u) ((Scheme.Modules.pullback c).obj L) := by
  have hfg : c ≫ (f ≫ g) = (f' ≫ g') ≫ c := by
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]
  have hgf : c ≫ (g ≫ f) = (g' ≫ f') ≫ c := by
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc]
  rw [← lift_comp c f g f' g' hf hg hfg, hαβ]
  rw [← Iso.trans_assoc, lift_scaled, lift_changeMap c h h' hfg hgf,
    lift_comp c g f g' f' hg hf hgf, Iso.trans_assoc]

#print axioms lift_commutation
#print axioms lift_comp
#print axioms square_paste
end PullbackLifts
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255

lemma fibre_scalar {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (f : R →+* A) (c : Rˣ) :
    Units.map (pullback.fst E.projection (Spec.map (CommRingCat.ofHom f))).appTop.hom.toMonoidHom (scalar E c) =
      scalar (baseChangedFamily E (Spec.map (CommRingCat.ofHom f))) (Units.map f.toMonoidHom c) := by
  let x := Spec.map (CommRingCat.ofHom f)
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫ E.projection.appTop ≫
        (pullback.fst E.projection x).appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
        (pullback.snd E.projection x).appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  apply Units.ext
  exact congrArg (fun g : CommRingCat.of R ⟶ Γ(pullback E.projection x, ⊤) => g (c : R)) h
#print axioms fibre_scalar

namespace Sections

def actOfHom {k : Type u} [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (f : X ⟶ X) (hf : f ≫ p = p) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
    Module.End k Γ(L, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
  refine { toFun := act f α, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    simp only [act, Scheme.Modules.pullbackLocalSection_add, map_add]
  · intro a s
    change α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f
      ((p.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv a)) • s)) =
      (p.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv a)) • act f α s
    have htop : p.appLE ⊤ ⊤ le_top = p.appTop := by simp [Scheme.Hom.appLE]
    rw [htop]
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module k Γ(L, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
    exact (actLinear k p f hf α).map_smul a s

lemma act_smulIso {X : Scheme.{u}} {L : X.Modules} (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (u : Γ(X, ⊤)ˣ) (s : Γ(L, ⊤)) :
    act f (α ≪≫ smulIso u L) s = (u : Γ(X, ⊤)) • act f α s := by
  change resTop (u : Γ(X, ⊤)) ⊤ • act f α s = _
  simp [resTop]

lemma act_commutation {X : Scheme.{u}} {L : X.Modules} (f g : X ⟶ X)
    (h : f ≫ g = g ≫ f) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) (u : Γ(X, ⊤)ˣ)
    (hc : PullbackLifts.compLift f g α β = (Scheme.Modules.pullbackCongr h).app L ≪≫
      PullbackLifts.compLift g f β α ≪≫ smulIso u L) (s : Γ(L, ⊤)) :
    act f α (act g β s) = (u : Γ(X, ⊤)) • act g β (act f α s) := by
  rw [← act_comp, ← act_comp]
  change act _ (PullbackLifts.compLift f g α β) s =
    (u : Γ(X, ⊤)) • act _ (PullbackLifts.compLift g f β α) s
  rw [hc, ← Iso.trans_assoc, act_smulIso, act_changeMap]
end Sections

variable {R A : Type u} [CommRing R] [CommRing A] (E : EllipticFamily R)
    (x : Spec (.of A) ⟶ Spec (.of R))
abbrev fibreTranslation (P : point E) :=
  fibreEnd E x (translation E P) (RelativeDoubledTorsionThetaLiftR0255.translation_over E P)

lemma fibreTranslations_commute (P Q : point E) :
    fibreTranslation E x P ≫ fibreTranslation E x Q = fibreTranslation E x Q ≫ fibreTranslation E x P := by
  have hp := RelativeDoubledTorsionThetaLiftR0255.translation_over E P
  have hq := RelativeDoubledTorsionThetaLiftR0255.translation_over E Q
  have hpq : (translation E P ≫ translation E Q) ≫ E.projection = E.projection := by
    rw [Category.assoc, hq, hp]
  have hqp : (translation E Q ≫ translation E P) ≫ E.projection = E.projection := by
    rw [Category.assoc, hp, hq]
  rw [← fibreEnd_comp E x _ _ hp hq hpq, ← fibreEnd_comp E x _ _ hq hp hqp]
  congr 1
  exact translations_commute E P Q

def fibreLift (m : ℕ) (P : point E) (α : Lift E m (translation E P)) :
    (Scheme.Modules.pullback (fibreTranslation E x P)).obj
        ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ≅
      (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m) :=
  PullbackLifts.lift (pullback.fst E.projection x) (translation E P) (fibreTranslation E x P)
    (fibreEnd_fst E x _ _).symm α

lemma fibreLift_commutation (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Rˣ) (hc : Commutator E m P Q α β c) :
    PullbackLifts.compLift _ _ (fibreLift E x m P α) (fibreLift E x m Q β) =
      (Scheme.Modules.pullbackCongr (fibreTranslations_commute E x P Q)).app _ ≪≫
        PullbackLifts.compLift _ _ (fibreLift E x m Q β) (fibreLift E x m P α) ≪≫
          smulIso (Units.map (pullback.fst E.projection x).appTop.hom.toMonoidHom (scalar E c)) _ := by
  obtain ⟨h, hc⟩ := hc
  apply PullbackLifts.lift_commutation
  simpa only [compose, scaled, changeMap, PullbackLifts.compLift, Iso.trans_assoc] using hc

#print axioms Sections.act_commutation
#print axioms fibreLift_commutation

def fibreAct {R k : Type u} [CommRing R] [CommRing k] (E : EllipticFamily R)
    (x : Spec (.of k) ⟶ Spec (.of R)) (m : ℕ) (P : point E)
    (α : Lift E m (translation E P)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x)
      ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ⊤
    Module.End k Γ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m), ⊤) :=
  Sections.actOfHom _ _ (fibreEnd_snd E x _ _) (fibreLift E x m P α)

lemma fibreAct_relation {R k : Type u} [CommRing R] [CommRing k] (E : EllipticFamily R)
    (f : R →+* k) (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Rˣ) (hc : Commutator E m P Q α β c) :
    let x := Spec.map (CommRingCat.ofHom f)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x)
      ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ⊤
    fibreAct E x m P α * fibreAct E x m Q β = f (c : R) •
      (fibreAct E x m Q β * fibreAct E x m P α) := by
  dsimp only
  let x := Spec.map (CommRingCat.ofHom f)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x)
      ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ⊤
  ext s
  have h := Sections.act_commutation _ _ (fibreTranslations_commute E x P Q)
    (fibreLift E x m P α) (fibreLift E x m Q β) _ (fibreLift_commutation E x m P Q α β c hc) s
  rw [fibre_scalar] at h
  change Sections.act (fibreTranslation E x P) (fibreLift E x m P α)
    (Sections.act (fibreTranslation E x Q) (fibreLift E x m Q β) s) =
    ((pullback.snd E.projection x).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv (f (c : R)))) •
      Sections.act (fibreTranslation E x Q) (fibreLift E x m Q β)
        (Sections.act (fibreTranslation E x P) (fibreLift E x m P α) s)
  have htop : (pullback.snd E.projection x).appLE ⊤ ⊤ le_top =
      (pullback.snd E.projection x).appTop := by simp [Scheme.Hom.appLE]
  rw [htop]
  exact h

lemma exists_fibre_eigensection {R k : Type u} [CommRing R] [Field k] [IsAlgClosed k] [Algebra ℚ k]
    (E : EllipticFamily R) (f : R →+* k) (m : ℕ) (hm : 0 < m) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Rˣ) (hc : Commutator E m P Q α β c) (i : ℕ) (hi : f (c : R) ^ i = 1) :
    let x := Spec.map (CommRingCat.ofHom f)
    let L := (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x) L ⊤
    ∃ (a b : kˣ) (s : Γ(L, ⊤)), s ≠ 0 ∧
      (fibreAct E x m P α ^ i) s = (a : k) • s ∧ fibreAct E x m Q β s = (b : k) • s := by
  dsimp only
  let x := Spec.map (CommRingCat.ofHom f)
  let F := baseChangedFamily E x
  let L := (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection (thetaLine F m) ⊤
  let e := sectionsIso F.projection ((fibreLineIso E x m) ≪≫ (fieldLineIso F m).symm)
  letI := field_sections_finite F m hm
  letI : Module.Finite k Γ(L, ⊤) := Module.Finite.equiv e.symm
  letI : Nontrivial Γ(L, ⊤) := Module.finrank_pos_iff.mp
    (by rw [e.finrank_eq, field_sections_finrank F m hm]; exact hm)
  letI : IsIso (translation E P) := (translationIso E P).isIso_hom
  letI : IsIso (translation E Q) := (translationIso E Q).isIso_hom
  letI : IsIso (fibreTranslation E x P) := fibreEnd_isIso E x _ _
  letI : IsIso (fibreTranslation E x Q) := fibreEnd_isIso E x _ _
  have hA : Function.Injective (fibreAct E x m P α) :=
    (Sections.act_bijective (fibreTranslation E x P) (fibreLift E x m P α)).1
  have hB : Function.Injective (fibreAct E x m Q β) :=
    (Sections.act_bijective (fibreTranslation E x Q) (fibreLift E x m Q β)).1
  have hAi : Function.Injective (fibreAct E x m P α ^ i) := by
    rw [Module.End.coe_pow]
    exact hA.iterate i
  exact exists_common_unit_eigenvector _ _
    (linear_twist_pow_commute _ _ (f (c : R)) (fibreAct_relation E f m P Q α β c hc) i hi) hAi hB
#print axioms exists_fibre_eigensection

open RelativeMidpointSymmetricThetaLift
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
variable {R k : Type u} [CommRing R] [Field k] [IsAlgClosed k] (E : EllipticFamily R)
    (x : Spec (.of k) ⟶ Spec (.of R))

def sectionAt (P : point E) : SchemeHomOver x E.projection :=
  GoodReductionJacobian.schemeHomOverComp x (Category.comp_id x) P

lemma sectionAt_mul (P Q : point E) :
    sectionAt E x (E.law.mul (𝟙 _) P Q) = E.law.mul x (sectionAt E x P) (sectionAt E x Q) :=
  E.law.mul_natural (𝟙 _) x x (Category.comp_id x) P Q

lemma sectionAt_nsmul (P : point E) (n : ℕ) :
    sectionAt E x (E.law.nsmul (𝟙 _) n P) = E.law.nsmul x n (sectionAt E x P) :=
  E.law.nsmul_natural (𝟙 _) x x (Category.comp_id x) n P

def shiftPoint (P : point E) (z : SchemeHomOver x E.projection) : SchemeHomOver x E.projection :=
  E.law.mul x z (sectionAt E x (E.law.nsmul (𝟙 _) 2 P))

lemma shiftPoint_iterate (P : point E) (n : ℕ) (z : SchemeHomOver x E.projection) :
    (shiftPoint E x P)^[n] z = E.law.mul x z
      (sectionAt E x (E.law.nsmul (𝟙 _) n (E.law.nsmul (𝟙 _) 2 P))) := by
  letI := E.law.pointGroup x
  rw [sectionAt_nsmul, nsmul_pow]
  change (fun w => w * sectionAt E x (E.law.nsmul (𝟙 _) 2 P))^[n] z = _
  induction n with
  | zero => exact (mul_one z).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact (mul_assoc _ _ _).trans (congrArg (z * ·) (pow_succ _ n).symm)

lemma fibrePointAt_shift (P : point E) (z : SchemeHomOver x E.projection) :
    fibrePointAt E x (shiftPoint E x P z) = (fibreTranslation E x P).base (fibrePointAt E x z) := by
  have he : shiftPoint E x P z =
      (show SchemeHomOver x E.projection from ⟨z.val ≫ translation E P, by
        rw [Category.assoc, RelativeDoubledTorsionThetaLiftR0255.translation_over, z.property]⟩) := by
    apply Subtype.ext
    exact (point_translate E x z _).symm
  rw [he]
  change (fibrePoint E x _).val (IsLocalRing.closedPoint k) = _
  rw [fibrePoint_end]
  rfl

lemma fibrePointAt_shift_iterate (P : point E) (n : ℕ) (z : SchemeHomOver x E.projection) :
    fibrePointAt E x ((shiftPoint E x P)^[n] z) =
      (fibreTranslation E x P).base^[n] (fibrePointAt E x z) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', fibrePointAt_shift, ih,
      Function.iterate_succ_apply']

lemma translatedTwoRows_orbit {m : ℕ} (hm : 0 < m) (M : FamilyLevel R E (2*m))
    (i : Fin m) (z : SchemeHomOver x E.projection) (bj : Bool × Fin m) :
    fibrePointAt E x (translatedTwoRows E x z hm M i bj) =
      (fibreTranslation E x M.y).base^[bj.2.val]
        ((fibreTranslation E x M.x).base^[if bj.1 then i.val else 0] (fibrePointAt E x z)) := by
  rw [← fibrePointAt_shift_iterate, ← fibrePointAt_shift_iterate]
  congr 1
  rw [shiftPoint_iterate, shiftPoint_iterate, E.law.mul_assoc]
  unfold translatedTwoRows translatedCombination levelCombinationAt levelCombination twoRowIndex
  dsimp only [Function.comp_apply, doubledLevel]
  rw [← sectionAt_mul]
  cases bj with
  | mk b j => cases b <;> rfl
#print axioms translatedTwoRows_orbit

lemma fibre_eigen_zero_invariant {R k : Type u} [CommRing R] [Field k]
    (E : EllipticFamily R) (x : Spec (.of k) ⟶ Spec (.of R)) (m : ℕ)
    (P : point E) (α : Lift E m (translation E P)) (n : ℕ)
    (s : Γ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m), ⊤))
    (a : kˣ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x)
      ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ⊤
    (fibreAct E x m P α ^ n) s = (a : k) • s →
      ((fibreTranslation E x P).base^[n]) ⁻¹' Sections.zeroSupport s = Sections.zeroSupport s := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x)
    ((Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)) ⊤
  intro hs
  apply Sections.eigen_zeroSupport_iterate
    ((RelativeNormalizedThetaInversion.line_invertible E m).pullback _)
    _ (fibreLift E x m P α) n s (scalar (baseChangedFamily E x) a).val
    (scalar (baseChangedFamily E x) a).isUnit
  rw [Module.End.coe_pow] at hs
  change (Sections.act (fibreTranslation E x P) (fibreLift E x m P α))^[n] s =
    ((pullback.snd E.projection x).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv (a : k))) • s at hs
  have htop : (pullback.snd E.projection x).appLE ⊤ ⊤ le_top =
      (pullback.snd E.projection x).appTop := by simp [Scheme.Hom.appLE]
  rw [htop] at hs
  exact hs

lemma invariant_iterates {X : Type*} (f : X → X) (S : Set X)
    (h : f ⁻¹' S = S) (n : ℕ) {z : X} (hz : z ∈ S) : f^[n] z ∈ S := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change f^[n] z ∈ f ⁻¹' S
    rwa [h]

lemma geometric_commutator_primitive {R k : Type u} [CommRing R] [Field k]
    [IsAlgClosed k] [Algebra ℚ k] (E : EllipticFamily R) (f : R →+* k)
    (m : ℕ) (hm : 0 < m) (M : FamilyLevel R E (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (c : Rˣ) (hc : Commutator E m M.x M.y α β c)
    (i : Fin m) (hi : i.val ≠ 0) : f (c : R) ^ i.val ≠ 1 := by
  intro hpow
  let x := Spec.map (CommRingCat.ofHom f)
  let L := (Scheme.Modules.pullback (pullback.fst E.projection x)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection x) L ⊤
  obtain ⟨a, b, s, hs, ha, hb⟩ := exists_fibre_eigensection E f m hm M.x M.y α β c hc i.val hpow
  obtain ⟨D, hD, _⟩ := fibre_zero_divisor E x m hm (Sections.sectionHom s)
    (Sections.fromSection_ne_zero s hs)
  obtain ⟨z, hz⟩ := divisor_exists_fibre_point E x hm D
  have hA := fibre_eigen_zero_invariant E x m M.x α i.val s a ha
  have hB := fibre_eigen_zero_invariant E x m M.y β 1 s b (by simpa only [pow_one] using hb)
  have hB' : (fibreTranslation E x M.y).base ⁻¹' Sections.zeroSupport s =
      Sections.zeroSupport s := by simpa only [Function.iterate_one] using hB
  have hz' : fibrePointAt E x z ∈ Sections.zeroSupport s := by
    change fibrePointAt E x z ∈ (Scheme.Modules.zeroSchemeIdeal (Sections.sectionHom s)).support
    rwa [← hD]
  apply fibre_two_rows_not_subset_zero_divisor E x hm M i hi z D
  intro bj
  rw [hD]
  change fibrePointAt E x (translatedTwoRows E x z hm M i bj) ∈ Sections.zeroSupport s
  rw [translatedTwoRows_orbit]
  apply invariant_iterates _ _ hB'
  cases bj with
  | mk b j =>
    cases b
    · exact hz'
    · change fibrePointAt E x z ∈ ((fibreTranslation E x M.x).base^[i.val]) ⁻¹' Sections.zeroSupport s
      rwa [hA]
#print axioms geometric_commutator_primitive
end ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator

namespace ArithmeticThetaRelativeThetaRelationsR0256
open RelativePrimitiveThetaCommutator

/-- The actual theta commutator of a full doubled level basis is primitive on every fibre. -/
theorem relative_primitive_theta_commutator :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R), ∀ m : ℕ, 0 < m → Even m → ∀ M : ArithmeticThetaLegendreAtlasR0176.FamilyLevel R E (2*m), ∀ (α : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E M.x)) (β : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E M.y)), ∃! c : Rˣ, ArithmeticThetaRelativeThetaRelationsR0256.Commutator E m M.x M.y α β c ∧ ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c := by
  intro R _ _ _ E m hm _ M α β
  apply (primitive_commutator_iff_geometric_tests E m M α β).mpr
  intro k _ _ f i hi
  letI : Algebra ℚ k := (f.comp (algebraMap ℚ R)).toAlgebra
  exact geometric_commutator_primitive E f m hm M α β _
    (commutatorUnit_spec E m M.x M.y α β) i hi

#print axioms relative_primitive_theta_commutator
end ArithmeticThetaRelativeThetaRelationsR0256
