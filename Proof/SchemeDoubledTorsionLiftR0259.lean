module

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
public import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
public import Theorems.Thm_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
public import SchemeThetaInversionR0259

@[expose] public section

/-! The doubled-torsion construction for the actual conormal theta line.
The supporting reduction below retains arbitrary scheme bases. -/
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u v
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255

variable {S : Scheme.{u}} (E : Family S)

@[instance_reducible] def pointCommGroup {T : Scheme.{u}} (t : T ⟶ S) :
    CommGroup (SchemeHomOver t E.p) :=
  { SchemeThetaInversion.pointGroup E t with mul_comm := E.law.mul_comm t }

lemma multiple_eq_pow {T : Scheme.{u}} (t : T ⟶ S)
    (P : SchemeHomOver t E.p) (n : ℕ) :
    letI := pointCommGroup E t
    ArithmeticThetaSchemeLevelR0204.multiple E t n P = P ^ n := by
  letI := pointCommGroup E t
  induction n with
  | zero => rfl
  | succ n ih =>
    change E.law.mul t (ArithmeticThetaSchemeLevelR0204.multiple E t n P) P = _
    rw [ih, pow_succ]
    rfl

/-- Pulling a section along its actual base map preserves the group law. -/
def pointPullback {T U : Scheme.{u}} (t : T ⟶ S) (s : U ⟶ S)
    (f : U ⟶ T) (hf : f ≫ t = s) :
    letI := pointCommGroup E t
    letI := pointCommGroup E s
    SchemeHomOver t E.p →* SchemeHomOver s E.p := by
  letI := pointCommGroup E t
  letI := pointCommGroup E s
  exact {
    toFun := GoodReductionJacobian.schemeHomOverComp f hf
    map_one' := SchemeLocal.one_natural E.law t s f hf
    map_mul' := E.law.mul_natural t s f hf }

lemma translation_over (P : point E) : translation E P ≫ E.p = E.p :=
  (E.law.mul E.p ⟨𝟙 _, Category.id_comp _⟩
    ⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc,
      (multiple E P 2).property, Category.comp_id]⟩).property

/-- Translation by a section killed by two is the identity, including empty bases. -/
lemma translation_eq_id_of_two_killed (P : point E)
    (hP : multiple E P 2 = E.law.one (𝟙 S)) :
    translation E P = 𝟙 E.curve := by
  have h := SchemeLocal.one_natural E.law (𝟙 S) E.p E.p (Category.comp_id _)
  have hc : (⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc,
      (multiple E P 2).property, Category.comp_id]⟩ : SchemeHomOver E.p E.p) =
      E.law.one E.p := by
    rw [hP]
    exact h
  unfold translation
  rw [hc, E.law.mul_one]

/-- The actual sheaf comparison in the two-killed special case. -/
def liftOfTwoKilled (m : ℕ) (P : point E)
    (hP : multiple E P 2 = E.law.one (𝟙 S)) : Lift E m (translation E P) :=
  changeMap E m (translation_eq_id_of_two_killed E P hP) (identityLift E m)

abbrev conormal := ArithmeticThetaSchemeHodgeR0205.Cotangent E

def primitiveLine : E.curve.Modules :=
  Scheme.Modules.dual E.zero.ker.module ⊗ (Scheme.Modules.pullback E.p).obj (conormal E)

lemma conormal_invertible : Scheme.Modules.IsInvertible (conormal E) :=
  (SchemeThetaInversion.zero_cartier E).isInvertible_module.pullback E.zero

lemma primitiveLine_invertible : Scheme.Modules.IsInvertible (primitiveLine E) :=
  (SchemeThetaInversion.zero_cartier E).isInvertible_module.dual.1.tensor_monoidalV2
    ((conormal_invertible E).pullback E.p)

/-- The power comparison uses ideal multiplication and the actual conormal sheaf. -/
def linePowerIso (m : ℕ) (hm : 0 < m) :
    thetaLine E m ≅ (primitiveLine E).tensorPow m := by
  let eD : Scheme.Modules.dual ((E.zero.ker ^ m).module) ≅
      (Scheme.Modules.dual E.zero.ker.module).tensorPow m :=
    ((MonoidalClosed.internalHom (C := E.curve.Modules)).mapIso
      (idealPowerIso E.zero.ker (SchemeThetaInversion.zero_cartier E) m hm).symm.op).app
        (𝟙_ _) ≪≫
      (dualPowerIso_exists _ (SchemeThetaInversion.zero_cartier E).isInvertible_module m).some
  exact (eD ⊗ᵢ Scheme.Modules.pullbackTensorPowIso E.p (conormal E) m) ≪≫
    (tensorPowerIso_exists _ _ (SchemeThetaInversion.zero_cartier E).isInvertible_module.dual.1
      ((conormal_invertible E).pullback E.p) m).some

/-- The origin fibre is canonically trivial because the Hodge factor is e*I. -/
def primitiveRigidification :
    (Scheme.Modules.pullback E.zero).obj (primitiveLine E) ≅ 𝟙_ S.Modules := by
  let eH : (Scheme.Modules.pullback E.zero).obj
      ((Scheme.Modules.pullback E.p).obj (conormal E)) ≅ conormal E :=
    (Scheme.Modules.pullbackComp E.zero E.p).app _ ≪≫
    (Scheme.Modules.pullbackCongr (SchemeThetaInversion.zero_over E)).app _ ≪≫
    (Scheme.Modules.pullbackId S).app _
  letI := dualComparison_isIso E.zero E.zero.ker.module
    (SchemeThetaInversion.zero_cartier E).isInvertible_module
  exact Scheme.Modules.pullbackTensorObjIso E.zero _ _ ≪≫
    (asIso (dualComparison E.zero E.zero.ker.module) ⊗ᵢ eH) ≪≫
      (β_ _ _) ≪≫ (conormal_invertible E).dual_monoidalV2.2.some

def primitiveInverseIso :
    (Scheme.Modules.pullback (inverse E)).obj (primitiveLine E) ≅ primitiveLine E := by
  let e : thetaLine E 1 ≅ primitiveLine E :=
    linePowerIso E 1 (by decide) ≪≫ Scheme.Modules.tensorPowOneIso _
  exact (Scheme.Modules.pullback (inverse E)).mapIso e.symm ≪≫
    SchemeThetaInversion.initialLift E 1 ≪≫ e

abbrev curvePoint := SchemeHomOver E.p E.p
local instance curvePointCommGroup : CommGroup (curvePoint E) := pointCommGroup E E.p

def pullbackPrimitive (a : curvePoint E) : E.curve.Modules :=
  (Scheme.Modules.pullback a.val).obj (primitiveLine E)

lemma pullbackPrimitive_invertible (a : curvePoint E) :
    Scheme.Modules.IsInvertible (pullbackPrimitive E a) :=
  (primitiveLine_invertible E).pullback a.val

lemma curvePoint_one_val : (1 : curvePoint E).val = E.p ≫ E.zero :=
  (congrArg Subtype.val (SchemeLocal.one_natural E.law (𝟙 S) E.p E.p
    (Category.comp_id _))).symm

def pullbackPrimitiveUnitIso : pullbackPrimitive E 1 ≅ 𝟙_ E.curve.Modules :=
  (Scheme.Modules.pullbackCongr (curvePoint_one_val E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp E.p E.zero).app _).symm ≪≫
    (Scheme.Modules.pullback E.p).mapIso (primitiveRigidification E) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso E.p

lemma comp_inverse (a : curvePoint E) : a.val ≫ inverse E = a⁻¹.val := by
  have h := SchemeThetaInversion.inverse_natural E E.p E.p a.val a.property
    ⟨𝟙 E.curve, Category.id_comp _⟩
  have he : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨𝟙 E.curve, Category.id_comp _⟩ : curvePoint E) = a :=
    Subtype.ext (Category.comp_id _)
  rw [he] at h
  exact congrArg Subtype.val h

def pullbackPrimitiveInvIso (a : curvePoint E) :
    pullbackPrimitive E a⁻¹ ≅ pullbackPrimitive E a :=
  (Scheme.Modules.pullbackCongr (comp_inverse E a).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp a.val (inverse E)).app _).symm ≪≫
    (Scheme.Modules.pullback a.val).mapIso (primitiveInverseIso E)

def constantPoint (P : point E) : curvePoint E :=
  pointPullback E (𝟙 S) E.p E.p (Category.comp_id _) P

lemma constantPoint_torsion (P : point E) (n : ℕ)
    (hP : multiple E P n = E.law.one (𝟙 S)) : constantPoint E P ^ n = 1 := by
  letI := pointCommGroup E (𝟙 S)
  have hp : P ^ n = 1 := (multiple_eq_pow E (𝟙 S) P n).symm.trans hP
  exact (map_pow (pointPullback E (𝟙 S) E.p E.p (Category.comp_id _)) P n).symm.trans
    ((congrArg (pointPullback E (𝟙 S) E.p E.p (Category.comp_id _)) hp).trans
      (map_one _))

lemma id_mul_constantPoint_two (P : point E) :
    ((⟨𝟙 E.curve, Category.id_comp _⟩ : curvePoint E) * constantPoint E P ^ 2).val =
      translation E P := by
  have h : constantPoint E P ^ 2 = constantPoint E (multiple E P 2) := by
    letI := pointCommGroup E (𝟙 S)
    rw [multiple, multiple_eq_pow]
    exact (map_pow (pointPullback E (𝟙 S) E.p E.p (Category.comp_id _)) P 2).symm
  rw [h]
  rfl

/-- The geometric cube obligation on actual pullback sheaves, without an affine
or Noetherian restriction. This is an intermediate predicate, not a provider. -/
def ActualPrimitiveCube : Prop :=
  ∀ a b c : curvePoint E, Nonempty
    (pullbackPrimitive E (a * b * c) ⊗
        ((pullbackPrimitive E a ⊗ pullbackPrimitive E b) ⊗ pullbackPrimitive E c) ≅
      (pullbackPrimitive E (a * b) ⊗ pullbackPrimitive E (b * c)) ⊗
        pullbackPrimitive E (c * a))

/-- Integral cancellation after a geometric cube provider has been constructed. -/
theorem lift_of_actualPrimitiveCube (hcube : ActualPrimitiveCube E)
    (m : ℕ) (hm : 0 < m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S)) :
    Nonempty (Lift E m (translation E P)) := by
  let a : curvePoint E := ⟨𝟙 E.curve, Category.id_comp _⟩
  obtain ⟨α⟩ := lineFamily_doubled_torsion (pullbackPrimitive E)
    (pullbackPrimitive_invertible E) ⟨pullbackPrimitiveUnitIso E⟩
    (fun x => ⟨pullbackPrimitiveInvIso E x⟩) hcube m a (constantPoint E P)
    (constantPoint_torsion E P (2*m) hP)
  let eleft : pullbackPrimitive E (a * constantPoint E P ^ 2) ≅
      (Scheme.Modules.pullback (translation E P)).obj (primitiveLine E) :=
    (Scheme.Modules.pullbackCongr (id_mul_constantPoint_two E P)).app _
  let eright : pullbackPrimitive E a ≅ primitiveLine E :=
    (Scheme.Modules.pullbackId E.curve).app _
  exact ⟨(Scheme.Modules.pullback (translation E P)).mapIso (linePowerIso E m hm) ≪≫
    Scheme.Modules.pullbackTensorPowIso _ _ m ≪≫
    Scheme.Modules.tensorPowMapIso eleft.symm m ≪≫ α ≪≫
    Scheme.Modules.tensorPowMapIso eright m ≪≫ (linePowerIso E m hm).symm⟩

#print axioms liftOfTwoKilled
#print axioms primitiveRigidification
#print axioms lift_of_actualPrimitiveCube
end SchemeDoubledTorsionLift
end ArithmeticThetaSchemeThetaMarkingR0259


/-! Universe-polymorphic adaptation of S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq. -/
namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.GroupModelRefinement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace DescB

theorem baseChange_mul_fst {S S' : Type u} [CommRing S] [CommRing S']
    (u : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (pullback.snd f u)) :
    ((G.baseChange u).mul t' x y).1 ≫ pullback.fst f u =
      (G.mul (t' ≫ u)
        ⟨x.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul u G t' x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
  exact h

theorem mul_val_congr {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end DescB

open DescB in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (φ₁ : R₁ →+* R) (φ₂ : R₂ →+* R) (ψ : R₁ →+* R₂) (hψ : φ₂.comp ψ = φ₁)
    (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (L₁ : RelativeGroupLaw R₁ f₁) (hA₁ : AbelianSchemePropertyBundle R₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom φ₁)))
    (hLa₁ : (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ₁))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1)) :
    ∃ (A₂ : Scheme.{u}) (f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)) (L₂ : RelativeGroupLaw R₂ f₂) (_ : AbelianSchemePropertyBundle R₂ f₂)
      (a₂ : A ⟶ A₂) (ha₂ : IsPullback a₂ f f₂ (Spec.map (CommRingCat.ofHom φ₂)))
      (b : A₂ ⟶ A₁) (hb : IsPullback b f₂ f₁ (Spec.map (CommRingCat.ofHom ψ))) (_ : a₂ ≫ b = a₁),
      (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₂ = (L₂.mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ b = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom ψ))
        ⟨P.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, Q.2]⟩).1) := by
  have hSpec : Spec.map (CommRingCat.ofHom φ₁) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  let ι := Spec.map (CommRingCat.ofHom ψ)
  have hP := IsPullback.of_hasPullback f₁ ι

  let a₂ : A ⟶ pullback f₁ ι := pullback.lift a₁ (f ≫ Spec.map (CommRingCat.ofHom φ₂))
    (by rw [ha₁.w, hSpec, Category.assoc])
  have ha₂fst : a₂ ≫ pullback.fst f₁ ι = a₁ := pullback.lift_fst _ _ _
  have ha₂snd : a₂ ≫ pullback.snd f₁ ι = f ≫ Spec.map (CommRingCat.ofHom φ₂) := pullback.lift_snd _ _ _
  have ha₂ : IsPullback a₂ f (pullback.snd f₁ ι) (Spec.map (CommRingCat.ofHom φ₂)) := by
    refine IsPullback.of_right ?_ ha₂snd hP
    rw [ha₂fst, ← hSpec]
    exact ha₁
  refine ⟨pullback f₁ ι, pullback.snd f₁ ι, L₁.baseChange ι,
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback hA₁ hP, a₂, ha₂, pullback.fst f₁ ι, hP, ha₂fst, ?_, ?_⟩
  · intro T t P Q
    apply pullback.hom_ext
    · rw [Category.assoc, ha₂fst, hLa₁ T t P Q, baseChange_mul_fst]
      exact mul_val_congr L₁ (by rw [hSpec, Category.assoc]) _ _ _ _
        (show P.1 ≫ a₁ = (P.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
        (show Q.1 ≫ a₁ = (Q.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
    · have h1 : (L.mul t P Q).1 ≫ a₂ ≫ pullback.snd f₁ ι = t ≫ Spec.map (CommRingCat.ofHom φ₂) := by
        rw [ha₂snd, ← Category.assoc, (L.mul t P Q).2]
      rw [Category.assoc]
      symm
      refine Eq.trans ?_ h1.symm
      exact ((L₁.baseChange ι).mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).2
  · intro T t P Q
    exact baseChange_mul_fst ι L₁ t P Q
#print axioms solution
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.GroupModelRefinement


/-! Universe-polymorphic adaptation of S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_fg_subalgebra_isPullback_prodStr_model. -/
namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeModelDescent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

noncomputable section

namespace CubeDescentAux

namespace FGStages

variable {A₀ : Type v} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type u := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type u := ↥i.1

abbrev φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

abbrev g (i : Idx B) : G B i →+* A := algebraMap ↥i.1 A

theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

def sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

theorem g_comp_φ (i j : Idx B) (h : i ≤ j) : (g B j).comp (φ B i j h) = g B i := RingHom.ext fun _ => rfl

theorem isNoetherianRing [IsNoetherianRing A₀] (i : Idx B) : IsNoetherianRing (G B i) := by
  haveI := (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  exact Algebra.FiniteType.isNoetherianRing A₀ ↥i.1

end FGStages

theorem one_comp_eq_one {R R₁ : Type u} [CommRing R] [CommRing R₁] {A A₁ : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)}
    (L : RelativeGroupLaw R f) (L₁ : RelativeGroupLaw R₁ f₁) (φ : R₁ →+* R)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by

  have key : ∀ {t₁ : T ⟶ Spec (CommRingCat.of R₁)} (x : SchemeHomOver t₁ f₁), L₁.mul t₁ x x = x → x = L₁.one t₁ := by
    intro t₁ x hxx
    calc x = L₁.mul t₁ (L₁.mul t₁ (L₁.inv t₁ x) x) x := by rw [L₁.inv_mul_cancel, L₁.one_mul]
      _ = L₁.mul t₁ (L₁.inv t₁ x) (L₁.mul t₁ x x) := by rw [L₁.mul_assoc]
      _ = L₁.one t₁ := by rw [hxx, L₁.inv_mul_cancel]
  have h := hLa T t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact congrArg Subtype.val (key ⟨(L.one t).1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
    (Subtype.ext h.symm))

theorem one_coe_eq_comp_one {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

section Sections

variable {R R₁ : Type u} [CommRing R] [CommRing R₁]

@[reassoc]
theorem rigSection_fst {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.fst c t = t ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rigSection_snd {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  pullback.lift_snd _ _ _

theorem rigSection_fst_comp {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ (pullback.fst c t ≫ c) = t := by
  rw [← Category.assoc, rigSection_fst, Category.assoc, ε.2, Category.comp_id]

variable {A T A₁ X₁ : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (g₁ : X₁ ⟶ Spec (CommRingCat.of R₁))
  (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₁))) f₁)
  (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₁)) (a : A ⟶ A₁) (u : T ⟶ X₁)
  (e₁ : f ≫ ι = a ≫ f₁) (e₂ : t ≫ ι = u ≫ g₁) (hε : ε.1 ≫ a = ι ≫ ε₁.1)

include hε in

theorem rigSection_comp_pullbackMap :
    rigSection f t ε ≫ pullback.map f t f₁ g₁ a u ι e₁ e₂ = u ≫ rigSection f₁ g₁ ε₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, rigSection_fst_assoc, Category.assoc, hε, ← Category.assoc, e₂,
      Category.assoc, rigSection_fst]
  · rw [Category.assoc, pullback.lift_snd, rigSection_snd_assoc, Category.assoc, rigSection_snd, Category.comp_id]

include hε in

theorem rigSection_comp_eq_comp_pullbackMap_rigSection
    (d : pullback f t ⟶ pullback (pullback.fst f₁ g₁ ≫ f₁) ι) (v : T ⟶ pullback g₁ ι)
    (hd₁ : d ≫ pullback.fst _ _ = pullback.map f t f₁ g₁ a u ι e₁ e₂) (hd₂ : d ≫ pullback.snd _ _ = pullback.fst f t ≫ f)
    (hv₁ : v ≫ pullback.fst _ _ = u) (hv₂ : v ≫ pullback.snd _ _ = t)
    (e₃ : g₁ ≫ 𝟙 _ = rigSection f₁ g₁ ε₁ ≫ (pullback.fst f₁ g₁ ≫ f₁)) (e₄ : ι ≫ 𝟙 _ = 𝟙 _ ≫ ι) :
    rigSection f t ε ≫ d =
      v ≫ pullback.map g₁ ι (pullback.fst f₁ g₁ ≫ f₁) ι (rigSection f₁ g₁ ε₁) (𝟙 _) (𝟙 _) e₃ e₄ := by
  apply pullback.hom_ext
  · rw [Category.assoc, hd₁, rigSection_comp_pullbackMap f t ε f₁ g₁ ε₁ ι a u e₁ e₂ hε, Category.assoc,
      pullback.lift_fst, ← Category.assoc, hv₁]
  · rw [Category.assoc, hd₂, rigSection_fst_comp, Category.assoc, pullback.lift_snd, Category.comp_id, hv₂]

end Sections

section Modules

theorem nonempty_pullback_pullback_iso_unit {U XR Q P : Scheme.{u}} (eU : U ≅ XR) (e : Q ≅ P) (r : U ⟶ Q) (sR : XR ⟶ P)
    (h : eU.hom ≫ sR = r ≫ e.hom) (N : Q.Modules)
    (hN : Nonempty ((Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit U.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback sR).obj ((Scheme.Modules.pullback e.inv).obj N) ≅
      SheafOfModules.unit XR.ringCatSheaf) := by
  have h' : sR ≫ e.inv = eU.inv ≫ r := by
    rw [← cancel_epi eU.hom, ← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id, eU.hom_inv_id_assoc]
  exact ⟨(Scheme.Modules.pullbackComp sR e.inv).app N ≪≫ (Scheme.Modules.pullbackCongr h').app N ≪≫
    ((Scheme.Modules.pullbackComp eU.inv r).app N).symm ≪≫ (Scheme.Modules.pullback eU.inv).mapIso hN.some ≪≫
    Scheme.Modules.pullbackUnitIso eU.inv⟩

theorem nonempty_iso_pullback {X P P' : Scheme.{u}} (e : X ≅ P) (cX : P ⟶ P') (gA : X ⟶ P')
    (hgA : gA = e.hom ≫ cX) (M' : P'.Modules) (N : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback cX).obj M' ≅ (Scheme.Modules.pullback e.inv).obj N)) :
    Nonempty (N ≅ (Scheme.Modules.pullback gA).obj M') := by
  obtain ⟨e₁⟩ := h
  exact ⟨((Scheme.Modules.pullbackCongr hgA).app M' ≪≫ ((Scheme.Modules.pullbackComp e.hom cX).app M').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso e₁ ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N).symm⟩

end Modules

section Cube

variable {R R' : Type u} [CommRing R] [CommRing R']
  {Aj : Scheme.{u}} (fj : Aj ⟶ Spec (CommRingCat.of R))
  {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of R'))
  (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (a : A' ⟶ Aj) (ha : IsPullback a f' fj ι')

abbrev sqMap : pullback f' f' ⟶ pullback fj fj := pullback.map f' f' fj fj a a ι' ha.w.symm ha.w.symm

theorem sqMap_prodStr : prodStr f' f' ≫ ι' = sqMap fj f' ι' a ha ≫ prodStr fj fj := by
  have h1 : sqMap fj f' ι' a ha ≫ pullback.fst fj fj = pullback.fst f' f' ≫ a := pullback.lift_fst _ _ _
  show (pullback.fst f' f' ≫ f') ≫ ι' = sqMap fj f' ι' a ha ≫ pullback.fst fj fj ≫ fj
  rw [Category.assoc, ← Category.assoc (sqMap fj f' ι' a ha), h1, Category.assoc, ha.w]

theorem isPullback_sqMap : IsPullback (sqMap fj f' ι' a ha) (prodStr f' f') (prodStr fj fj) ι' :=
  AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback fj fj ι' f' f' a a ha ha

abbrev cubeMap : pullback (prodStr f' f') f' ⟶ pullback (prodStr fj fj) fj :=
  pullback.map (prodStr f' f') f' (prodStr fj fj) fj (sqMap fj f' ι' a ha) a ι' (sqMap_prodStr fj f' ι' a ha) ha.w.symm

theorem isPullback_cubeMap :
    IsPullback (cubeMap fj f' ι' a ha) (pullback.fst (prodStr f' f') f' ≫ prodStr f' f')
      (pullback.fst (prodStr fj fj) fj ≫ prodStr fj fj) ι' :=
  AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (prodStr fj fj) fj ι' (prodStr f' f') f'
    (sqMap fj f' ι' a ha) a (isPullback_sqMap fj f' ι' a ha) ha

end Cube

section CubeUnit

variable {R R' : Type u} [CommRing R] [CommRing R']
  {Aj : Scheme.{u}} (fj : Aj ⟶ Spec (CommRingCat.of R))
  {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
  (a : A' ⟶ Aj) (ha : IsPullback a f' fj (Spec.map (CommRingCat.ofHom φ)))

theorem prod_one_coe_comp_sqMap (L' : RelativeGroupLaw R' f') (Lj : RelativeGroupLaw R fj)
    (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t f'),
      (L'.mul t P Q).1 ≫ a = (Lj.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    ((L'.prod L').one t).1 ≫ sqMap fj f' (Spec.map (CommRingCat.ofHom φ)) a ha =
      ((Lj.prod Lj).one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h1 : (L'.one t).1 ≫ a = (Lj.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := one_comp_eq_one L' Lj φ a ha hLa t
  rw [RelativeGroupLaw.prod_one, RelativeGroupLaw.prod_one]
  show pullback.lift (L'.one t).1 (L'.one t).1 _ ≫ pullback.map f' f' fj fj a a _ _ _ =
    pullback.lift (Lj.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 (Lj.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, h1]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, h1]

end CubeUnit

end CubeDescentAux

end

open CubeDescentAux

theorem solution
    (k : Type v) [CommRing k] [IsNoetherianRing k]
    {S : Type u} [CommRing S] [Algebra k S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (T : Subalgebra k S) (hT : T.FG)
    (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥T))
    (L₁ : RelativeGroupLaw ↥T f₁) (a₁ : A ⟶ A₁)
    (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))))
    (hA₁ : AbelianSchemePropertyBundle ↥T f₁)
    (hLa₁ : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1) :
    ∃ (S₁ : Subalgebra k S) (_ : S₁.FG)
      (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (_ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (_ : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁)))) f₁),
      Nonempty (M.L ≅ (Scheme.Modules.pullback
        (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L) := by
  classical

  haveI := hA₁.proper
  haveI : Nonempty (FGStages.Idx T) := FGStages.nonempty T hT

  have hLa₁' : ∀ (T' : Scheme.{u}) (t : T' ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1 := fun T' t P Q => hLa₁ t P Q

  haveI hqc : QuasiCompact (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) := inferInstance
  haveI hqs : QuasiSeparated (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) := inferInstance

  have hs₁ : rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 _)) ≫ (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) = f₁ :=
    rigSection_fst_comp _ _ _

  have hε₁ : ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ sqMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T S)) ≫ ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥T)))).1 := by
    rw [prod_one_coe_comp_sqMap f₁ f _ a₁ ha₁ L L₁ hLa₁', one_coe_eq_comp_one (L₁.prod L₁), Category.id_comp]

  have hc₁ := isPullback_cubeMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁
  have h𝓛 := M.isInvertible.pullback hc₁.isoPullback.inv
  have hsq₁ : ha₁.isoPullback.hom ≫ pullback.map f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        (rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 _))) (𝟙 _) (𝟙 _)
        (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) =
      rigSection (prodStr f f) f ((L.prod L).one (𝟙 _)) ≫ hc₁.isoPullback.hom :=
    (rigSection_comp_eq_comp_pullbackMap_rigSection (prodStr f f) f ((L.prod L).one (𝟙 _)) (prodStr f₁ f₁) f₁
      ((L₁.prod L₁).one (𝟙 _)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
      (sqMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁) a₁
      (sqMap_prodStr f₁ f _ a₁ ha₁) ha₁.w.symm hε₁
      hc₁.isoPullback.hom ha₁.isoPullback.hom (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])).symm
  have htriv := nonempty_pullback_pullback_iso_unit ha₁.isoPullback hc₁.isoPullback _ _ hsq₁ _ M.rigidified

  obtain ⟨k, hik, 𝓛k, h𝓛k, ⟨erig⟩, hcmp⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
      (FGStages.φ T) (FGStages.g T) (FGStages.isDirectLimit T hT) (⟨T, hT, le_rfl⟩ : FGStages.Idx T)
      (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) f₁ (rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 _))) hs₁ _ h𝓛 htriv

  obtain ⟨A₂, f₂, L₂, hA₂, a₂, ha₂, b, hb, hab, hLa₂, hLb⟩ :=
    ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.GroupModelRefinement.solution L
      (algebraMap ↥T S) (FGStages.g T k) (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik)
      (FGStages.g_comp_φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik) A₁ f₁ L₁ hA₁ a₁ ha₁ hLa₁'

  have hc₂ := isPullback_cubeMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik))) b hb
  have hε₂ : ((L₂.prod L₂).one (𝟙 _)).1 ≫ sqMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik))) b hb =
      Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik)) ≫ ((L₁.prod L₁).one (𝟙 _)).1 := by
    rw [prod_one_coe_comp_sqMap f₁ f₂ _ b hb L₂ L₁ hLb, one_coe_eq_comp_one (L₁.prod L₁), Category.id_comp]
  have hsq₂ := rigSection_comp_eq_comp_pullbackMap_rigSection (prodStr f₂ f₂) f₂ ((L₂.prod L₂).one (𝟙 _)) (prodStr f₁ f₁) f₁
      ((L₁.prod L₁).one (𝟙 _)) (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik)))
      (sqMap f₁ f₂ _ b hb) b (sqMap_prodStr f₁ f₂ _ b hb) hb.w.symm hε₂
      hc₂.isoPullback.hom hb.isoPullback.hom (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

  refine ⟨k.1, k.2.1, A₂, f₂, L₂, hA₂, a₂, ha₂, hLa₂,
    { L := (Scheme.Modules.pullback hc₂.isoPullback.hom).obj 𝓛k
      isInvertible := h𝓛k.pullback _
      rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app 𝓛k ≪≫ (Scheme.Modules.pullbackCongr hsq₂).app 𝓛k ≪≫
        ((Scheme.Modules.pullbackComp _ _).app 𝓛k).symm ≪≫ (Scheme.Modules.pullback hb.isoPullback.hom).mapIso erig ≪≫
        Scheme.Modules.pullbackUnitIso _⟩ }, ?_⟩

  have hsq : sqMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫
      sqMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik))) b hb =
      sqMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hab]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hab]
  have hmap : cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫
      cubeMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik))) b hb =
      cubeMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hsq]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hab]
  have h₁ : (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫ hc₂.isoPullback.hom) ≫
      pullback.fst _ _ = pullback.fst _ _ := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, hmap]
    rw [Iso.inv_comp_eq]
    exact hc₁.isoPullback_hom_fst.symm
  have h₂ : (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫ hc₂.isoPullback.hom) ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (FGStages.g T k)) := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_fst_assoc,
      ← sqMap_prodStr f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂]
    rw [Iso.inv_comp_eq, hc₁.isoPullback_hom_snd_assoc, Category.assoc]
    rfl
  have key := nonempty_iso_pullback hc₁.isoPullback
    (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫ hc₂.isoPullback.hom) _
    (Iso.hom_inv_id_assoc _ _).symm 𝓛k _ (hcmp _ h₁ h₂)
  exact ⟨key.some ≪≫ ((Scheme.Modules.pullbackComp _ _).app 𝓛k).symm⟩
#print axioms solution
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeModelDescent


/-! Universe-polymorphic adaptation of S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback. -/
namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesBaseChange

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

noncomputable section

namespace FBC

open AlgebraicGeometry.Scheme.Modules

section lociso
variable {S' : Type u} [CommRing S'] {X Y Z : Scheme.{u}}

theorem locIsoOnBase_of_iso (q : X ⟶ Spec (CommRingCat.of S')) {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem locIsoOnBase_unit_congr (q : X ⟶ Spec (CommRingCat.of S')) {M M' : X.Modules} (e : M ≅ M') :
    LocIsoOnBase q M (𝟙_ _) ↔ LocIsoOnBase q M' (𝟙_ _) :=
  ⟨fun h => (LocIsoOnBase.equivalence q).trans (locIsoOnBase_of_iso q e.symm) h,
   fun h => (LocIsoOnBase.equivalence q).trans (locIsoOnBase_of_iso q e) h⟩

def pullbackCompCongr {φ : X ⟶ Y} {ψ : Y ⟶ Z} {χ : X ⟶ Z} (h : φ ≫ ψ = χ) (M : Z.Modules) :
    (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj M) ≅ (Scheme.Modules.pullback χ).obj M :=
  (pullbackComp φ ψ).app M ≪≫ (pullbackCongr h).app M

theorem locIsoOnBase_unit_iff_of_iso (e : X ≅ Y) (qX : X ⟶ Spec (CommRingCat.of S')) (qY : Y ⟶ Spec (CommRingCat.of S'))
    (he : e.hom ≫ qY = qX) (K : Y.Modules) :
    LocIsoOnBase qX ((Scheme.Modules.pullback e.hom).obj K) (𝟙_ _) ↔ LocIsoOnBase qY K (𝟙_ _) := by
  constructor
  · intro h
    have h' := LocIsoOnBase.pullback_of_comp_eq qY e.inv (𝟙 _) (by rw [Category.comp_id, ← he, e.inv_hom_id_assoc]) h
    have eK : (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj K) ≅ K :=
      pullbackCompCongr e.inv_hom_id K ≪≫ (pullbackId _).app K
    exact (LocIsoOnBase.equivalence qY).trans ((LocIsoOnBase.equivalence qY).trans (locIsoOnBase_of_iso qY eK.symm) h')
      (locIsoOnBase_of_iso qY (pullbackTensorUnitObjIso e.inv))
  · intro h
    have h' := LocIsoOnBase.pullback_of_comp_eq qX e.hom (𝟙 _) (by rw [Category.comp_id, he]) h
    exact (LocIsoOnBase.equivalence qX).trans h' (locIsoOnBase_of_iso qX (pullbackTensorUnitObjIso e.hom))

end lociso

section square

variable {S₁ : Type u} [CommRing S₁] {A₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
  {S : Type u} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

theorem one_coe_eq {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : (G.one t).1 = t ≫ (G.one (𝟙 _)).1 :=
  (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id t))).symm

include hLa in

theorem one_comp_a {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  let E : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f₁ :=
    ⟨(L.one t).1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
  have hE : L₁.mul _ E E = E := by
    have h := hLa T t (L.one t) (L.one t)
    rw [L.one_mul] at h
    exact (Subtype.ext h).symm
  have : E = L₁.one _ := by
    calc E = L₁.mul _ (L₁.one _) E := (L₁.one_mul _ E).symm
    _ = L₁.mul _ (L₁.mul _ (L₁.inv _ E) E) E := by rw [L₁.inv_mul_cancel]
    _ = L₁.mul _ (L₁.inv _ E) (L₁.mul _ E E) := L₁.mul_assoc _ _ _ _
    _ = L₁.mul _ (L₁.inv _ E) E := by rw [hE]
    _ = L₁.one _ := L₁.inv_mul_cancel _ E
  exact congrArg Subtype.val this

def aa : pullback f f ⟶ pullback f₁ f₁ :=
  pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm

@[scoped simp] theorem aa_fst : aa φ a ha ≫ pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
@[scoped simp] theorem aa_snd : aa φ a ha ≫ pullback.snd f₁ f₁ = pullback.snd f f ≫ a := pullback.lift_snd _ _ _

theorem aa_prodStr : aa φ a ha ≫ prodStr f₁ f₁ = prodStr f f ≫ Spec.map (CommRingCat.ofHom φ) := by
  change aa φ a ha ≫ pullback.fst f₁ f₁ ≫ f₁ = (pullback.fst f f ≫ f) ≫ _
  rw [← Category.assoc, aa_fst, Category.assoc, Category.assoc, ha.w]

def aaa : pullback (prodStr f f) f ⟶ pullback (prodStr f₁ f₁) f₁ :=
  pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm

@[scoped simp] theorem aaa_fst : aaa φ a ha ≫ pullback.fst (prodStr f₁ f₁) f₁ = pullback.fst (prodStr f f) f ≫ aa φ a ha :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem aaa_snd : aaa φ a ha ≫ pullback.snd (prodStr f₁ f₁) f₁ = pullback.snd (prodStr f f) f ≫ a :=
  pullback.lift_snd _ _ _

def θ : pullback f f ≅ pullback (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)) where
  hom := pullback.lift (aa φ a ha) (prodStr f f) (aa_prodStr φ a ha)
  inv := pullback.lift
    (ha.lift (pullback.fst _ _ ≫ pullback.fst f₁ f₁) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition))
    (ha.lift (pullback.fst _ _ ≫ pullback.snd f₁ f₁) (pullback.snd _ _)
      (by rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact pullback.condition))
    (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply ha.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, aa_fst]
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_snd]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      apply ha.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, aa_snd]
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_snd]; exact pullback.condition (f := f) (g := f)
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
      · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      change _ ≫ pullback.fst f f ≫ f = _
      rw [pullback.lift_fst_assoc, IsPullback.lift_snd]

theorem θ_hom_fst : (θ φ a ha).hom ≫ pullback.fst _ _ = aa φ a ha := pullback.lift_fst _ _ _
theorem θ_hom_snd : (θ φ a ha).hom ≫ pullback.snd _ _ = prodStr f f := pullback.lift_snd _ _ _

include hLa in

theorem one_prodStr_comp_a : (L.one (prodStr f f)).1 ≫ a = aa φ a ha ≫ (L₁.one (prodStr f₁ f₁)).1 := by
  rw [one_comp_a L₁ φ L a ha hLa, one_coe_eq L₁ (prodStr f f ≫ _), one_coe_eq L₁ (prodStr f₁ f₁), ← Category.assoc,
    aa_prodStr]

end square

section faces

variable {S₁ : Type u} [CommRing S₁] {A₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
  {S : Type u} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

def F1 {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift
    (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2]))
    (pullback.snd g g)
    (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition)

def F2 {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift
    (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2]))
    (pullback.snd g g)
    (by rw [pullback.lift_fst_assoc]; exact pullback.condition)

def F3 {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2])

include hLa in
theorem F1_comp : F1 L ≫ aaa φ a ha = aa φ a ha ≫ F1 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F1
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst, one_prodStr_comp_a L₁ φ L a ha hLa]
    · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd, aa_fst]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F1
    rw [pullback.lift_snd_assoc, pullback.lift_snd, aa_snd]

include hLa in
theorem F2_comp : F2 L ≫ aaa φ a ha = aa φ a ha ≫ F2 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F2
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst, aa_fst]
    · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd, one_prodStr_comp_a L₁ φ L a ha hLa]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F2
    rw [pullback.lift_snd_assoc, pullback.lift_snd, aa_snd]

include hLa in
theorem F3_comp : F3 L ≫ aaa φ a ha = aa φ a ha ≫ F3 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F3
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F3
    rw [pullback.lift_snd_assoc, pullback.lift_snd, one_prodStr_comp_a L₁ φ L a ha hLa]

def faceIso {F : pullback f f ⟶ pullback (prodStr f f) f} {F₁ : pullback f₁ f₁ ⟶ pullback (prodStr f₁ f₁) f₁}
    (hF : F ≫ aaa φ a ha = aa φ a ha ≫ F₁) (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    (Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback (aaa φ a ha)).obj N) ≅
      (Scheme.Modules.pullback (θ φ a ha).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback F₁).obj N)) :=
  pullbackCompCongr hF N ≪≫ (pullbackCompCongr rfl N).symm ≪≫ (pullbackCompCongr (θ_hom_fst φ a ha) _).symm

include hLa in
theorem face_iff {F : pullback f f ⟶ pullback (prodStr f f) f} {F₁ : pullback f₁ f₁ ⟶ pullback (prodStr f₁ f₁) f₁}
    (hF : F ≫ aaa φ a ha = aa φ a ha ≫ F₁) (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    LocIsoOnBase (prodStr f f) ((Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback (aaa φ a ha)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback F₁).obj N)) (𝟙_ _) :=
  (locIsoOnBase_unit_congr _ (faceIso φ a ha hF N)).trans
    (locIsoOnBase_unit_iff_of_iso (θ φ a ha) _ _ (θ_hom_snd φ a ha) _)

end faces

end FBC

open FBC in
theorem solution
    {S₁ : Type u} [CommRing S₁] {A₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
    {S : Type u} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L₁.one (prodStr f₁ f₁)).1 (pullback.fst f₁ f₁) (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc, (L₁.one _).2]; exact pullback.condition))).obj N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f₁ f₁) (L₁.one (prodStr f₁ f₁)).1 (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L₁.one (prodStr f₁ f₁)).1 (by rw [Category.id_comp, (L₁.one _).2]))).obj N)) (𝟙_ _)) := by
  exact ⟨FBC.face_iff L₁ φ L a ha hLa (FBC.F1_comp L₁ φ L a ha hLa) N,
    FBC.face_iff L₁ φ L a ha hLa (FBC.F2_comp L₁ φ L a ha hLa) N,
    FBC.face_iff L₁ φ L a ha hLa (FBC.F3_comp L₁ φ L a ha hLa) N⟩
#print axioms solution
end
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesBaseChange


/-! Universe-polymorphic adaptation of S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_rigidified_cube_pullback_of_isPullback. -/
namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeRigidificationBaseChange

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

namespace CubeRigBC

variable {S₁ : Type u} [CommRing S₁] {A₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
  {S : Type u} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g) (hx : G.mul t x x = x) : x = G.one t := by
  have h1 := congrArg (G.mul t (G.inv t x)) hx
  rwa [← G.mul_assoc, G.inv_mul_cancel, G.one_mul] at h1

include ha hLa in

theorem one_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h := hLa T t (L.one t) (L.one t)
  rw [L.one_mul] at h

  have hx := eq_one_of_mul_self L₁ (t ≫ Spec.map (CommRingCat.ofHom φ))
    ⟨(L.one t).1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩ (Subtype.ext h.symm)
  exact congrArg Subtype.val hx

include ha hLa in

theorem f_one_a : f ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ a =
    a ≫ f₁ ≫ (L₁.one (𝟙 (Spec (CommRingCat.of S₁)))).1 := by
  have hL : (L.one f).1 = f ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S))) f f (Category.comp_id f)
    rw [← this]; rfl
  have hL₁ : (L₁.one (a ≫ f₁)).1 = a ≫ f₁ ≫ (L₁.one (𝟙 (Spec (CommRingCat.of S₁)))).1 := by
    have := L₁.one_natural (𝟙 (Spec (CommRingCat.of S₁))) (a ≫ f₁) (a ≫ f₁) (Category.comp_id _)
    rw [← this]; rfl
  have key : (L₁.one (f ≫ Spec.map (CommRingCat.ofHom φ))).1 = (L₁.one (a ≫ f₁)).1 := by
    rw [ha.w]
  rw [← Category.assoc, ← hL, one_comp L₁ φ L a ha hLa f, key, hL₁]

noncomputable abbrev a3 : pullback (prodStr f f) f ⟶ pullback (prodStr f₁ f₁) f₁ :=
  pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
    (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
    a (Spec.map (CommRingCat.ofHom φ))
    (by
      have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
          pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
      show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
        pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
          pullback.fst f₁ f₁ ≫ f₁
      rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
    ha.w.symm

include hLa in

theorem rigSection_comp_a3 :
    rigSection (prodStr f f) f ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) ≫ a3 φ a ha =
      a ≫ rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of S₁)))) := by
  have hone := f_one_a L₁ φ L a ha hLa
  apply pullback.hom_ext
  ·
    rw [Category.assoc, pullback.lift_fst, Category.assoc]
    unfold rigSection
    rw [pullback.lift_fst_assoc, pullback.lift_fst, RelativeGroupLaw.prod_one, RelativeGroupLaw.prod_one,
      prodPairPt_coe, prodPairPt_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, hone]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, hone]
  ·
    rw [Category.assoc, pullback.lift_snd, Category.assoc]
    unfold rigSection
    rw [pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

end CubeRigBC

open CubeRigBC in
theorem solution
    {S₁ : Type u} [CommRing S₁] {A₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
    {S : Type u} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of S₁)))) f₁) :
    ∃ M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f,
      M.L = (Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L :=
  ⟨{ L := (Scheme.Modules.pullback (a3 φ a ha)).obj M₁.L
     isInvertible := M₁.isInvertible.pullback _
     rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M₁.L ≪≫
        (Scheme.Modules.pullbackCongr (rigSection_comp_a3 L₁ φ L a ha hLa)).app M₁.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app M₁.L).symm ≪≫
        (Scheme.Modules.pullback a).mapIso M₁.rigidified.some ≪≫
        Scheme.Modules.pullbackUnitIso a⟩ }, rfl⟩
#print axioms solution
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeRigidificationBaseChange


/-! Universe-polymorphic adaptation of S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces. -/
namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesDescent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

namespace CFDStages

variable {A₀ : Type v} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type u := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type u := ↥i.1

def φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

def g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl
theorem g_comp_φ (i j : Idx B) (h : i ≤ j) : (g B j).comp (φ B i j h) = g B i := rfl

instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

def sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

end CFDStages

namespace CFDAsm

theorem ofIso {S' : Type u} [CommRing S'] {Q : Scheme.{u}} (q : Q ⟶ Spec (CommRingCat.of S')) {M M' : Q.Modules}
    (e : M ≅ M') : LocIsoOnBase q M M' := fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem rebase {S₁ : Type u} [CommRing S₁] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of S₁))
    {R R' : Type u} [CommRing R] [CommRing R'] (s : S₁ →+* R) (s' : S₁ →+* R') (t : R →+* R') (ht : t.comp s = s')
    (N : X.Modules)
    (h : LocIsoOnBase (pullback.snd fX (Spec.map (CommRingCat.ofHom s)))
      ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom s)))).obj N) (𝟙_ _)) :
    LocIsoOnBase (pullback.snd fX (Spec.map (CommRingCat.ofHom s')))
      ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom s')))).obj N) (𝟙_ _) := by
  have hs : Spec.map (CommRingCat.ofHom t) ≫ Spec.map (CommRingCat.ofHom s) = Spec.map (CommRingCat.ofHom s') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ht]
  let ρ : pullback fX (Spec.map (CommRingCat.ofHom s')) ⟶ pullback fX (Spec.map (CommRingCat.ofHom s)) :=
    pullback.lift (pullback.fst fX _) (pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom t))
      (by rw [pullback.condition, Category.assoc, hs])
  have hρ₁ : ρ ≫ pullback.fst fX _ = pullback.fst fX _ := pullback.lift_fst _ _ _
  have hρ₂ : ρ ≫ pullback.snd fX _ = pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom t) := pullback.lift_snd _ _ _
  have h' := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (pullback.snd fX (Spec.map (CommRingCat.ofHom s'))) ρ
    (Spec.map (CommRingCat.ofHom t)) hρ₂ h
  have EQ := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd fX (Spec.map (CommRingCat.ofHom s')))
  refine EQ.trans (EQ.trans (ofIso _ ?_) h') (ofIso _ (Scheme.Modules.pullbackTensorUnitObjIso ρ))
  exact ((Scheme.Modules.pullbackComp ρ _).app N ≪≫ (Scheme.Modules.pullbackCongr hρ₁).app N).symm

end CFDAsm

open CFDStages CFDAsm in
theorem solution
    (k₀ : Type v) [CommRing k₀] [IsNoetherianRing k₀]
    {S : Type u} [CommRing S] [Algebra k₀ S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _))
    (S₁ : Subalgebra k₀ S) (hS₁ : S₁.FG)
      (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (hA₁ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (hLa : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁)))) f₁)
    (hM : Nonempty (M.L ≅ (Scheme.Modules.pullback
        (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L)) :
    ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : IsNoetherianRing S₀) (A₀ : Scheme) (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀))
      (L₀ : RelativeGroupLaw S₀ f₀) (_ : AbelianSchemePropertyBundle S₀ f₀)
      (M₀ : RigidifiedLineBundle (prodStr f₀ f₀) ((L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀),
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (L₀.one (prodStr f₀ f₀)).1 (pullback.fst f₀ f₀) (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc, (L₀.one _).2]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst f₀ f₀) (L₀.one (prodStr f₀ f₀)).1 (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) (L₀.one (prodStr f₀ f₀)).1 (by rw [Category.id_comp, (L₀.one _).2]))).obj M₀.L) (𝟙_ _) ∧
      (Nonempty (M₀.L ≅ (RigidifiedLineBundle.unit (c := prodStr f₀ f₀) (ε := (L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀).L) →
        Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f).L)) := by
  classical
  obtain ⟨eM⟩ := hM
  haveI : IsProper f₁ := hA₁.proper
  haveI : QuasiCompact (prodStr f₁ f₁) := inferInstance
  haveI : QuasiSeparated (prodStr f₁ f₁) := inferInstance

  haveI hne : Nonempty (Idx S₁) := nonempty S₁ hS₁
  have hDL := isDirectLimit S₁ hS₁
  let i₀ : Idx S₁ := ⟨S₁, hS₁, le_rfl⟩

  have hF := ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesBaseChange.solution L₁ S₁.val.toRingHom L a ha hLa M₁.L
  have EQ := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (prodStr f f)
  have d₁ := hF.1.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₁)
  have d₂ := hF.2.1.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₂)
  have d₃ := hF.2.2.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₃)

  obtain ⟨k₁, hk₁, e₁⟩ :=
    AlgebraicGeometry.Polarisation.exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₁
  obtain ⟨k₂, hk₂, e₂⟩ :=
    AlgebraicGeometry.Polarisation.exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₂
  obtain ⟨k₃, hk₃, e₃⟩ :=
    AlgebraicGeometry.Polarisation.exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₃

  obtain ⟨k₁₂, h₁, h₂'⟩ := exists_ge_ge k₁ k₂
  obtain ⟨k, h₁₂, h₃'⟩ := exists_ge_ge k₁₂ k₃
  have hk : i₀ ≤ k := hk₁.trans (h₁.trans h₁₂)
  have r₁ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₁ hk₁) (φ S₁ i₀ k hk) (φ S₁ k₁ k (h₁.trans h₁₂)) rfl _ e₁
  have r₂ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₂ hk₂) (φ S₁ i₀ k hk) (φ S₁ k₂ k (h₂'.trans h₁₂)) rfl _ e₂
  have r₃ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₃ hk₃) (φ S₁ i₀ k hk) (φ S₁ k₃ k h₃') rfl _ e₃

  let S₀ : Type u := G S₁ k
  haveI : IsNoetherianRing S₀ := by
    haveI : Algebra.FiniteType k₀ ↥k.1 := (Subalgebra.fg_iff_finiteType _).mp k.2.1
    exact Algebra.FiniteType.isNoetherianRing k₀ ↥k.1
  let σ : Spec (CommRingCat.of S₀) ⟶ Spec (CommRingCat.of ↥S₁) := Spec.map (CommRingCat.ofHom (φ S₁ i₀ k hk))
  let f₀ : pullback f₁ σ ⟶ Spec (CommRingCat.of S₀) := pullback.snd f₁ σ
  let L₀ : RelativeGroupLaw S₀ f₀ := L₁.baseChange σ
  have ha₀ : IsPullback (pullback.fst f₁ σ) f₀ f₁ σ := IsPullback.of_hasPullback f₁ σ
  have hA₀ : AbelianSchemePropertyBundle S₀ f₀ := GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback hA₁ ha₀
  have hLa₀ : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ pullback.fst f₁ σ = (L₁.mul (t ≫ σ)
        ⟨P.1 ≫ pullback.fst f₁ σ, by rw [Category.assoc, ha₀.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f₁ σ, by rw [Category.assoc, ha₀.w, ← Category.assoc, Q.2]⟩).1 :=
    fun T t P Q => congrArg Subtype.val (L₁.baseChangePointToBase_mul σ t P Q)
  obtain ⟨M₀, hM₀⟩ := ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeRigidificationBaseChange.solution
    L₁ (φ S₁ i₀ k hk) L₀ (pullback.fst f₁ σ) ha₀ hLa₀ M₁
  have hF₀ := ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesBaseChange.solution
    L₁ (φ S₁ i₀ k hk) L₀ (pullback.fst f₁ σ) ha₀ hLa₀ M₁.L
  refine ⟨S₀, inferInstance, inferInstance, pullback f₁ σ, f₀, L₀, hA₀, M₀, ?_, ?_, ?_, ?_⟩
  · rw [hM₀]; exact hF₀.1.mpr r₁
  · rw [hM₀]; exact hF₀.2.1.mpr r₂
  · rw [hM₀]; exact hF₀.2.2.mpr r₃
  ·
    rintro ⟨e₀⟩
    have hσ : Spec.map (CommRingCat.ofHom (g S₁ k)) ≫ σ = Spec.map (CommRingCat.ofHom S₁.val.toRingHom) := by
      show Spec.map (CommRingCat.ofHom (g S₁ k)) ≫ Spec.map (CommRingCat.ofHom (φ S₁ i₀ k hk)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    let ψ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of S₀) := Spec.map (CommRingCat.ofHom (g S₁ k))
    let c : A ⟶ pullback f₁ σ := pullback.lift a (f ≫ ψ) (by rw [Category.assoc, hσ]; exact ha.w)
    have hc₁ : c ≫ pullback.fst f₁ σ = a := pullback.lift_fst _ _ _
    have hc₂ : c ≫ f₀ = f ≫ ψ := pullback.lift_snd _ _ _
    let cc : pullback f f ⟶ pullback f₀ f₀ := pullback.map f f f₀ f₀ c c ψ hc₂.symm hc₂.symm
    have hcc₁ : cc ≫ pullback.fst f₀ f₀ = pullback.fst f f ≫ c := pullback.lift_fst _ _ _
    have hcc₂ : cc ≫ pullback.snd f₀ f₀ = pullback.snd f f ≫ c := pullback.lift_snd _ _ _
    let γ : pullback (prodStr f f) f ⟶ pullback (prodStr f₀ f₀) f₀ :=
      pullback.map (prodStr f f) f (prodStr f₀ f₀) f₀ cc c ψ
        (by
          show (pullback.fst f f ≫ f) ≫ ψ = cc ≫ pullback.fst f₀ f₀ ≫ f₀
          rw [← Category.assoc, hcc₁, Category.assoc, Category.assoc, hc₂])
        hc₂.symm
    have hγ₁ : γ ≫ pullback.fst (prodStr f₀ f₀) f₀ = pullback.fst (prodStr f f) f ≫ cc := pullback.lift_fst _ _ _
    have hγ₂ : γ ≫ pullback.snd (prodStr f₀ f₀) f₀ = pullback.snd (prodStr f f) f ≫ c := pullback.lift_snd _ _ _

    let aa := pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm
    have haa₁ : aa ≫ pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
    have haa₂ : aa ≫ pullback.snd f₁ f₁ = pullback.snd f f ≫ a := pullback.lift_snd _ _ _
    let bb := pullback.map f₀ f₀ f₁ f₁ (pullback.fst f₁ σ) (pullback.fst f₁ σ) σ ha₀.w.symm ha₀.w.symm
    have hbb₁ : bb ≫ pullback.fst f₁ f₁ = pullback.fst f₀ f₀ ≫ pullback.fst f₁ σ := pullback.lift_fst _ _ _
    have hbb₂ : bb ≫ pullback.snd f₁ f₁ = pullback.snd f₀ f₀ ≫ pullback.fst f₁ σ := pullback.lift_snd _ _ _
    have hccbb : cc ≫ bb = aa := by
      apply pullback.hom_ext
      · rw [Category.assoc, hbb₁, ← Category.assoc, hcc₁, Category.assoc, hc₁, haa₁]
      · rw [Category.assoc, hbb₂, ← Category.assoc, hcc₂, Category.assoc, hc₁, haa₂]

    obtain ⟨AAA, hAAA₁, hAAA₂, ⟨hAAA⟩⟩ : ∃ AAA : pullback (prodStr f f) f ⟶ pullback (prodStr f₁ f₁) f₁,
        AAA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ aa ∧ AAA ≫ pullback.snd _ _ = pullback.snd _ _ ≫ a ∧
          Nonempty (M.L ≅ (Scheme.Modules.pullback AAA).obj M₁.L) :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ⟨eM⟩⟩
    obtain ⟨BBB, hBBB, hBBB₁, hBBB₂⟩ : ∃ BBB : pullback (prodStr f₀ f₀) f₀ ⟶ pullback (prodStr f₁ f₁) f₁,
        M₀.L = (Scheme.Modules.pullback BBB).obj M₁.L ∧ BBB ≫ pullback.fst _ _ = pullback.fst _ _ ≫ bb ∧
          BBB ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst f₁ σ :=
      ⟨_, hM₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have key : γ ≫ BBB = AAA := by
      apply pullback.hom_ext
      · rw [Category.assoc, hBBB₁, ← Category.assoc, hγ₁, Category.assoc, hccbb, hAAA₁]
      · rw [Category.assoc, hBBB₂, ← Category.assoc, hγ₂, Category.assoc, hc₁, hAAA₂]
    refine ⟨hAAA ≪≫ (Scheme.Modules.pullbackCongr key.symm).app M₁.L ≪≫ ((Scheme.Modules.pullbackComp γ BBB).app M₁.L).symm ≪≫
      (Scheme.Modules.pullback γ).mapIso (eqToIso hBBB.symm ≪≫ e₀) ≪≫ Scheme.Modules.pullbackUnitIso γ⟩
#print axioms solution
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.CubeFacesDescent

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard
theorem cubeTrivialOfGroupModel
    (k : Type v) [CommRing k] [IsNoetherianRing k]
    {S : Type u} [CommRing S] [Algebra k S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _))
    (T : Subalgebra k S) (hT : T.FG)
    (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥T))
    (L₁ : RelativeGroupLaw ↥T f₁) (a₁ : A ⟶ A₁)
    (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))))
    (hA₁ : AbelianSchemePropertyBundle ↥T f₁)
    (hLa₁ : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1) :
    Nonempty (M.L ≅ 𝟙_ _) := by
  obtain ⟨S₁, hS₁, A₂, f₂, L₂, hA₂, a₂, ha₂, hLa₂, M₂, hM₂⟩ :=
    CubeModelDescent.solution k L hA M T hT A₁ f₁ L₁ a₁ ha₁ hA₁ hLa₁
  obtain ⟨S₀, _, _, A₀, f₀, L₀, hA₀, M₀, h₀₁, h₀₂, h₀₃, hfinish⟩ :=
    CubeFacesDescent.solution k L hA M h₁ h₂ h₃ S₁ hS₁ A₂ f₂ L₂ hA₂ a₂ ha₂ hLa₂ M₂ hM₂
  exact hfinish
    (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.CubeTrivial.solution
      L₀ hA₀ M₀ h₀₁ h₀₂ h₀₃)

#print axioms cubeTrivialOfGroupModel
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaLocalWeierstrassR0203.FiniteTypeApproximation

/-- The accepted finite-type construction with its actual subalgebra retained,
so that further rigidified sheaf data can descend along the same directed system. -/
theorem framedSubalgebraModel
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (Q₀ : FramedCurve T) (π : Q.target ⟶ Q₀.target)
        (sq : IsPullback π Q.structureMap Q₀.structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap T R)))),
      ∀ {Z : Scheme.{u}} (t : Z ⟶ Base R) (x y : SchemeHomOver t Q.structureMap),
        (Q.law.mul t x y).val ≫ π =
          (Q₀.law.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap T R)))
            ⟨x.val ≫ π, by rw [Category.assoc, sq.w, ← Category.assoc, x.property]⟩
            ⟨y.val ≫ π, by rw [Category.assoc, sq.w, ← Category.assoc, y.property]⟩).val := by
  obtain ⟨T, hT, X, f, L, π, hp, hd, sq, ⟨frame⟩, hz, hm⟩ :=
    rational_framed_group_descent R Q
  letI := hp
  letI := hd
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℚ T
  let V : Set (PrimeSpectrum T) := {p | GeometricallyIrreducible (f.fiberToSpecResidueField p)}
  have hV : IsOpen V := by
    have heq : V = {p : Base T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : T →+* k),
        RingHom.ker x = p.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} := by
      ext p
      exact (AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
        f p).symm
    rw [heq]
    exact GoodFibreLocus.good_fibre_locus_open f
  have hRV : ∀ p : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap T R) p ∈ V := by
    intro p
    haveI := connected_fibre_at_scalar_image R Q (algebraMap T R) f π sq p
    haveI := AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom (algebraMap T R))) p))
    exact inferInstanceAs (GeometricallyIrreducible
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom (algebraMap T R))) p)))
  obtain ⟨U, hTU, hU, hUV⟩ := finite_stage_factors_open R T hT V hV hRV
  letI : Algebra T U := (Subalgebra.inclusion hTU).toRingHom.toAlgebra
  let c : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
  let b : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  let a : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  have hbc : b ≫ c = a := by
    dsimp [b, c, a]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let fU := pullback.snd f c
  let LU := L.baseChange c
  haveI : GeometricallyIrreducible fU := by
    rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
    intro q
    haveI : GeometricallyIrreducible (f.fiberToSpecResidueField (c q)) := hUV q
    exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
      (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f c) q) inferInstance
  haveI : GeometricallyConnected fU := GeometricallyIrreducible.geometricallyConnected fU
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 fU := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd f c))
  have hzU : (LU.one (𝟙 _)).val ≫ pullback.fst f c = c ≫ (L.one (𝟙 _)).val := by
    have h := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 (Base U)) ≫ c) c (by simp))
    simpa only [LU, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, GoodReductionJacobian.schemeHomOverComp_coe] using h.symm
  have frameU : Nonempty ((SheafOfModules.unit (Base U).ringCatSheaf : (Base U).Modules) ≅
      (Scheme.Modules.pullback (LU.one (𝟙 _)).val).obj fU.kaehler) := by
    exact ⟨(Scheme.Modules.pullbackUnitIso c).symm ≪≫ (Scheme.Modules.pullback c).mapIso frame ≪≫
      ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso
        f fU (pullback.fst f c) (IsPullback.of_hasPullback f c)
        (L.one (𝟙 _)).val (LU.one (𝟙 _)).val hzU⟩
  let π' : Q.target ⟶ pullback f c :=
    pullback.lift π (Q.structureMap ≫ b) (by rw [Category.assoc, hbc, sq.w])
  have sq' : IsPullback π' Q.structureMap fU b := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f c) (h₂₂ := c) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f c)
    rw [pullback.lift_fst, hbc]
    exact sq
  have hm' := multiplication_lift Q.law L a b c hbc π sq.w π'
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (fun Z t x y => (hm Z t x y _ _ rfl rfl).symm)
  have hz' : Q.zero ≫ π' = b ≫ (LU.one (𝟙 _)).val := by
    apply origin_eq_of_mul_eq Q.law LU b π' sq'.w
    intro Z t x y
    exact (hm' Z t x y _ _ rfl rfl).symm
  let model : FramedCurve U := {
    target := pullback f c
    structureMap := fU
    law := LU
    geometry := {
      smooth := inferInstance
      proper := inferInstanceAs (IsProper (pullback.snd f c))
      connectedFibres := fun q => fU.isConnected_preimage_singleton q
      hasGroupLaw := ⟨LU⟩ }
    dimension := inferInstance
    hodge := frameU }
  refine ⟨U, hU, model, π', sq', ?_⟩
  intro Z t x y
  exact (hm' Z t x y _ _ rfl rfl).symm

#print axioms framedSubalgebraModel
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard
open ArithmeticThetaLocalWeierstrassR0203

/-- Cube triviality on every framed rational family, with the model constructed
from the given family rather than supplied as a premise. -/
theorem framedCubeTrivial
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R)
    (M : RigidifiedLineBundle (prodStr Q.structureMap Q.structureMap)
      ((Q.law.prod Q.law).one (𝟙 (Spec (CommRingCat.of R)))) Q.structureMap)
    (h₁ : LocIsoOnBase (prodStr Q.structureMap Q.structureMap)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (Q.law.one (prodStr Q.structureMap Q.structureMap)).1 (pullback.fst Q.structureMap Q.structureMap) (by rw [(Q.law.one _).2]))
          (pullback.snd Q.structureMap Q.structureMap)
          (by rw [pullback.lift_fst_assoc, (Q.law.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr Q.structureMap Q.structureMap)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst Q.structureMap Q.structureMap) (Q.law.one (prodStr Q.structureMap Q.structureMap)).1 (by rw [(Q.law.one _).2]))
          (pullback.snd Q.structureMap Q.structureMap)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr Q.structureMap Q.structureMap)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (Q.law.one (prodStr Q.structureMap Q.structureMap)).1 (by rw [Category.id_comp, (Q.law.one _).2]))).obj M.L) (𝟙_ _))
    : Nonempty (M.L ≅ 𝟙_ _) := by
  obtain ⟨T, hT, Q₀, π, sq, hm⟩ := framedSubalgebraModel R Q
  exact cubeTrivialOfGroupModel ℚ Q.law Q.geometry M h₁ h₂ h₃
    T hT Q₀.target Q₀.structureMap Q₀.law π sq Q₀.geometry hm

open ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeGeometry.CubePBS

/-- The actual cube line of any invertible sheaf on a framed rational family is
trivial, without any Noetherian assumption on the given base ring. -/
theorem framedCubeLine
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R)
    (𝓛 : Q.target.Modules) (hL : Scheme.Modules.IsInvertible 𝓛) :
    letI := Q.law.grpObjOverMk
    Nonempty (N Q.structureMap 𝓛 (eG Q.structureMap Q.law) ≅ 𝟙_ _) := by
  letI := Q.law.grpObjOverMk
  exact framedCubeTrivial R Q (Nrig Q.structureMap Q.law 𝓛 hL)
    (locIsoOnBase_of_nonempty _ (slice_trivial Q.structureMap 𝓛
      (eG Q.structureMap Q.law) hL (σ₁ Q.structureMap Q.law)
      (pcls_σ₁ Q.structureMap Q.law 𝓛)))
    (locIsoOnBase_of_nonempty _ (slice_trivial Q.structureMap 𝓛
      (eG Q.structureMap Q.law) hL (σ₂ Q.structureMap Q.law)
      (pcls_σ₂ Q.structureMap Q.law 𝓛)))
    (locIsoOnBase_of_nonempty _ (slice_trivial Q.structureMap 𝓛
      (eG Q.structureMap Q.law) hL (σ₃ Q.structureMap Q.law)
      (pcls_σ₃ Q.structureMap Q.law 𝓛)))

#print axioms framedCubeTrivial
#print axioms framedCubeLine
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaLegendreAtlasR0176

/-- The affine doubled-torsion construction without a Noetherian restriction.
A local Hodge trivialization is used solely to construct a finite-type model;
the returned lift acts on the original differential theta line. -/
theorem framedAffineLift
    (R : Type u) [CommRing R] [Algebra ℚ R] (F : EllipticFamily R)
    (hframe : Nonempty ((𝟙_ (Spec (CommRingCat.of R)).Modules) ≅
      (Scheme.Modules.pullback (F.law.one (𝟙 _)).val).obj F.projection.kaehler))
    (m : ℕ) (hm : 0 < m)
    (P : ArithmeticThetaRelativeThetaLiftsR0255.point F)
    (hP : P.val ≫ F.law.schemeNsmul (2*m) = ArithmeticThetaRelativeThetaLiftsR0255.zero F) :
    Nonempty (ArithmeticThetaRelativeThetaLiftsR0255.Lift F m
      (ArithmeticThetaRelativeThetaLiftsR0255.translation F P)) := by
  let Q : FramedCurve R := {
    target := F.curve
    structureMap := F.projection
    law := F.law
    geometry := ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180.geometry F
    dimension := F.smooth
    hodge := hframe }
  apply ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.lift_of_actualPrimitiveCube F
    (m := m) (hm := hm) (P := P) (hP := hP)
  apply ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.actualCube_of_N_trivial F
  exact framedCubeLine R Q
    (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.primitiveThetaLine F)
    (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.primitiveThetaLine_invertible F)

#print axioms framedAffineLift
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion

lemma affineMultiple_eq {R : Type u} [CommRing R] (F : EllipticFamily R)
    (P : ArithmeticThetaRelativeThetaLiftsR0255.point F) (n : ℕ) :
    multiple (relativeFamily F) P n = F.law.nsmul (𝟙 _) n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F.law.mul (𝟙 _) (multiple (relativeFamily F) P n) P = _
    rw [ih, F.law.nsmul_succ]

lemma affineTranslation_eq {R : Type u} [CommRing R] (F : EllipticFamily R)
    (P : ArithmeticThetaRelativeThetaLiftsR0255.point F) :
    translation (relativeFamily F) P = ArithmeticThetaRelativeThetaLiftsR0255.translation F P := by
  change F.law.translate (multiple (relativeFamily F) P 2) =
    F.law.translate (F.law.nsmul (𝟙 _) 2 P)
  rw [affineMultiple_eq]

/-- The local affine lift on the exact conormal line, transported through the
fixed derivative comparison specified by the contract. -/
theorem framedAffineConormalLift
    (R : Type u) [CommRing R] [Algebra ℚ R] (F : EllipticFamily R)
    (hframe : Nonempty ((𝟙_ (Spec (CommRingCat.of R)).Modules) ≅
      (Scheme.Modules.pullback (F.law.one (𝟙 _)).val).obj F.projection.kaehler))
    (m : ℕ) (hm : 0 < m) (P : ArithmeticThetaRelativeThetaLiftsR0255.point F)
    (hP : multiple (relativeFamily F) P (2*m) = F.law.one (𝟙 _)) :
    Nonempty (Lift (relativeFamily F) m (translation (relativeFamily F) P)) := by
  have hkill : P.val ≫ F.law.schemeNsmul (2*m) = ArithmeticThetaRelativeThetaLiftsR0255.zero F := by
    apply (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.killed_iff F P (2*m)).mpr
    rw [← affineMultiple_eq F P (2*m)]
    exact hP
  obtain ⟨α⟩ := framedAffineLift R F hframe m hm P hkill
  rw [affineTranslation_eq F P]
  exact ⟨(Scheme.Modules.pullback (ArithmeticThetaRelativeThetaLiftsR0255.translation F P)).mapIso
      (affineThetaComparison F m) ≪≫ α ≪≫ (affineThetaComparison F m).symm⟩

#print axioms framedAffineConormalLift
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Transport of the specified theta line along an actual pointed Cartesian
square, including nonflat tests. The Hodge comparison is induced by the
inclusion-compatible identity ideal comparison. -/
def cartesianThetaIso {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine F m := by
  let hE := SchemeThetaInversion.zero_cartier E
  let hF := SchemeThetaInversion.zero_cartier F
  let hi := CartesianIdentityIdeal.ideal_comap E F b f hc hz
  let i := idealPullbackIso f E.zero.ker F.zero.ker hE hF hi
  let iH := cotangentComparison E F b f hz i
  let im := idealPullbackIso f (E.zero.ker ^ m) (F.zero.ker ^ m)
    (hE.pow m) (hF.pow m) (by rw [comap_power, hi])
  letI := dualComparison_isIso f (E.zero.ker ^ m).module (hE.pow m).isInvertible_module
  let eD : (Scheme.Modules.pullback f).obj (Scheme.Modules.dual (E.zero.ker ^ m).module) ≅
      Scheme.Modules.dual (F.zero.ker ^ m).module :=
    asIso (dualComparison f _) ≪≫
      ((MonoidalClosed.internalHom (C := F.curve.Modules)).mapIso im.symm.op).app (𝟙_ _)
  let eH : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback E.p).obj ((Cotangent E).tensorPow m)) ≅
      (Scheme.Modules.pullback F.p).obj ((Cotangent F).tensorPow m) :=
    (Scheme.Modules.pullbackComp f E.p).app _ ≪≫
    (Scheme.Modules.pullbackCongr hc.w).app _ ≪≫
    ((Scheme.Modules.pullbackComp F.p b).app _).symm ≪≫
    (Scheme.Modules.pullback F.p).mapIso (Scheme.Modules.pullbackTensorPowIso b (Cotangent E) m ≪≫
      Scheme.Modules.tensorPowMapIso iH m)
  exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (eD ⊗ᵢ eH)

#print axioms cartesianThetaIso
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeLevelR0204

section PointTransport
variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hc : IsPullback f F.p E.p b)
  (hmul : Multiplicative E F b f)

/-- The actual Cartesian comparison acts on test points as a group homomorphism. -/
def familyPointMap {U : Scheme.{u}} (t : U ⟶ T) :
    letI := pointCommGroup F t
    letI := pointCommGroup E (t ≫ b)
    SchemeHomOver t F.p →* SchemeHomOver (t ≫ b) E.p := by
  letI := pointCommGroup F t
  letI := pointCommGroup E (t ≫ b)
  let g (x : SchemeHomOver t F.p) : SchemeHomOver (t ≫ b) E.p :=
    ⟨x.val ≫ f, by rw [Category.assoc, hc.w, ← Category.assoc, x.property]⟩
  have hgm (x y : SchemeHomOver t F.p) : g (x * y) = g x * g y :=
    Subtype.ext (hmul U t x y (g x) (g y) rfl rfl).symm
  refine { toFun := g, map_mul' := hgm, map_one' := ?_ }
  have h : g 1 * g 1 = g 1 := (hgm 1 1).symm.trans (congrArg g (one_mul 1))
  exact mul_left_cancel (h.trans (mul_one (g 1)).symm)

lemma familyPointMap_bijective {U : Scheme.{u}} (t : U ⟶ T) :
    Function.Bijective (familyPointMap E F b f hc hmul t) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply hc.hom_ext (congrArg Subtype.val h)
    exact x.property.trans y.property.symm
  · intro y
    let x : SchemeHomOver t F.p := ⟨hc.lift y.val t y.property, hc.lift_snd _ _ _⟩
    exact ⟨x, Subtype.ext (hc.lift_fst _ _ _)⟩

def familyPointEquiv {U : Scheme.{u}} (t : U ⟶ T) :
    letI := pointCommGroup F t
    letI := pointCommGroup E (t ≫ b)
    SchemeHomOver t F.p ≃* SchemeHomOver (t ≫ b) E.p := by
  letI := pointCommGroup F t
  letI := pointCommGroup E (t ≫ b)
  exact MulEquiv.ofBijective (familyPointMap E F b f hc hmul t)
    (familyPointMap_bijective E F b f hc hmul t)

/-- Restriction of the given section through the actual Cartesian square. -/
def restrictedPoint (P : point E) : point F := by
  letI := pointCommGroup F (𝟙 T)
  letI := pointCommGroup E ((𝟙 T) ≫ b)
  exact (familyPointEquiv E F b f hc hmul (𝟙 T)).symm
    (pointPullback E (𝟙 S) ((𝟙 T) ≫ b) b (by simp) P)

lemma restrictedPoint_comp (P : point E) :
    (restrictedPoint E F b f hc hmul P).val ≫ f = b ≫ P.val := by
  letI := pointCommGroup F (𝟙 T)
  letI := pointCommGroup E ((𝟙 T) ≫ b)
  exact congrArg Subtype.val ((familyPointEquiv E F b f hc hmul (𝟙 T)).apply_symm_apply _)

lemma restrictedPoint_multiple (P : point E) (n : ℕ) :
    ArithmeticThetaSchemeThetaMarkingR0259.multiple F (restrictedPoint E F b f hc hmul P) n =
      restrictedPoint E F b f hc hmul
        (ArithmeticThetaSchemeThetaMarkingR0259.multiple E P n) := by
  letI := pointCommGroup E (𝟙 S)
  letI := pointCommGroup F (𝟙 T)
  letI := pointCommGroup E ((𝟙 T) ≫ b)
  change ArithmeticThetaSchemeLevelR0204.multiple F _ n _ =
    (familyPointEquiv E F b f hc hmul (𝟙 T)).symm
      (pointPullback E (𝟙 S) ((𝟙 T) ≫ b) b (by simp)
        (ArithmeticThetaSchemeLevelR0204.multiple E _ n P))
  rw [multiple_eq_pow, multiple_eq_pow, map_pow, map_pow]
  rfl

lemma restrictedPoint_one : restrictedPoint E F b f hc hmul (E.law.one (𝟙 S)) =
    F.law.one (𝟙 T) := by
  letI := pointCommGroup E (𝟙 S)
  letI := pointCommGroup F (𝟙 T)
  letI := pointCommGroup E ((𝟙 T) ≫ b)
  change (familyPointEquiv E F b f hc hmul (𝟙 T)).symm
    (pointPullback E (𝟙 S) ((𝟙 T) ≫ b) b (by simp) 1) = 1
  rw [map_one, map_one]

lemma restrictedPoint_killed (P : point E) (n : ℕ)
    (hP : ArithmeticThetaSchemeThetaMarkingR0259.multiple E P n = E.law.one (𝟙 S)) :
    ArithmeticThetaSchemeThetaMarkingR0259.multiple F (restrictedPoint E F b f hc hmul P) n =
      F.law.one (𝟙 T) := by
  rw [restrictedPoint_multiple, hP, restrictedPoint_one]

lemma translation_cartesian (P : point E) :
    translation F (restrictedPoint E F b f hc hmul P) ≫ f = f ≫ translation E P := by
  let Q := restrictedPoint E F b f hc hmul P
  let A : SchemeHomOver F.p F.p := ⟨𝟙 _, Category.id_comp _⟩
  let B : SchemeHomOver F.p F.p :=
    ⟨F.p ≫ (ArithmeticThetaSchemeThetaMarkingR0259.multiple F Q 2).val,
      by rw [Category.assoc, (ArithmeticThetaSchemeThetaMarkingR0259.multiple F Q 2).property, Category.comp_id]⟩
  let a : SchemeHomOver E.p E.p := ⟨𝟙 _, Category.id_comp _⟩
  let q : SchemeHomOver E.p E.p :=
    ⟨E.p ≫ (ArithmeticThetaSchemeThetaMarkingR0259.multiple E P 2).val,
      by rw [Category.assoc, (ArithmeticThetaSchemeThetaMarkingR0259.multiple E P 2).property, Category.comp_id]⟩
  let a' := GoodReductionJacobian.schemeHomOverComp f hc.w a
  let q' := GoodReductionJacobian.schemeHomOverComp f hc.w q
  have ha : a'.val = A.val ≫ f := (Category.comp_id f).trans (Category.id_comp f).symm
  have hq : q'.val = B.val ≫ f := by
    change f ≫ (E.p ≫ _) = (F.p ≫ _) ≫ f
    rw [Category.assoc, restrictedPoint_multiple E F b f hc hmul P 2,
      restrictedPoint_comp, ← Category.assoc, hc.w, Category.assoc]
  have h := hmul F.curve F.p A B a' q' ha hq
  have hn := E.law.mul_natural E.p (F.p ≫ b) f hc.w a q
  exact h.symm.trans (congrArg Subtype.val hn).symm
end PointTransport

#print axioms restrictedPoint_killed
#print axioms translation_cartesian
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion
open ArithmeticThetaLegendreAtlasR0176

variable {S : Scheme.{u}} (E : Family S) (C : SchemeLocal.FramedChart E)
attribute [local instance] SchemeLocal.FramedChart.commRing

def chartAffineFamily : EllipticFamily C.ring where
  curve := C.Q.target
  projection := C.Q.structureMap
  law := C.Q.law
  commutative := C.comm
  proper := C.Q.geometry.proper
  smooth := C.Q.dimension
  connected := MorphismProperty.of_isPullback C.cartesian E.connected

lemma chart_multiplicative : ArithmeticThetaSchemeLevelR0204.Multiplicative E
    (relativeFamily (chartAffineFamily E C)) C.base C.comparison := C.mul_eq

/-- A lift of the restricted global translation on the pullback of the global
line, with every chart, section and conormal map constructed from the family. -/
theorem chart_translation_lift
    (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (m : ℕ) (hm : 0 < m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S)) :
    Nonempty ((Scheme.Modules.pullback C.comparison).obj
        ((Scheme.Modules.pullback (translation E P)).obj (thetaLine E m)) ≅
      (Scheme.Modules.pullback C.comparison).obj (thetaLine E m)) := by
  let scalar : k →+* C.ring := (Spec.preimage (C.base ≫ σ)).hom
  letI : Algebra k C.ring := scalar.toAlgebra
  letI : Algebra ℚ C.ring := Algebra.compHom C.ring (algebraMap ℚ k)
  let F := chartAffineFamily E C
  let G := relativeFamily F
  let Q := restrictedPoint E G C.base C.comparison C.cartesian (chart_multiplicative E C) P
  have hQ : multiple G Q (2*m) = G.law.one (𝟙 _) :=
    restrictedPoint_killed E G C.base C.comparison C.cartesian (chart_multiplicative E C) P (2*m) hP
  obtain ⟨α⟩ := framedAffineConormalLift C.ring F C.Q.hodge m hm Q hQ
  let i := cartesianThetaIso E G C.base C.comparison C.cartesian C.zero_eq m
  have ht : translation G Q ≫ C.comparison = C.comparison ≫ translation E P :=
    translation_cartesian E G C.base C.comparison C.cartesian (chart_multiplicative E C) P
  exact ⟨(Scheme.Modules.pullbackComp C.comparison (translation E P)).app _ ≪≫
    (Scheme.Modules.pullbackCongr ht.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (translation G Q) C.comparison).app _).symm ≪≫
    (Scheme.Modules.pullback (translation G Q)).mapIso i ≪≫ α ≪≫ i.symm⟩

#print axioms chart_translation_lift
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.SectionGluing
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift

variable {S X : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)

def sectionRestrict (U : S.Opens) : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p U).flip.lift (U.ι ≫ e) (𝟙 _)
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

lemma sectionRestrict_ι (U : S.Opens) :
    sectionRestrict p e he U ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ e :=
  (isPullback_morphismRestrict p U).flip.lift_fst _ _ _

lemma sectionRestrict_section (U : S.Opens) :
    sectionRestrict p e he U ≫ p ∣_ U = 𝟙 _ :=
  (isPullback_morphismRestrict p U).flip.lift_snd _ _ _

include e he in
lemma base_le {U V : S.Opens} (h : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U) : V ≤ U := by
  intro x hx
  have hpx : p (e x) = x := by simpa using congrArg (fun f : S ⟶ S => f x) he
  have hv : e x ∈ p ⁻¹ᵁ V := by change p (e x) ∈ V; rw [hpx]; exact hx
  have hu := h hv
  change p (e x) ∈ U at hu
  rwa [hpx] at hu

lemma sectionRestrict_nested {U V : S.Opens} (h : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U) :
    sectionRestrict p e he V ≫ X.homOfLE h =
      S.homOfLE (base_le p e he h) ≫ sectionRestrict p e he U := by
  rw [← cancel_mono (p ⁻¹ᵁ U).ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, sectionRestrict_ι,
    Scheme.homOfLE_ι_assoc]

/-- Pull a global fibre trivialization to a restricted section, retaining the
pullback composition and equality comparisons. -/
def sectionTrivialization (M : X.Modules)
    (tM : (Scheme.Modules.pullback e).obj M ≅ 𝟙_ S.Modules) (U : S.Opens) :
    (Scheme.Modules.pullback (sectionRestrict p e he U)).obj
      ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj M) ≅ 𝟙_ U.toScheme.Modules :=
  (Scheme.Modules.pullbackComp (sectionRestrict p e he U) (p ⁻¹ᵁ U).ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (sectionRestrict_ι p e he U)).app M ≪≫
    ((Scheme.Modules.pullbackComp U.ι e).app M).symm ≪≫
    (Scheme.Modules.pullback U.ι).mapIso tM ≪≫ Scheme.Modules.pullbackUnitIso U.ι

include he in
/-- Local isomorphisms of lines with trivialized section fibres glue over an
arbitrary scheme base when structural functions are constant on each open. -/
theorem iso_of_local_trivialized
    (hp : ∀ U : S.Opens, Function.Surjective (p ∣_ U).appTop)
    (L M : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (tL : (Scheme.Modules.pullback e).obj L ≅ 𝟙_ S.Modules)
    (tM : (Scheme.Modules.pullback e).obj M ≅ 𝟙_ S.Modules)
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj L ≅
        (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj M)) : Nonempty (L ≅ M) := by
  classical
  let I := {U : S.Opens // Nonempty ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj L ≅
    (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj M)}
  let U (i : I) : X.Opens := p ⁻¹ᵁ i.val
  let restr {V W : X.Opens} (h : W ≤ V)
      (α : (Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj M) :=
    ((Scheme.Modules.pullbackComp (X.homOfLE h) V.ι).app L ≪≫
      (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app L).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE h)).mapIso α ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE h) V.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M)
  have hex (i : I) : ∃! φ : (Scheme.Modules.pullback (U i).ι).obj L ≅
      (Scheme.Modules.pullback (U i).ι).obj M,
      (Scheme.Modules.pullback (sectionRestrict p e he i.val)).mapIso φ =
        sectionTrivialization p e he L tL i.val ≪≫
          (sectionTrivialization p e he M tM i.val).symm :=
    existsUnique_fibreIso (p ∣_ i.val) (hp i.val) (sectionRestrict p e he i.val)
      (sectionRestrict_section p e he i.val) _ _ (hL.pullback _) _ i.property.some
  choose φ hφ using fun i : I => (hex i).exists
  have hU : ⨆ i : I, U i = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨V, hx, hV⟩ := hloc (p x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  have hB : ∀ i j : I, U i ⊓ U j ≤ ⨆ (k : {k : I // U k ≤ U i ⊓ U j}), U k.val := by
    intro i j x hx
    let W := i.val ⊓ j.val
    have hWi : p ⁻¹ᵁ W ≤ U i := fun _ h => h.1
    let k : I := ⟨W, ⟨restr hWi (φ i)⟩⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, fun _ h => h⟩, hx⟩
  have hcompat : ∀ (i j : I) (h : U j ≤ U i),
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso (φ i) =
        ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app L ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app L) ≪≫
          φ j ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M).symm := by
    intro i j h
    have hX := Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
      e (U i).ι (U j).ι (sectionRestrict p e he i.val) i.val.ι (sectionRestrict_ι p e he i.val)
      (sectionRestrict p e he j.val) j.val.ι (sectionRestrict_ι p e he j.val)
      (X.homOfLE h) (X.homOfLE_ι h) (S.homOfLE (base_le p e he h))
      (sectionRestrict_nested p e he h) (S.homOfLE_ι _) L M tL tM (φ i)
      (congrArg Iso.hom (hφ i))
    have hr : (Scheme.Modules.pullback (sectionRestrict p e he j.val)).mapIso (restr h (φ i)) =
        sectionTrivialization p e he L tL j.val ≪≫
          (sectionTrivialization p e he M tM j.val).symm := Iso.ext hX
    have hu : restr h (φ i) = φ j := (hex j).unique hr (hφ j)
    rw [← hu]
    dsimp only [restr]
    ext
    simp
  obtain ⟨α, _⟩ := Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
    L M U hU hB φ hcompat
  exact ⟨α⟩

#print axioms iso_of_local_trivialized
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.SectionGluing

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.SectionGluing
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255
variable {S X : Scheme.{u}}

def ratioTrivialization (L M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    {T : Scheme.{u}} (f : T ⟶ X)
    (c : (Scheme.Modules.pullback f).obj L ≅ (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullback f).obj (L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ T.Modules :=
  Scheme.Modules.pullbackTensorObjIso f L (Scheme.Modules.dual M) ≪≫
    (c ⊗ᵢ (hM.pullback_dual_monoidalV2 f).some) ≪≫
    (hM.pullback f).dual_monoidalV2.2.some

/-- The section fibres may be nontrivial: trivialize their ratio and cancel. -/
theorem iso_of_local (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (hp : ∀ U : S.Opens, Function.Surjective (p ∣_ U).appTop)
    (L M : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hM : Scheme.Modules.IsInvertible M)
    (c : (Scheme.Modules.pullback e).obj L ≅ (Scheme.Modules.pullback e).obj M)
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj L ≅
        (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj M)) : Nonempty (L ≅ M) := by
  classical
  let D := L ⊗ Scheme.Modules.dual M
  have hD : Scheme.Modules.IsInvertible D := hL.tensor_monoidalV2 hM.dual_monoidalV2.1
  have hlocD : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj D ≅
        (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj (𝟙_ X.Modules)) := by
    intro s
    obtain ⟨U, hs, ⟨α⟩⟩ := hloc s
    exact ⟨U, hs, ⟨ratioTrivialization L M hM _ α ≪≫
      (Scheme.Modules.pullbackUnitIso _).symm⟩⟩
  have h := iso_of_local_trivialized p e he hp D (𝟙_ X.Modules) hD
    (ratioTrivialization L M hM e c) (Scheme.Modules.pullbackUnitIso e) hlocD
  apply (lineClass_eq_iff L M hL hM).mp
  apply mul_inv_eq_one.mp
  have hc := (lineClass_eq_iff D (𝟙_ X.Modules) hD
    (Scheme.Modules.isInvertible_unit X)).mpr h
  change lineClass (L ⊗ Scheme.Modules.dual M)
    (hL.tensor_monoidalV2 hM.dual_monoidalV2.1) =
      lineClass (𝟙_ X.Modules) (Scheme.Modules.isInvertible_unit X) at hc
  rw [lineClass_tensor L (Scheme.Modules.dual M) hL hM.dual_monoidalV2.1,
    lineClass_dual M hM, lineClass_unit] at hc
  exact hc

#print axioms iso_of_local
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift.SectionGluing

namespace ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
variable {S : Scheme.{u}} (E : Family S)

lemma restricted_structure_surjective (U : S.Opens) :
    Function.Surjective (E.p ∣_ U).appTop := by
  rw [morphismRestrict_appTop]
  exact (ConcreteCategory.bijective_of_isIso
    (E.curve.presheaf.map (eqToHom (image_morphismRestrict_preimage E.p U ⊤)).op)).surjective.comp
    (ArithmeticThetaKatoCharacterizationR0254.GlobalUnitTwoThreeNormRigidity.structure_app_bijective E _).surjective

lemma chart_range (C : SchemeLocal.FramedChart E) :
    letI := C.openImmersion
    Set.range C.comparison = (E.p ⁻¹ᵁ C.base.opensRange : Set E.curve) := by
  letI := C.openImmersion
  rw [← IsOpenImmersion.range_pullbackFst C.base E.p]
  exact range_eq_range_of_surjective _ _ C.cartesian.isoPullback.hom
    C.cartesian.isoPullback_hom_fst

lemma chart_to_open (C : SchemeLocal.FramedChart E) (L M : E.curve.Modules)
    (h : Nonempty ((Scheme.Modules.pullback C.comparison).obj L ≅
      (Scheme.Modules.pullback C.comparison).obj M)) :
    letI := C.openImmersion
    Nonempty ((Scheme.Modules.pullback (E.p ⁻¹ᵁ C.base.opensRange).ι).obj L ≅
      (Scheme.Modules.pullback (E.p ⁻¹ᵁ C.base.opensRange).ι).obj M) := by
  letI := C.openImmersion
  letI : IsOpenImmersion C.comparison :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.cartesian.flip C.openImmersion
  let U := E.p ⁻¹ᵁ C.base.opensRange
  have hr : Set.range C.comparison = Set.range U.ι := by
    rw [chart_range E C]
    exact (Subtype.range_coe_subtype).symm
  let j := IsOpenImmersion.isoOfRangeEq C.comparison U.ι hr
  have hj : j.inv ≫ C.comparison = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hr
  obtain ⟨α⟩ := h
  exact ⟨((Scheme.Modules.pullbackComp j.inv C.comparison).app L ≪≫
      (Scheme.Modules.pullbackCongr hj).app L).symm ≪≫
    (Scheme.Modules.pullback j.inv).mapIso α ≪≫
    (Scheme.Modules.pullbackComp j.inv C.comparison).app M ≪≫
      (Scheme.Modules.pullbackCongr hj).app M⟩

lemma point_inverse {T : Scheme.{u}} (t : T ⟶ S)
    (a : SchemeHomOver t E.p) :
    a.val ≫ inverse E = (E.law.inv t a).val := by
  have h := SchemeThetaInversion.inverse_natural E E.p t a.val a.property
    (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.p E.p)
  have ha : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.p E.p) = a := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha] at h
  exact congrArg Subtype.val h

lemma point_translation {T : Scheme.{u}} (t : T ⟶ S)
    (a : SchemeHomOver t E.p) (P : point E) :
    a.val ≫ translation E P =
      (E.law.mul t a ⟨t ≫ (multiple E P 2).val,
        by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩).val := by
  have h := E.law.mul_natural E.p t a.val a.property
    (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.p E.p)
    ⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩
  have h₁ : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.p E.p) = a := by
    apply Subtype.ext
    exact Category.comp_id _
  have h₂ : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩ :
        SchemeHomOver E.p E.p) =
      ⟨t ≫ (multiple E P 2).val, by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩ := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (multiple E P 2).val) a.property)
  rw [h₁, h₂] at h
  exact congrArg Subtype.val h

lemma reflection_fixed (P : point E) : negative E P ≫ reflection E P = negative E P := by
  let a := E.law.inv (𝟙 _) P
  have hd : a.val ≫ translation E P = P.val := by
    rw [point_translation]
    have hid : (⟨𝟙 _ ≫ (multiple E P 2).val, by
        rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩ :
        point E) = multiple E P 2 := by
      apply Subtype.ext
      exact Category.id_comp _
    rw [hid]
    letI := pointCommGroup E (𝟙 S)
    have htwo : multiple E P 2 = P * P := by
      rw [multiple, multiple_eq_pow]
      exact pow_two P
    rw [htwo]
    change (P⁻¹ * (P * P)).val = P.val
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  change a.val ≫ (translation E P ≫ inverse E) = a.val
  rw [← Category.assoc, hd, point_inverse]

#print axioms restricted_structure_surjective
#print axioms chart_to_open
#print axioms reflection_fixed
end ArithmeticThetaSchemeThetaMarkingR0259.SchemeDoubledTorsionLift

namespace ArithmeticThetaSchemeThetaMarkingR0259
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open SchemeDoubledTorsionLift

/-- Translation by twice a `2*m`-torsion section preserves the actual conormal
rigidified theta line on an arbitrary characteristic-zero scheme base. -/
theorem scheme_doubled_torsion_lift
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m) (_heven : Even m)
    (P : point E) (hP : multiple E P (2*m) = E.law.one (𝟙 S)) :
    Nonempty (Lift E m (translation E P)) := by
  classical
  let L := thetaLine E m
  let t := translation E P
  let r := reflection E P
  let i : (Scheme.Modules.pullback r).obj L ≅ (Scheme.Modules.pullback t).obj L :=
    ((Scheme.Modules.pullbackComp t (inverse E)).app L).symm ≪≫
      (Scheme.Modules.pullback t).mapIso (SchemeThetaInversion.initialLift E m)
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (E.p ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback r).obj L) ≅
        (Scheme.Modules.pullback (E.p ⁻¹ᵁ U).ι).obj L) := by
    intro s
    obtain ⟨C, hs⟩ := SchemeLocal.exists_framedChart E s
    letI := C.openImmersion
    obtain ⟨α⟩ := chart_translation_lift E C k σ m hm P hP
    refine ⟨C.base.opensRange, hs, chart_to_open E C _ _ ?_⟩
    exact ⟨(Scheme.Modules.pullback C.comparison).mapIso i ≪≫ α⟩
  obtain ⟨β⟩ := SectionGluing.iso_of_local E.p (negative E P)
    (E.law.inv (𝟙 S) P).property (restricted_structure_surjective E)
    ((Scheme.Modules.pullback r).obj L) L
    ((SchemeThetaInversion.line_invertible E m).pullback r)
    (SchemeThetaInversion.line_invertible E m)
    (fixedComparison E m (negative E P) r (reflection_fixed E P)) hloc
  exact ⟨i.symm ≪≫ β⟩

#print axioms scheme_doubled_torsion_lift
end ArithmeticThetaSchemeThetaMarkingR0259
