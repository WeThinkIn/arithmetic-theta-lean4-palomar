module

public import SchemeThetaMarkingDefinitionsR0259
public import RelativeGeometricNaturalityR0258

@[expose] public section

/-! Structural commutators for the actual theta line over arbitrary schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemePrimitiveThetaCommutator
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

variable {S : Scheme.{u}} (E : Family S)

lemma line_invertible (m : ℕ) : Scheme.Modules.IsInvertible (thetaLine E m) := by
  have hI := ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E
  exact (hI.pow m).isInvertible_module.dual.1.tensor_monoidalV2
    (((hI.isInvertible_module.pullback E.zero).tensorPow m).pullback E.p)

lemma constants_bijective : Function.Bijective E.p.appTop := by
  exact
    ArithmeticThetaKatoCharacterizationR0254.GlobalUnitTwoThreeNormRigidity.structure_app_bijective E ⊤

lemma scalar_bijective : Function.Bijective (scalar E) := by
  let f := E.p.appTop.hom
  have hf := constants_bijective E
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

lemma existsUnique_scaled (m : ℕ) (f : E.curve ⟶ E.curve)
    (α β : Lift E m f) : ∃! c : Γ(S, ⊤)ˣ, α = scaled E m c β := by
  obtain ⟨s, hs⟩ := aut_scalar (line_invertible E m) (β.symm ≪≫ α)
  obtain ⟨c, hc⟩ := (scalar_bijective E).2 s
  have heq : α = scaled E m c β := by
    unfold scaled
    rw [hc, hs]
    simp
  refine ⟨c, heq, ?_⟩
  intro d hd
  apply (scalar_bijective E).1
  apply Units.ext
  apply smulHom_injective (line_invertible E m)
  have h := congrArg Iso.hom (hd.symm.trans heq)
  exact (cancel_epi β.hom).mp h

/-- Translation by an undoubled section, used only for the group-law calculation. -/
def rawTranslation (P : point E) : E.curve ⟶ E.curve :=
  (E.law.mul E.p ⟨𝟙 E.curve, Category.id_comp _⟩
    ⟨E.p ≫ P.val, by rw [Category.assoc, P.property, Category.comp_id]⟩).val

lemma point_translate {T : Scheme.{u}} (t : T ⟶ S)
    (a : SchemeHomOver t E.p) (b : point E) :
    a.val ≫ rawTranslation E b =
      (E.law.mul t a ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩).val := by
  let i : SchemeHomOver E.p E.p := ⟨𝟙 E.curve, Category.id_comp _⟩
  have h := E.law.mul_natural E.p t a.val a.property i
    ⟨E.p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  have h₁ : GoodReductionJacobian.schemeHomOverComp a.val a.property i = a := by
    apply Subtype.ext
    exact Category.comp_id _
  have h₂ : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨E.p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ :
        SchemeHomOver E.p E.p) =
      ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b.val) a.property)
  rw [h₁, h₂] at h
  exact congrArg Subtype.val h

lemma translations_commute (P Q : point E) :
    translation E P ≫ translation E Q = translation E Q ≫ translation E P := by
  let a := multiple E P 2
  let b := multiple E Q 2
  let ca : SchemeHomOver E.p E.p :=
    ⟨E.p ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let cb : SchemeHomOver E.p E.p :=
    ⟨E.p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  let i : SchemeHomOver E.p E.p := ⟨𝟙 E.curve, Category.id_comp _⟩
  change (E.law.mul E.p i ca).val ≫ rawTranslation E b =
    (E.law.mul E.p i cb).val ≫ rawTranslation E a
  rw [point_translate, point_translate]
  change (E.law.mul E.p (E.law.mul E.p i ca) cb).val =
    (E.law.mul E.p (E.law.mul E.p i cb) ca).val
  rw [E.law.mul_assoc, E.law.mul_assoc, E.law.mul_comm E.p ca cb]

/-- Global scalar existence does not require torsion, characteristic, or positivity. -/
lemma existsUnique_commutator (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) :
    ∃! c : Γ(S, ⊤)ˣ, Commutator E m P Q α β c := by
  let h := translations_commute E P Q
  obtain ⟨c, hc, hu⟩ := existsUnique_scaled E m _
    (compose E m _ _ α β) (changeMap E m h (compose E m _ _ β α))
  refine ⟨c, ⟨h, hc⟩, ?_⟩
  rintro d ⟨h', hd⟩
  exact hu d hd

open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

section Cartesian
variable {T : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)

/-- The dual identity-ideal power is transported by its actual Cartier comparison. -/
def originPowerComparison (m : ℕ) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dual ((E.zero.ker ^ m).module)) ≅
      Scheme.Modules.dual ((F.zero.ker ^ m).module) := by
  have hE := ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E
  have hF := ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible F
  let e := idealPullbackIso f (E.zero.ker ^ m) (F.zero.ker ^ m) (hE.pow m) (hF.pow m)
    (by rw [comap_power,
        ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.ideal_comap E F b f hc hz])
  letI := dualComparison_isIso f (E.zero.ker ^ m).module (hE.pow m).isInvertible_module
  exact asIso (dualComparison f _) ≪≫
    ((MonoidalClosed.internalHom (C := F.curve.Modules)).mapIso e.symm.op).app (𝟙_ F.curve.Modules)

/-- Pull back the conormal along the pointed square; no Hodge frame is chosen. -/
def cotangentComparison :
    (Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E) ≅
      ArithmeticThetaSchemeHodgeR0205.Cotangent F :=
  ArithmeticThetaSchemeHodgeR0205.cotangentComparison E F b f hz
    (ArithmeticThetaSchemeHodgeR0205.cartesian_identity_ideal S T E F b f hc hz).exists.choose

def thetaComparison (m : ℕ) :
    (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine F m :=
  Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    (originPowerComparison E F b f hc hz m ⊗ᵢ
      ((Scheme.Modules.pullbackComp f E.p).app _ ≪≫
        (Scheme.Modules.pullbackCongr hc.w).app _ ≪≫
        ((Scheme.Modules.pullbackComp F.p b).app _).symm ≪≫
        (Scheme.Modules.pullback F.p).mapIso
          (Scheme.Modules.pullbackTensorPowIso b _ m ≪≫
            Scheme.Modules.tensorPowMapIso (cotangentComparison E F b f hc hz) m)))
include hc hz in
lemma translation_square
    (hm : ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f)
    (P : point E) (P' : point F) (hP : P'.val ≫ f = b ≫ P.val) :
    f ≫ translation E P = translation F P' ≫ f := by
  have h := point_translate E (F.p ≫ b) ⟨f, hc.w⟩ (multiple E P 2)
  change f ≫ translation E P = _ at h
  rw [h]
  apply hm F.curve F.p
    (⟨𝟙 F.curve, Category.id_comp _⟩ : SchemeHomOver F.p F.p)
    ⟨F.p ≫ (multiple F P' 2).val, by
      rw [Category.assoc, (multiple F P' 2).property, Category.comp_id]⟩
    ⟨f, hc.w⟩
    ⟨(F.p ≫ b) ≫ (multiple E P 2).val, by
      rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩
  · simp
  · change (F.p ≫ b) ≫ (multiple E P 2).val =
      (F.p ≫ (multiple F P' 2).val) ≫ f
    rw [Category.assoc, Category.assoc,
      ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp E F b f hz hm P' P hP 2]

include hc in
lemma scalar_square (c : Γ(S, ⊤)ˣ) :
    Units.map f.appTop.hom.toMonoidHom (scalar E c) =
      scalar F (Units.map b.appTop.hom.toMonoidHom c) := by
  have h : E.p.appTop ≫ f.appTop = b.appTop ≫ F.p.appTop := by
    rw [← Scheme.Hom.comp_appTop, hc.w, Scheme.Hom.comp_appTop]
  apply Units.ext
  exact congrArg (fun g : Γ(S, ⊤) ⟶ Γ(F.curve, ⊤) => g (c : Γ(S, ⊤))) h

def transportedLift (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (hg : f ≫ g = g' ≫ f) (α : Lift E m g) : Lift F m g' :=
  ArithmeticThetaRelativeThetaNaturalityR0258.MidpointNaturalityProof.transport f
    (thetaComparison E F b f hc hz m) g g' hg α

/-- The whole commutator equation pulls back with the same structural scalar. -/
lemma commutator_transport (m : ℕ)
    (hm : ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f)
    (P Q : point E) (P' Q' : point F)
    (hP : P'.val ≫ f = b ≫ P.val) (hQ : Q'.val ≫ f = b ≫ Q.val)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Γ(S, ⊤)ˣ) (hab : Commutator E m P Q α β c) :
    Commutator F m P' Q'
      (transportedLift E F b f hc hz m _ _ (translation_square E F b f hc hz hm P P' hP) α)
      (transportedLift E F b f hc hz m _ _ (translation_square E F b f hc hz hm Q Q' hQ) β)
      (Units.map b.appTop.hom.toMonoidHom c) := by
  obtain ⟨h, hh⟩ := hab
  let h' := translations_commute F P' Q'
  refine ⟨h', ?_⟩
  have heq : ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift
      (translation E P) (translation E Q) α β =
      (Scheme.Modules.pullbackCongr h).app (thetaLine E m) ≪≫
        ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift
          (translation E Q) (translation E P) β α ≪≫ smulIso (scalar E c) (thetaLine E m) := by
    simpa only [compose, scaled, changeMap, transportedLift,
      ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift,
      Iso.trans_assoc] using hh
  simpa only [compose, scaled, changeMap, transportedLift,
    ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift,
    Iso.trans_assoc] using
    (ArithmeticThetaRelativeThetaNaturalityR0258.GeometricNaturalityProof.transport_commutation f
      (thetaComparison E F b f hc hz m) _ _ _ _
      (translation_square E F b f hc hz hm P P' hP)
      (translation_square E F b f hc hz hm Q Q' hQ)
      h h' α β _ _ rfl rfl (scalar E c) _ (scalar_square E F b f hc c) heq)

end Cartesian

namespace Affine
open ArithmeticThetaLegendreAtlasR0176
abbrev schemeFamily {R : Type u} [CommRing R] (F : EllipticFamily R) :=
  ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F

variable {R : Type u} [CommRing R] (F : EllipticFamily R)

lemma multiple_eq (P : point (schemeFamily F)) (n : ℕ) :
    multiple (schemeFamily F) P n = F.law.nsmul (𝟙 _) n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F.law.mul _ (multiple (schemeFamily F) P n) P =
      F.law.mul _ (F.law.nsmul _ n P) P
    rw [ih]

def level (m : ℕ) (M : ArithmeticThetaSchemeLevelR0204.FullLevel (schemeFamily F) m) :
    FamilyLevel R F m where
  x := M.x
  y := M.y
  killed_x := by
    apply (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.killed_iff F M.x m).mpr
    rw [← multiple_eq]
    exact M.killed_x
  killed_y := by
    apply (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.killed_iff F M.y m).mpr
    rw [← multiple_eq]
    exact M.killed_y
  avoids := by
    intro i j hij
    have h := M.avoids i j hij
    simp only [multiple_eq] at h
    exact h

def lift (m : ℕ) (P : point (schemeFamily F))
    (α : Lift (schemeFamily F) m (translation (schemeFamily F) P)) :
    ArithmeticThetaRelativeThetaLiftsR0255.Lift F m
      (ArithmeticThetaRelativeThetaLiftsR0255.translation F P) :=
  (Scheme.Modules.pullback (translation (schemeFamily F) P)).mapIso (affineThetaComparison F m).symm ≪≫
    α ≪≫ affineThetaComparison F m

def baseUnit (c : Γ(Base R, ⊤)ˣ) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom c

lemma scalar_eq (c : Γ(Base R, ⊤)ˣ) :
    scalar (schemeFamily F) c = ArithmeticThetaRelativeThetaRelationsR0256.scalar F (baseUnit c) := by
  have h : (Scheme.ΓSpecIso (.of R)).hom ≫
      ((Scheme.ΓSpecIso (.of R)).inv ≫ F.projection.appTop) = F.projection.appTop := by simp
  apply Units.ext
  exact (congrArg (fun g : Γ(Base R, ⊤) ⟶ Γ(F.curve, ⊤) => g (c : Γ(Base R, ⊤))) h).symm

lemma commutator (m : ℕ) (P Q : point (schemeFamily F))
    (α : Lift (schemeFamily F) m (translation (schemeFamily F) P))
    (β : Lift (schemeFamily F) m (translation (schemeFamily F) Q))
    (c : Γ(Base R, ⊤)ˣ) (hc : Commutator (schemeFamily F) m P Q α β c) :
    ArithmeticThetaRelativeThetaRelationsR0256.Commutator F m P Q
      (lift F m P α) (lift F m Q β) (baseUnit c) := by
  obtain ⟨h, hh⟩ := hc
  refine ⟨h, ?_⟩
  have hab : ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift
      (translation (schemeFamily F) P) (translation (schemeFamily F) Q) α β =
      (Scheme.Modules.pullbackCongr h).app _ ≪≫
        ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift
          (translation (schemeFamily F) Q) (translation (schemeFamily F) P) β α ≪≫
          smulIso (scalar (schemeFamily F) c) _ := by
    simpa only [compose, scaled, changeMap,
      ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift,
      Iso.trans_assoc] using hh
  have htrans := ArithmeticThetaRelativeThetaNaturalityR0258.GeometricNaturalityProof.conjugate_commutation
    _ _ h (affineThetaComparison F m) α β _ hab
  rw [scalar_eq] at htrans
  simp only [lift, ArithmeticThetaRelativeThetaRelationsR0256.compose,
    ArithmeticThetaRelativeThetaRelationsR0256.scaled,
    ArithmeticThetaRelativeThetaRelationsR0256.changeMap,
    ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.PullbackLifts.compLift,
    Iso.trans_assoc] at htrans ⊢
  exact htrans

/-- The accepted geometric argument requires no Noetherian hypothesis on the base ring. -/
lemma primitive [Algebra ℚ R] (m : ℕ) (hm : 0 < m)
    (M : FamilyLevel R F (2*m))
    (α : ArithmeticThetaRelativeThetaLiftsR0255.Lift F m
      (ArithmeticThetaRelativeThetaLiftsR0255.translation F M.x))
    (β : ArithmeticThetaRelativeThetaLiftsR0255.Lift F m
      (ArithmeticThetaRelativeThetaLiftsR0255.translation F M.y))
    (c : Rˣ) (hc : ArithmeticThetaRelativeThetaRelationsR0256.Commutator F m M.x M.y α β c) :
    ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c := by
  apply (ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.primitiveUnit_iff_geometric_tests m c).mpr
  refine ⟨?_, ?_⟩
  · exact ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.commutator_pow_eq_one
      F m m M.x M.y M.killed_x α β c hc
  · intro k _ _ f i hi
    letI : Algebra ℚ k := (f.comp (algebraMap ℚ R)).toAlgebra
    exact ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.geometric_commutator_primitive
      F f m hm M α β c hc i hi
lemma primitive_scheme [Algebra ℚ R] (m : ℕ) (hm : 0 < m)
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel (schemeFamily F) (2*m))
    (α : Lift (schemeFamily F) m (translation (schemeFamily F) M.x))
    (β : Lift (schemeFamily F) m (translation (schemeFamily F) M.y))
    (c : Γ(Base R, ⊤)ˣ) (hc : Commutator (schemeFamily F) m M.x M.y α β c) :
    PrimitiveUnit m c := by
  have hp := primitive F m hm (level F (2*m) M) (lift F m M.x α) (lift F m M.y β)
    (baseUnit c) (commutator F m M.x M.y α β c hc)
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  constructor
  · apply Units.ext
    apply e.injective
    have h := congrArg Units.val hp.1
    change e (c : Γ(Base R, ⊤)) ^ m = 1 at h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using h
  · intro i hi
    have h := (hp.2 i hi).map e.symm.toRingHom
    change IsUnit (e.symm (e (c : Γ(Base R, ⊤)) ^ i.val - 1)) at h
    simpa only [map_sub, map_pow, map_one, RingEquiv.symm_apply_apply] using h

end Affine

section AffineTests
variable {R : Type u} [CommRing R] (b : Base R ⟶ S)

def affineFamily : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R := by
  letI := E.proper
  letI := E.dimension
  letI := E.connected
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact {
    curve := pullback E.p b
    projection := pullback.snd E.p b
    law := SchemeLocal.affineLaw b E.law
    commutative := SchemeLocal.affineLaw_comm E.law b
    proper := inferInstance
    smooth := MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    connected := inferInstance }

lemma affine_zero : (Affine.schemeFamily (affineFamily E b)).zero ≫ pullback.fst E.p b = b ≫ E.zero :=
  SchemeLocal.affineLaw_zero E b

lemma affine_multiplicative : ArithmeticThetaSchemeLevelR0204.Multiplicative E
    (Affine.schemeFamily (affineFamily E b)) b (pullback.fst E.p b) := by
  intro U t x y x' y' hx hy
  change (E.law.mul _ x' y').val = (pullback.lift _ _ _) ≫ pullback.fst E.p b
  rw [pullback.lift_fst]
  have hx' : x' = SchemeLocal.baseChangePointToBase b x := Subtype.ext hx
  have hy' : y' = SchemeLocal.baseChangePointToBase b y := Subtype.ext hy
  rw [hx', hy']

include b in
lemma primitive_on_affine [Algebra ℚ R] (m : ℕ) (hm : 0 < m)
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (c : Γ(S, ⊤)ˣ) (hc : Commutator E m M.x M.y α β c) :
    PrimitiveUnit m (Units.map b.appTop.hom.toMonoidHom c) := by
  let F := Affine.schemeFamily (affineFamily E b)
  let f := pullback.fst E.p b
  have hpb : IsPullback f F.p E.p b := IsPullback.of_hasPullback E.p b
  have hz : F.zero ≫ f = b ≫ E.zero := affine_zero E b
  have hmul := affine_multiplicative E b
  let N := ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.up E F b f hpb hz hmul (2*m) M
  have hx : N.x.val ≫ f = b ≫ M.x.val :=
    ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.lift_comp E F b f hpb M.x
  have hy : N.y.val ≫ f = b ≫ M.y.val :=
    ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.lift_comp E F b f hpb M.y
  exact Affine.primitive_scheme (affineFamily E b) m hm N _ _ _
    (commutator_transport E F b f hpb hz m hmul M.x M.y N.x N.y hx hy α β c hc)
end AffineTests

lemma sections_eq_of_affine_tests (a d : Γ(S, ⊤))
    (h : ∀ (R : Type u) [CommRing R] (b : Base R ⟶ S), b.appTop a = b.appTop d) : a = d := by
  apply TopCat.Presheaf.section_ext S.sheaf ⊤ a d
  intro x hx
  obtain ⟨R, b, hb, y, rfl⟩ := S.exists_Spec_apply_eq x
  letI := hb
  apply (asIso (b.stalkMap y)).commRingCatIsoToRingEquiv.injective
  change b.stalkMap y (S.presheaf.germ ⊤ (b y) hx a) =
    b.stalkMap y (S.presheaf.germ ⊤ (b y) hx d)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  exact congrArg ((Base R).presheaf.germ (b ⁻¹ᵁ ⊤) y hx) (h R b)

lemma isUnit_of_affine_tests (a : Γ(S, ⊤))
    (h : ∀ (R : Type u) [CommRing R] (b : Base R ⟶ S), IsUnit (b.appTop a)) : IsUnit a := by
  apply S.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
  intro x hx
  obtain ⟨R, b, hb, y, rfl⟩ := S.exists_Spec_apply_eq x
  apply (isUnit_map_iff (b.stalkMap y).hom _).mp
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact (h R b).map ((Base R).presheaf.germ (b ⁻¹ᵁ ⊤) y hx).hom

lemma primitive_global (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (m : ℕ) (hm : 0 < m) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (c : Γ(S, ⊤)ˣ) (hc : Commutator E m M.x M.y α β c) : PrimitiveUnit m c := by
  have hlocal : ∀ (R : Type u) [CommRing R] (b : Base R ⟶ S),
      PrimitiveUnit m (Units.map b.appTop.hom.toMonoidHom c) := by
    intro R _ b
    let φ : k →+* R := ((Scheme.ΓSpecIso (.of k)).inv ≫
      (b ≫ σ).appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom
    letI : Algebra ℚ R := (φ.comp (algebraMap ℚ k)).toAlgebra
    exact primitive_on_affine E b m hm M α β c hc
  constructor
  · apply Units.ext
    apply sections_eq_of_affine_tests
    intro R _ b
    have h := congrArg Units.val (hlocal R b).1
    simp only [Units.val_pow_eq_pow_val, Units.val_one, Units.coe_map, MonoidHom.coe_coe,
      map_pow, map_one] at h ⊢
    exact h
  · intro i hi
    apply isUnit_of_affine_tests
    intro R _ b
    have h := (hlocal R b).2 i hi
    simp only [Units.coe_map, MonoidHom.coe_coe, map_sub, map_pow, map_one] at h ⊢
    exact h

#print axioms line_invertible
#print axioms existsUnique_commutator
#print axioms thetaComparison
#print axioms commutator_transport
#print axioms Affine.commutator
#print axioms Affine.primitive
#print axioms Affine.primitive_scheme
#print axioms primitive_on_affine
#print axioms primitive_global
end SchemePrimitiveThetaCommutator

/-- The unique structural theta commutator is primitive on an arbitrary base. -/
theorem scheme_primitive_theta_commutator :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∀ (m : ℕ), 0 < m → Even m →
      ∀ M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m),
      ∀ (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m
        (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x))
        (β : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m
        (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y)),
      ∃! c : (S.presheaf.obj (Opposite.op ⊤))ˣ,
        ArithmeticThetaSchemeThetaMarkingR0259.Commutator E m M.x M.y α β c ∧
        ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c := by
  intro k _ _ S σ E m hm _ M α β
  obtain ⟨c, hc, hu⟩ := SchemePrimitiveThetaCommutator.existsUnique_commutator E m M.x M.y α β
  exact ⟨c, ⟨hc, SchemePrimitiveThetaCommutator.primitive_global E k σ m hm M α β c hc⟩,
    fun d hd => hu d hd.1⟩

#print axioms scheme_primitive_theta_commutator
end ArithmeticThetaSchemeThetaMarkingR0259
