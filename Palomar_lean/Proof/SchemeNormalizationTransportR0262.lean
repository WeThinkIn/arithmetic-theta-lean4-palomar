module

public import SchemeThetaNaturalityDefinitionsR0262
public import SchemeMidpointThetaLiftR0259
public import RelativeMidpointNaturalityR0258

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259
namespace NormalizationTransportProof
open SchemeDoubledTorsionLift
open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
open ArithmeticThetaRelativeThetaNaturalityR0258

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
  (hm : Multiplicative E F b f)

include hc hm

lemma inverse_commutes : inverse F ≫ f = f ≫ inverse E := by
  letI := pointCommGroup F F.p
  letI := pointCommGroup E (F.p ≫ b)
  have h := congrArg Subtype.val
    (map_inv (familyPointMap E F b f hc hm F.p)
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver F.p F.p))
  exact h.trans (point_inverse E (F.p ≫ b) ⟨f, hc.w⟩).symm

lemma point_eq (P : point E) (Q : point F) (hq : Q.val ≫ f = b ≫ P.val) :
    Q = restrictedPoint E F b f hc hm P := by
  apply Subtype.ext
  exact hc.hom_ext (hq.trans (restrictedPoint_comp E F b f hc hm P).symm)
    (Q.property.trans (restrictedPoint E F b f hc hm P).property.symm)

lemma translation_commutes (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val) :
    translation F Q ≫ f = f ≫ translation E P := by
  rw [point_eq E F b f hc hm P Q hq]
  exact translation_cartesian E F b f hc hm P

lemma negative_commutes (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val) :
    negative F Q ≫ f = b ≫ negative E P := by
  change (F.law.inv (𝟙 _) Q).val ≫ f = _
  rw [← point_inverse F, Category.assoc, inverse_commutes E F b f hc hm,
    ← Category.assoc, hq, Category.assoc, point_inverse E]
  rfl

omit hm in
lemma transported_eq (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (h : g' ≫ f = f ≫ g) (α : Lift E m g) :
    transportedLift E F b f hc hz m g g' h α =
      MidpointNaturalityProof.transport f (thetaComparison E F b f hc hz m) g g' h.symm α := by
  apply Iso.ext
  simp [transportedLift, MidpointNaturalityProof.transport, PullbackLifts.lift,
    PullbackLifts.squareNat, Scheme.Modules.pullbackCongr]

lemma inversion_corresponds (m : ℕ)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι') :
    LiftCorresponds E F b f hc hz m (inverse E) (inverse F) ι ι' := by
  let h := inverse_commutes E F b f hc hm
  refine ⟨h, ?_⟩
  rw [transported_eq]
  obtain ⟨φ, hφ, hu⟩ := SchemeThetaInversion.unique_fixed_lift F m
  obtain ⟨he, hi⟩ := hi.1
  obtain ⟨he', hi'⟩ := hi'.1
  have ht := InversionNaturalityProof.lift_fixed f b E.zero F.zero
    (inverse E) (inverse F) h.symm hz.symm he he' (thetaLine E m) ι hi
  have ht' := InversionNaturalityProof.conjugate_fixed F.zero (inverse F) he'
    (thetaComparison E F b f hc hz m) _ ht
  exact (hu _ hi').trans (hu _ ht').symm

omit hc hm

lemma transport_id {X Y : Scheme.{u}} (c : Y ⟶ X) {L : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj L ≅ N)
    (h : c ≫ 𝟙 X = 𝟙 Y ≫ c) :
    MidpointNaturalityProof.transport c e (𝟙 X) (𝟙 Y) h
      ((Scheme.Modules.pullbackId X).app L) = (Scheme.Modules.pullbackId Y).app N := by
  let a : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback (𝟙 X)).obj L) ≅
      (Scheme.Modules.pullback c).obj L := (Scheme.Modules.pullbackComp c (𝟙 X)).app L
  let d : (Scheme.Modules.pullback (𝟙 Y)).obj ((Scheme.Modules.pullback c).obj L) ≅
      (Scheme.Modules.pullback c).obj L := (Scheme.Modules.pullbackComp (𝟙 Y) c).app L
  have hl := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality c) L
  have hr := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality c) L
  change a.inv ≫ (Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackId X).hom.app L) ≫
    𝟙 _ = 𝟙 _ at hl
  change d.inv ≫ (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback c).obj L) ≫
    𝟙 _ = 𝟙 _ at hr
  simp only [Category.comp_id] at hl hr
  have hr' : d.hom = (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback c).obj L) := by
    apply (cancel_epi d.inv).mp
    rw [d.inv_hom_id]
    exact hr.symm
  have hn := (Scheme.Modules.pullbackId Y).hom.naturality e.inv
  apply Iso.ext
  change (Scheme.Modules.pullback (𝟙 Y)).map e.inv ≫
    ((d.hom ≫ (𝟙 ((Scheme.Modules.pullback c).obj L)) ≫ a.inv) ≫
      (Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackId X).hom.app L)) ≫ e.hom =
    (Scheme.Modules.pullbackId Y).hom.app N
  simp only [Category.comp_id, Category.assoc]
  rw [reassoc_of% hl, Category.id_comp, hr', ← Category.assoc, hn]
  simp

lemma transport_change {X Y : Scheme.{u}} (c : Y ⟶ X) {L : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj L ≅ N)
    {g k : X ⟶ X} {g' k' : Y ⟶ Y} (h : g = k) (h' : g' = k')
    (hg : c ≫ g = g' ≫ c) (hk : c ≫ k = k' ≫ c)
    (α : (Scheme.Modules.pullback k).obj L ≅ L) :
    MidpointNaturalityProof.transport c e g g' hg ((Scheme.Modules.pullbackCongr h).app L ≪≫ α) =
      (Scheme.Modules.pullbackCongr h').app N ≪≫
        MidpointNaturalityProof.transport c e k k' hk α := by
  subst k k'
  change MidpointNaturalityProof.transport c e g g' hg (Iso.refl _ ≪≫ α) =
    Iso.refl _ ≪≫ MidpointNaturalityProof.transport c e g g' hk α
  simp only [Iso.refl_trans]

lemma transport_square {X Y : Scheme.{u}} (c : Y ⟶ X) {L : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj L ≅ N)
    (g : X ⟶ X) (g' : Y ⟶ Y) (h : c ≫ g = g' ≫ c)
    (hg : g ≫ g = 𝟙 X) (hg' : g' ≫ g' = 𝟙 Y)
    (α : (Scheme.Modules.pullback g).obj L ≅ L)
    (ha : (Scheme.Modules.pullback g).mapIso α ≪≫ α =
      (Scheme.Modules.pullbackComp g g).app L ≪≫
        (Scheme.Modules.pullbackCongr hg).app L ≪≫ (Scheme.Modules.pullbackId X).app L) :
    let β := MidpointNaturalityProof.transport c e g g' h α
    (Scheme.Modules.pullback g').mapIso β ≪≫ β =
      (Scheme.Modules.pullbackComp g' g').app N ≪≫
        (Scheme.Modules.pullbackCongr hg').app N ≪≫ (Scheme.Modules.pullbackId Y).app N := by
  have hgg : c ≫ (g ≫ g) = (g' ≫ g') ≫ c := by rw [hg, hg']; simp
  have ha' : PullbackLifts.compLift g g α α =
      (Scheme.Modules.pullbackCongr hg).app L ≪≫ (Scheme.Modules.pullbackId X).app L := by
    unfold PullbackLifts.compLift
    rw [ha, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  have ht := MidpointNaturalityProof.transport_comp c e g g g' g' h h hgg α α
  rw [ha', transport_change c e hg hg' hgg (by simp), transport_id] at ht
  dsimp only
  apply Iso.ext
  have ht' := congrArg (fun z => ((Scheme.Modules.pullbackComp g' g').app N).hom ≫ z.hom) ht.symm
  simpa only [PullbackLifts.compLift, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using ht'

include hc hm

lemma reflection_commutes (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val) :
    reflection F Q ≫ f = f ≫ reflection E P := by
  change (translation F Q ≫ inverse F) ≫ f = f ≫ (translation E P ≫ inverse E)
  rw [Category.assoc, inverse_commutes E F b f hc hm, ← Category.assoc,
    translation_commutes E F b f hc hm P Q hq, Category.assoc]

lemma reflection_transport (m : ℕ) (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι')
    (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q))
    (ha : LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α') :
    MidpointNaturalityProof.transport f (thetaComparison E F b f hc hz m)
      (reflection E P) (reflection F Q) (reflection_commutes E F b f hc hm P Q hq).symm
      (reflectionLift E m P ι α) = reflectionLift F m Q ι' α' := by
  obtain ⟨hiMap, hiEq⟩ := inversion_corresponds E F b f hc hz hm m ι ι' hi hi'
  obtain ⟨haMap, haEq⟩ := ha
  rw [transported_eq] at hiEq haEq
  change MidpointNaturalityProof.transport f _ _ _ _
    (PullbackLifts.compLift _ _ α ι) = PullbackLifts.compLift _ _ α' ι'
  rw [MidpointNaturalityProof.transport_comp f _ _ _ _ _ haMap.symm hiMap.symm,
    ← haEq, ← hiEq]

lemma midpoint_transport (m : ℕ) (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι')
    (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q))
    (ha : LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α')
    (hn : MidpointNormalized E m P ι α) : MidpointNormalized F m Q ι' α' := by
  obtain ⟨hfix, hn⟩ := hn
  let hfix' := SchemeDoubledTorsionLift.reflection_fixed F Q
  have hp := InversionNaturalityProof.lift_fixed f b (negative E P) (negative F Q)
    (reflection E P) (reflection F Q) (reflection_commutes E F b f hc hm P Q hq).symm
    (negative_commutes E F b f hc hm P Q hq).symm hfix hfix' (thetaLine E m)
    (reflectionLift E m P ι α) hn
  have ht := InversionNaturalityProof.conjugate_fixed (negative F Q) (reflection F Q)
    hfix' (thetaComparison E F b f hc hz m) _ hp
  have he := reflection_transport E F b f hc hz hm m P Q hq ι ι' hi hi' α α' ha
  change (Scheme.Modules.pullback (negative F Q)).mapIso
    (MidpointNaturalityProof.transport f _ _ _ _ _) = _ at ht
  rw [he] at ht
  exact ⟨hfix', ht⟩

lemma symmetric_transport (m : ℕ) (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι')
    (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q))
    (ha : LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α')
    (hs : Symmetric E m P ι α) : Symmetric F m Q ι' α' := by
  obtain ⟨hsq, hs⟩ := hs
  let hsq' := SchemeMidpointThetaLift.reflection_square F Q
  have ht := transport_square f (thetaComparison E F b f hc hz m)
    (reflection E P) (reflection F Q) (reflection_commutes E F b f hc hm P Q hq).symm
    hsq hsq' (reflectionLift E m P ι α) hs
  dsimp only at ht
  rw [reflection_transport E F b f hc hz hm m P Q hq ι ι' hi hi' α α' ha] at ht
  exact ⟨hsq', ht⟩

lemma midpoint_corresponds (m : ℕ) (P : point E) (Q : point F)
    (hq : Q.val ≫ f = b ≫ P.val)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι')
    (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q))
    (hn : MidpointNormalized E m P ι α) (hn' : MidpointNormalized F m Q ι' α') :
    LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α' := by
  let h := translation_commutes E F b f hc hm P Q hq
  let β := transportedLift E F b f hc hz m _ _ h α
  have hb := midpoint_transport E F b f hc hz hm m P Q hq ι ι' hi hi' α β ⟨h, rfl⟩ hn
  obtain ⟨φ, hφ, hu⟩ := SchemeMidpointThetaLift.normalized_reflection F m Q
    ⟨reflectionLift F m Q ι' α'⟩
  obtain ⟨_, hβ⟩ := hb
  obtain ⟨_, hα'⟩ := hn'
  have he : reflectionLift F m Q ι' α' = reflectionLift F m Q ι' β :=
    (hu _ hα').trans (hu _ hβ).symm
  exact ⟨h, MidpointNaturalityProof.compLift_injective _ _ ι' he⟩

end NormalizationTransportProof

/-- Canonical transport preserves all the stated normalization conditions on arbitrary bases. -/
theorem scheme_normalization_transport :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
    ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
      (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve)
      (hc : CategoryTheory.IsPullback f F.p E.p b)
      (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero),
    ∀ m : ℕ, ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f →
      ArithmeticThetaSchemeThetaNaturalityR0262.NormalizationNatural E F b f hc hz m := by
  intro k _ _ S σ E T F b f hc hz m hm
  constructor
  · intro ι hi ι' hi'
    exact NormalizationTransportProof.inversion_corresponds E F b f hc hz hm m ι ι' hi hi'
  · intro P Q hq ι ι' hi hi' α α'
    constructor
    · intro ha
      exact ⟨NormalizationTransportProof.midpoint_transport E F b f hc hz hm m P Q hq
        ι ι' hi hi' α α' ha,
        NormalizationTransportProof.symmetric_transport E F b f hc hz hm m P Q hq
        ι ι' hi hi' α α' ha⟩
    · exact NormalizationTransportProof.midpoint_corresponds E F b f hc hz hm m P Q hq
        ι ι' hi hi' α α'

#print axioms scheme_normalization_transport
end ArithmeticThetaSchemeThetaNaturalityR0262
