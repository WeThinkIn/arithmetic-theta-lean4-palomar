import SchemeThetaMarkingDefinitionsR0259
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso

/-! Section cohomology for the actual conormal theta line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u v w

namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeThetaSectionCohomology
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeHodgeR0205
open scoped TensorProduct

/-- Invertibility uses the actual identity Cartier ideal, on every base. -/
lemma line_invertible {S : Scheme.{u}} (E : Family S) (m : ℕ) :
    Scheme.Modules.IsInvertible (thetaLine E m) :=
  ((CartesianIdentityIdeal.zero_ideal_invertible E).pow m).isInvertible_module.dual.1.tensor_monoidalV2
    (((((CartesianIdentityIdeal.zero_ideal_invertible E).isInvertible_module).pullback
      E.zero).tensorPow m).pullback E.p)

/-- Every affine test retains the same invertible line, with no flatness assumption. -/
lemma test_line_invertible {S : Scheme.{u}} (E : Family S) (m : ℕ)
    {R : Type u} [CommRing R] (b : Base R ⟶ S) :
    Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)) :=
  (line_invertible E m).pullback _

/-- Rank and projectivity are transported through the actual section equivalence. -/
lemma finiteProjectiveRank_equiv {R : Type u} [CommRing R]
    {V : Type v} {W : Type w} [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) (m : ℕ)
    (h : ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R V m) :
    ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R W m := by
  letI : Module.Finite R V := h.1
  letI : Module.Projective R V := h.2.1
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, ?_⟩
  intro K _ _ _
  let eK : K ⊗[R] V ≃ₗ[K] K ⊗[R] W := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e
  letI : Module.Finite K (K ⊗[R] V) := (h.2.2 K).1
  exact ⟨Module.Finite.equiv eK, eK.finrank_eq.symm.trans (h.2.2 K).2⟩

/-- Canonical section base change for an affine structural map. -/
def CanonicalBaseChange {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Base R) (L : X.Modules) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    let t := Scheme.TwoAffineOpenCover.specMap R A
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f t)
      ((Scheme.Modules.pullback (pullback.fst f t)).obj L) ((pullback.fst f t) ⁻¹ᵁ ⊤)
    ∃ e : A ⊗[R] Γ(L, ⊤) ≃ₗ[A]
        Γ((Scheme.Modules.pullback (pullback.fst f t)).obj L, (pullback.fst f t) ⁻¹ᵁ ⊤),
      ∀ (a : A) (s : Γ(L, ⊤)),
        e (a ⊗ₜ[R] s) = a • Scheme.Modules.pullbackLocalSection (pullback.fst f t) s

/-- An isomorphism of sheaves preserves the canonical pure-tensor formula. -/
lemma canonicalBaseChange_iso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Base R) {L M : X.Modules} (e : L ≅ M)
    (h : CanonicalBaseChange f L) : CanonicalBaseChange f M := by
  intro A _ _
  let t := Scheme.TwoAffineOpenCover.specMap R A
  let g := pullback.fst f t
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f t)
    ((Scheme.Modules.pullback g).obj L) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f t)
    ((Scheme.Modules.pullback g).obj M) ⊤
  let e₀ := ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv f e
  let e₁ := ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv
    (pullback.snd f t) ((Scheme.Modules.pullback g).mapIso e)
  obtain ⟨β, hβ⟩ := h A
  refine ⟨((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e₀.symm).trans β).trans e₁, ?_⟩
  intro a s
  change e₁ (β ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e₀.symm) (a ⊗ₜ[R] s))) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, hβ, map_smul]
  congr 1
  change ((Scheme.Modules.pullback g).map e.hom).app ⊤
    (Scheme.Modules.pullbackLocalSection g (e.inv.app ⊤ s)) = _
  have hn := Scheme.Modules.pullbackLocalSection_app g e.hom (e.inv.app ⊤ s)
  have he : e.hom.app ⊤ (e.inv.app ⊤ s) = s := by
    change (e.inv ≫ e.hom).app ⊤ s = s
    rw [e.inv_hom_id]
    rfl
  exact hn.symm.trans (congrArg (Scheme.Modules.pullbackLocalSection g) he)

/-- The accepted Noetherian affine theorem applies to the conormal line through
the prescribed derivative comparison, without selecting a Hodge frame. -/
lemma affine_noetherian_sections {R : Type u} [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (F : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R)
    (m : ℕ) (hm : 0 < m) :
    let E := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F
    let L := thetaLine E m
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection L ⊤
     ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m) ∧
    CanonicalBaseChange F.projection L := by
  letI := ArithmeticThetaRelativeSchrodingerR0257.sectionModule F m
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection
    (thetaLine (ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F) m) ⊤
  obtain ⟨hr, hb⟩ := ArithmeticThetaRelativeSchrodingerR0257.relative_theta_sections_cohomology
    R F m hm
  let e := (affineThetaComparison F m).symm
  exact ⟨finiteProjectiveRank_equiv
    (ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv F.projection e)
    m hr, canonicalBaseChange_iso F.projection e hb⟩

open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Cartier powers and their duals commute with the actual pointed Cartesian square. -/
def originPowerComparison {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dual (E.zero.ker ^ m).module) ≅
      Scheme.Modules.dual (F.zero.ker ^ m).module := by
  let e := idealPullbackIso f (E.zero.ker ^ m) (F.zero.ker ^ m)
    ((CartesianIdentityIdeal.zero_ideal_invertible E).pow m)
    ((CartesianIdentityIdeal.zero_ideal_invertible F).pow m)
    (by rw [comap_power, CartesianIdentityIdeal.ideal_comap E F b f hc hz])
  letI := dualComparison_isIso f (E.zero.ker ^ m).module
    ((CartesianIdentityIdeal.zero_ideal_invertible E).pow m).isInvertible_module
  exact asIso (dualComparison f _) ≪≫
    ((MonoidalClosed.internalHom (C := F.curve.Modules)).mapIso e.symm.op).app
      (𝟙_ F.curve.Modules)

/-- The conormal theta line comparison is built from the identity ideal and the
pointed Cartesian square. No frame or unspecified line is supplied. -/
def thetaComparison {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine F m := by
  let i := idealPullbackIso f E.zero.ker F.zero.ker
    (CartesianIdentityIdeal.zero_ideal_invertible E)
    (CartesianIdentityIdeal.zero_ideal_invertible F)
    (CartesianIdentityIdeal.ideal_comap E F b f hc hz)
  let eH := cotangentComparison E F b f hz i
  let eW := Scheme.Modules.pullbackTensorPowIso b (Cotangent E) m ≪≫
    Scheme.Modules.tensorPowMapIso eH m
  exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    (originPowerComparison E F b f hc hz m ⊗ᵢ
      ((Scheme.Modules.pullbackComp f E.p).app _ ≪≫
        (Scheme.Modules.pullbackCongr hc.w).app _ ≪≫
        ((Scheme.Modules.pullbackComp F.p b).app _).symm ≪≫
        (Scheme.Modules.pullback F.p).mapIso eW))

/-- The elliptic family on an affine test is the actual fibre product. -/
def affineTestFamily {S : Scheme.{u}} (E : Family S) {R : Type u} [CommRing R]
    (b : Base R ⟶ S) : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R := by
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
    smooth := inferInstance
    connected := inferInstance }

/-- Pulling back the global conormal theta line gives the conormal theta line
of the same affine test family, through the specified Cartier comparison. -/
def affineTestComparison {S : Scheme.{u}} (E : Family S) {R : Type u} [CommRing R]
    (b : Base R ⟶ S) (m : ℕ) :
    (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m) ≅
      thetaLine
        (ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily
          (affineTestFamily E b)) m :=
  thetaComparison E
    (ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily
      (affineTestFamily E b))
    b (pullback.fst E.p b) (IsPullback.of_hasPullback E.p b)
    (SchemeLocal.affineLaw_zero E b) m

/-- The full section statement on each Noetherian rational affine test of an
arbitrary scheme base, retaining the actual global line and pure-tensor formula.
The arbitrary-ring extension is proved below in `affine_test`. -/
lemma noetherian_affine_test {S : Scheme.{u}} (E : Family S)
    (m : ℕ) (hm : 0 < m) {R : Type u} [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (b : Base R ⟶ S) :
    let f := pullback.snd E.p b
    let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
     ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m) ∧
    CanonicalBaseChange f L := by
  let F := affineTestFamily E b
  let G := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F
  let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection (thetaLine G m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection L ⊤
  obtain ⟨hr, hb⟩ := affine_noetherian_sections F m hm
  let e := (affineTestComparison E b m).symm
  exact ⟨finiteProjectiveRank_equiv
    (ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv F.projection e)
    m hr, canonicalBaseChange_iso F.projection e hb⟩

/-! Extend the accepted finite-stage scheme and group descent to unframed
elliptic families. The arguments use the actual proper smooth map and law;
no global Hodge frame is introduced. -/
namespace FiniteStage
open GoodReductionJacobian
open ArithmeticThetaLocalWeierstrassR0203.FiniteTypeApproximation

/-- Finite presentation follows from the actual smooth proper geometry. -/
theorem finite_presentation (R : Type u) [CommRing R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    LocallyOfFinitePresentation Q.projection ∧ QuasiCompact Q.projection ∧
      QuasiSeparated Q.projection := by
  letI : SmoothOfRelativeDimension 1 Q.projection := Q.smooth
  letI : IsProper Q.projection := Q.proper
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Effective finite-type descent of the underlying scheme and structural map.
The group operations, connected fibres and relative dimension are retained
in subsequent lemmas for the final elliptic model. -/
theorem underlying_scheme_descent
    {A₀ : Type u} [CommRing A₀]
    (R : Type u) [CommRing R] [Algebra A₀ R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra A₀ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.curve ⟶ X),
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        IsPullback π Q.projection f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  obtain ⟨hlfp, hqc, hqs⟩ := finite_presentation R Q
  letI := hlfp
  letI := hqc
  letI := hqs
  obtain ⟨T, hT, _, X, f, π, hs⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := A₀) Q.projection ∅
  exact ⟨T, hT, X, f, π, hs⟩

/-- The underlying model can be chosen over a finitely generated rational
subalgebra, with no nontriviality, reducedness or domain hypothesis on `R`. -/
theorem rational_scheme_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.curve ⟶ X),
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        IsPullback π Q.projection f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  letI : Algebra (ULift.{u} ℚ) R := ULift.algebra' ℚ R
  letI : IsScalarTower ℚ (ULift.{u} ℚ) R :=
    IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ULift.{u} ℚ) (A := R) fun r => rfl
  obtain ⟨T, hT, X, f, π, hs⟩ := underlying_scheme_descent (A₀ := ULift.{u} ℚ) R Q
  letI : Algebra.FiniteType ℚ (ULift.{u} ℚ) :=
    Algebra.FiniteType.equiv inferInstance (ULift.algEquiv : ULift.{u} ℚ ≃ₐ[ℚ] ℚ).symm
  letI : Algebra.FiniteType (ULift.{u} ℚ) T := T.fg_iff_finiteType.mp hT
  have hTQ : (T.restrictScalars ℚ).FG := by
    apply (T.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := ULift.{u} ℚ) (A := T)
      inferInstance inferInstance
  exact ⟨T.restrictScalars ℚ, hTQ, X, f, π, hs⟩

/-- Properness and flatness can be retained on the rational finite-type model.
The group law and relative dimension are not asserted here. -/
theorem rational_proper_flat_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.curve ⟶ X),
        IsProper f ∧ Flat f ∧
        IsPullback π Q.projection f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  letI : Algebra (ULift.{u} ℚ) R := ULift.algebra' ℚ R
  letI : IsScalarTower ℚ (ULift.{u} ℚ) R :=
    IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ULift.{u} ℚ) (A := R) fun r => rfl
  letI : SmoothOfRelativeDimension 1 Q.projection := Q.smooth
  letI : IsProper Q.projection := Q.proper
  obtain ⟨T, hT, _, X, f, π, hs⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := ULift.{u} ℚ) Q.projection ∅
  letI : Algebra.FiniteType ℚ (ULift.{u} ℚ) :=
    Algebra.FiniteType.equiv inferInstance (ULift.algEquiv : ULift.{u} ℚ ≃ₐ[ℚ] ℚ).symm
  letI : Algebra.FiniteType (ULift.{u} ℚ) T := T.fg_iff_finiteType.mp hT
  have hTQ : (T.restrictScalars ℚ).FG := by
    apply (T.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := ULift.{u} ℚ) (A := T)
      inferInstance inferInstance
  exact ⟨T.restrictScalars ℚ, hTQ, X, f, π, hs⟩

/-- Smoothness can also be retained after enlarging the finite rational stage.
The Cartesian comparison remains the map induced by the same structural maps. -/
theorem rational_smooth_proper_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.curve ⟶ X),
        IsProper f ∧ Smooth f ∧
        IsPullback π Q.projection f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  obtain ⟨T, hT, X, f, π, hp, hf, hπ⟩ := rational_proper_flat_descent R Q
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℚ T
  letI := hp
  letI := hf
  letI : SmoothOfRelativeDimension 1 Q.projection := Q.smooth
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  haveI : Smooth (pullback.snd f b) := by
    rw [← hπ.isoPullback_inv_snd]
    infer_instance
  obtain ⟨U, hU, _, hsm⟩ :=
    AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd f (A := R) ∅
  let v : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T U))
  let c : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  have hcv : c ≫ v = b := by
    dsimp [c, v, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let π' : Q.curve ⟶ pullback f v :=
    pullback.lift π (Q.projection ≫ c) (by rw [Category.assoc, hcv, hπ.w])
  have hπ' : IsPullback π' Q.projection (pullback.snd f v) c := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f v) (h₂₂ := v) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f v)
    rw [pullback.lift_fst, hcv]
    exact hπ
  letI : Algebra.FiniteType T U := U.fg_iff_finiteType.mp hU
  have hUQ : (U.restrictScalars ℚ).FG := by
    apply (U.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := T) (A := U) inferInstance inferInstance
  exact ⟨U.restrictScalars ℚ, hUQ, pullback f v, pullback.snd f v, π',
    inferInstance, hsm, hπ'⟩

private theorem mul_val_congr
    {S : Type u} [CommRing S] {X Z : Scheme.{u}} {f : X ⟶ Base S}
    (L : RelativeGroupLaw S f) {t₁ t₂ : Z ⟶ Base S} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f)
    (hx : x₁.val = x₂.val) (hy : y₁.val = y₂.val) :
    (L.mul t₁ x₁ y₁).val = (L.mul t₂ x₂ y₂).val := by
  subst t₂
  cases Subtype.ext hx
  cases Subtype.ext hy
  rfl

/-- Commutativity follows through the same checked multiplication comparison. -/
lemma commutative_of_iso {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Base R} {g : Y ⟶ Base R}
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g)
    (e : X ≅ Y) (he : e.hom ≫ g = f) (hL : L.IsCommutative)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t f),
      (M.mul t ⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩
        ⟨y.val ≫ e.hom, by rw [Category.assoc, he, y.property]⟩).val =
        (L.mul t x y).val ≫ e.hom) : M.IsCommutative := by
  intro T t x y
  have hi : e.inv ≫ f = g := by rw [← he, Iso.inv_hom_id_assoc]
  let x' : SchemeHomOver t f := ⟨x.val ≫ e.inv, by rw [Category.assoc, hi, x.property]⟩
  let y' : SchemeHomOver t f := ⟨y.val ≫ e.inv, by rw [Category.assoc, hi, y.property]⟩
  have hxy := hmul t x' y'
  have hyx := hmul t y' x'
  simp only [x', y', Category.assoc, Iso.inv_hom_id, Category.comp_id] at hxy hyx
  apply Subtype.ext
  exact hxy.trans ((congrArg (fun z : SchemeHomOver t f => z.val ≫ e.hom)
    (hL t x' y')).trans hyx.symm)

/-- The actual group law descends on a smooth proper rational finite-type model,
with multiplication preserved on every scheme-valued point. -/
theorem rational_smooth_proper_group_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (L : RelativeGroupLaw T f)
        (π : Q.curve ⟶ X)
        (hπ : IsPullback π Q.projection f
          (Spec.map (CommRingCat.ofHom (algebraMap T R)))),
        L.IsCommutative ∧ IsProper f ∧ Smooth f ∧
        ∀ (Z : Scheme.{u}) (t : Z ⟶ Base R) (x y : SchemeHomOver t Q.projection),
          (Q.law.mul t x y).val ≫ π =
            (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap T R)))
              ⟨x.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, x.property]⟩
              ⟨y.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, y.property]⟩).val := by
  obtain ⟨T, hT, X, f, π, hp, hs, hπ⟩ := rational_smooth_proper_descent R Q
  letI := hp
  letI := hs
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  let e : Q.curve ≅ pullback f b := hπ.isoPullback
  have he : e.hom ≫ pullback.snd f b = Q.projection := hπ.isoPullback_hom_snd
  obtain ⟨LR, hLR, _⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso e he Q.law
  obtain ⟨U, hU, _, LU, c, hciso, hc, _, hmul, hcomm⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      f LR ∅
  letI := hciso
  let v : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T U))
  let a : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  let fU := pullback.snd f v
  let π' : Q.curve ⟶ pullback f v := (e.hom ≫ c) ≫ pullback.fst fU a
  have hc' : (e.hom ≫ c) ≫ pullback.snd fU a = Q.projection := by
    rw [Category.assoc, hc, he]
  have hpb : IsPullback (e.hom ≫ c) Q.projection (pullback.snd fU a) (𝟙 (Base R)) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hc'⟩
  have hπ' : IsPullback π' Q.projection fU a := by
    simpa only [Category.id_comp] using hpb.paste_horiz (IsPullback.of_hasPullback fU a)
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : Algebra.FiniteType T U := U.fg_iff_finiteType.mp hU
  have hUQ : (U.restrictScalars ℚ).FG := by
    apply (U.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := T) (A := U) inferInstance inferInstance
  refine ⟨U.restrictScalars ℚ, hUQ, pullback f v, fU, LU, π', hπ', hcomm (commutative_of_iso Q.law LR e he Q.commutative hLR),
    inferInstance, inferInstance, ?_⟩
  intro Z t x y
  let xe : SchemeHomOver t (pullback.snd f b) :=
    ⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩
  let ye : SchemeHomOver t (pullback.snd f b) :=
    ⟨y.val ≫ e.hom, by rw [Category.assoc, he, y.property]⟩
  have h1 : (LR.mul t xe ye).val = (Q.law.mul t x y).val ≫ e.hom := hLR t x y
  have h2 := congrArg (fun z => z ≫ pullback.fst fU a) (hmul t xe ye)
  rw [h1] at h2
  simp only [fU, a, v, RelativeGroupLaw.baseChange_mul,
    RelativeGroupLaw.baseChangePointOfBase_coe, RelativeGroupLaw.baseChangePointToBase,
    pullback.lift_fst] at h2
  refine (show (Q.law.mul t x y).val ≫ π' = _ from by
    simpa only [π', fU, a, v, Category.assoc] using h2).trans ?_
  apply mul_val_congr LU
  · rfl
  · simp only [xe, π', fU, a, v, Category.assoc]
  · simp only [ye, π', fU, a, v, Category.assoc]


theorem connected_fibre_at_scalar_image
    (R : Type u) [CommRing R] (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R)
    {T : Type u} [CommRing T] (α : T →+* R)
    {X : Scheme.{u}} (f : X ⟶ Base T) (π : Q.curve ⟶ X)
    (sq : IsPullback π Q.projection f (Spec.map (CommRingCat.ofHom α)))
    (p : Base R) :
    GeometricallyConnected
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom α)) p)) := by
  letI := Q.connected
  let b := Spec.map (CommRingCat.ofHom α)
  letI : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      @Surjective := GeometricallyConnected.descendsAlong_surjective
  have hb : Surjective (Spec.map (b.residueFieldMap p)) := by
    refine ⟨fun x => ⟨IsLocalRing.closedPoint _, ?_⟩⟩
    exact Subsingleton.elim _ _
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected)
    (Q := @Surjective) (isPullback_fiberToSpecResidueField_of_isPullback sq p).flip hb inferInstance

/-- Every unframed rational elliptic family descends to a finite rational stage
with the actual pointed Cartesian comparison. Empty bases are included. -/
theorem elliptic_approximation (R : Type u) [CommRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (F : ArithmeticThetaLegendreAtlasR0176.EllipticFamily T) (π : Q.curve ⟶ F.curve),
        IsPullback π Q.projection F.projection
          (Spec.map (CommRingCat.ofHom (algebraMap T R))) ∧
        (Q.law.one (𝟙 _)).val ≫ π =
          Spec.map (CommRingCat.ofHom (algebraMap T R)) ≫ (F.law.one (𝟙 _)).val := by
  obtain ⟨T, hT, X, f, L, π, sq, hcomm, hp, hs, hm⟩ :=
    rational_smooth_proper_group_descent R Q
  letI := hp
  letI := hs
  letI := Q.smooth
  have hd : SmoothOfRelativeDimension 1 f :=
    smooth_dimension_of_dense_comparison f Q.projection π _ sq 1
      (dense_comparison_of_injective f Q.projection π (algebraMap T R) sq Subtype.val_injective)
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
  let π' : Q.curve ⟶ pullback f c :=
    pullback.lift π (Q.projection ≫ b) (by rw [Category.assoc, hbc, sq.w])
  have sq' : IsPullback π' Q.projection fU b := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f c) (h₂₂ := c) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f c)
    rw [pullback.lift_fst, hbc]
    exact sq
  have hm' := multiplication_lift Q.law L a b c hbc π sq.w π'
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hm
  have hz' : (Q.law.one (𝟙 _)).val ≫ π' = b ≫ (LU.one (𝟙 _)).val := by
    apply origin_eq_of_mul_eq Q.law LU b π' sq'.w
    intro Z t x y
    exact (hm' Z t x y _ _ rfl rfl).symm
  let model : ArithmeticThetaLegendreAtlasR0176.EllipticFamily U := {
    curve := pullback f c
    projection := fU
    law := LU
    commutative := RelativeGroupLaw.IsCommutative.baseChange c hcomm
    proper := inferInstanceAs (IsProper (pullback.snd f c))
    smooth := inferInstance
    connected := inferInstance }
  exact ⟨U, hU, model, π', sq', hz'⟩

end FiniteStage

/-- Canonical base change propagates along a Cartesian square and the specified
line comparison, including nonflat scalar maps. -/
lemma canonicalBaseChange_descend {T R : Type u} [CommRing T] [CommRing R]
    {Y X : Scheme.{u}} (f₀ : Y ⟶ Base T) (L₀ : Y.Modules)
    (h₀ : CanonicalBaseChange f₀ L₀) (α : T →+* R)
    (f : X ⟶ Base R) (g : X ⟶ Y)
    (hg : IsPullback g f f₀ (Spec.map (CommRingCat.ofHom α)))
    (L : X.Modules) (e : (Scheme.Modules.pullback g).obj L₀ ≅ L) :
    CanonicalBaseChange f L := by
  intro A _ _
  have hf : f.appTop = f.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE f
  have H := Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
    f₀ L₀
    (fun B _ ψ X' f' g' hg' =>
      Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
        f₀ L₀ h₀ B ψ X' f' g' hg')
    α f g hg L e A (algebraMap R A) _ _ _ (IsPullback.of_hasPullback f _)
  rw [toAlgebra_algebraMap, hf] at H
  exact H

/-- Finite projectivity and geometric rank are preserved by arbitrary scalar extension. -/
lemma finiteProjectiveRank_baseChange {T R : Type u} [CommRing T] [CommRing R]
    [Algebra T R] {V : Type v} [AddCommGroup V] [Module T V] (m : ℕ)
    (h : ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank T V m) :
    ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R (R ⊗[T] V) m := by
  letI := h.1
  letI := h.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro K _ _ _
  letI : Algebra T K := ((algebraMap R K).comp (algebraMap T R)).toAlgebra
  letI : IsScalarTower T R K := IsScalarTower.of_algebraMap_eq' rfl
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange T R K K V
  exact ⟨inferInstance, e.finrank_eq.trans (h.2.2 K).2⟩

/-- The section space itself is scalar extension along the actual Cartesian map. -/
lemma sections_equiv_of_cartesian {T R : Type u} [CommRing T] [CommRing R]
    [Algebra T R] {Y X : Scheme.{u}} (f₀ : Y ⟶ Base T) (L₀ : Y.Modules)
    (h₀ : CanonicalBaseChange f₀ L₀) (f : X ⟶ Base R) (g : X ⟶ Y)
    (hg : IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap T R))))
    (L : X.Modules) (e : (Scheme.Modules.pullback g).obj L₀ ≅ L) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f₀ L₀ ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
    Nonempty (R ⊗[T] Γ(L₀, ⊤) ≃ₗ[R] Γ(L, ⊤)) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f₀ L₀ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f ((Scheme.Modules.pullback g).obj L₀) ⊤
  have H := Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
    f₀ L₀ h₀ R (algebraMap T R) X f g hg
  have hf : f₀.appTop = f₀.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE f₀
  rw [toAlgebra_algebraMap, hf] at H
  obtain ⟨β, _⟩ := H
  exact ⟨β.trans (ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv f e)⟩

/-- The Noetherian stage is eliminated for the actual conormal theta line. -/
lemma affine_sections {R : Type u} [CommRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) (m : ℕ) (hm : 0 < m) :
    let E := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily Q
    let L := thetaLine E m
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.projection L ⊤
     ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m) ∧
    CanonicalBaseChange Q.projection L := by
  obtain ⟨T, hT, F, g, hg, hz⟩ := FiniteStage.elliptic_approximation R Q
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℚ T
  let E := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily Q
  let E₀ := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F
  let L := thetaLine E m
  let L₀ := thetaLine E₀ m
  let e : (Scheme.Modules.pullback g).obj L₀ ≅ L :=
    thetaComparison E₀ E (Spec.map (CommRingCat.ofHom (algebraMap T R))) g hg hz m
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection L₀ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.projection L ⊤
  obtain ⟨hr, hb⟩ := affine_noetherian_sections F m hm
  obtain ⟨β⟩ := sections_equiv_of_cartesian F.projection L₀ hb Q.projection g hg L e
  exact ⟨finiteProjectiveRank_equiv β m (finiteProjectiveRank_baseChange m hr),
    canonicalBaseChange_descend F.projection L₀ hb (algebraMap T R) Q.projection g hg L e⟩

/-- Every rational affine test, without Noetherian or flatness restrictions. -/
lemma affine_test {S : Scheme.{u}} (E : Family S)
    (m : ℕ) (hm : 0 < m) {R : Type u} [CommRing R] [Algebra ℚ R]
    (b : Base R ⟶ S) :
    let f := pullback.snd E.p b
    let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
     ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m) ∧
    CanonicalBaseChange f L := by
  let F := affineTestFamily E b
  let G := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F
  let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection (thetaLine G m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.projection L ⊤
  obtain ⟨hr, hb⟩ := affine_sections F m hm
  let e := (affineTestComparison E b m).symm
  exact ⟨finiteProjectiveRank_equiv
    (ArithmeticThetaRelativeThetaNaturalityR0258.SectionIntertwining.sectionsEquiv F.projection e)
    m hr, canonicalBaseChange_iso F.projection e hb⟩

end SchemeThetaSectionCohomology

open CategoryTheory

/-- Positive-degree theta sections have finite projective geometric rank and
canonical arbitrary scalar extension on every affine test of the given scheme. -/
theorem scheme_theta_section_cohomology :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∀ m : ℕ, 0 < m → SectionFacts E m := by
  intro k _ _ S σ E m hm R _ b
  let scalar : k →+* R := (AlgebraicGeometry.Spec.preimage (b ≫ σ)).hom
  letI : Algebra k R := scalar.toAlgebra
  letI : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ k)
  exact SchemeThetaSectionCohomology.affine_test E m hm b

end ArithmeticThetaSchemeThetaMarkingR0259

#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.line_invertible
#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.test_line_invertible
#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.affine_noetherian_sections
#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.thetaComparison
#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.noetherian_affine_test

#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.FiniteStage.rational_smooth_proper_group_descent

#print axioms ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.FiniteStage.elliptic_approximation
#print axioms ArithmeticThetaSchemeThetaMarkingR0259.scheme_theta_section_cohomology
