module

public import ConormalInitialDefinitionsR0162
public import GeometricDiscriminantInitialR0161

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ArithmeticThetaConormalInitialR0162
namespace ActualOriginAugmentedTaylorR0162
open CategoryTheory AlgebraicGeometry

private lemma scalar_eval {R S : Type} [CommRing R] [CommRing S]
    {X : Scheme} (f : X ⟶ Spec (.of R)) (g : Spec (.of S) ⟶ X)
    (ρ : R →+* S) (h : g ≫ f = Spec.map (CommRingCat.ofHom ρ)) :
    (Scheme.ΓSpecIso (.of S)).hom.hom.comp
      (g.appTop.hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)) = ρ := by
  apply CommRingCat.hom_ext_iff.mp
  change (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ g.appTop ≫
    (Scheme.ΓSpecIso (.of S)).hom = CommRingCat.ofHom ρ
  rw [← Scheme.Hom.comp_appTop_assoc, h, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

private lemma stalk_eval {S : Type} [CommRing S] {X : Scheme} (x : X)
    (η : X.presheaf.stalk x →+* S) :
    (Scheme.ΓSpecIso (.of S)).hom.hom.comp
      ((Spec.map (CommRingCat.ofHom η) ≫ X.fromSpecStalk x).appTop.hom) =
    η.comp (X.presheaf.germ ⊤ x (by trivial)).hom := by
  apply CommRingCat.hom_ext_iff.mp
  change (Spec.map (CommRingCat.ofHom η) ≫ X.fromSpecStalk x).appTop ≫
    (Scheme.ΓSpecIso (.of S)).hom = X.presheaf.germ ⊤ x _ ≫ CommRingCat.ofHom η
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  change X.presheaf.germ ⊤ x _ ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
    (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom ≫ CommRingCat.ofHom η = _
  rw [Iso.inv_hom_id_assoc]

private def stalkScalar {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by trivial)).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

private lemma stalk_scalar {R S : Type} [CommRing R] [CommRing S]
    {X : Scheme} (f : X ⟶ Spec (.of R)) (x : X)
    (η : X.presheaf.stalk x →+* S) (ρ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom η) ≫ X.fromSpecStalk x ≫ f =
      Spec.map (CommRingCat.ofHom ρ)) :
    η.comp (stalkScalar f x) = ρ := by
  have hh := scalar_eval f (Spec.map (CommRingCat.ofHom η) ≫ X.fromSpecStalk x)
    ρ (by simpa only [Category.assoc] using h)
  rw [← RingHom.comp_assoc, stalk_eval] at hh
  exact hh

private lemma stalkScalar_comp {R B : Type} [CommRing R] [CommRing B]
    {X : Scheme} (f : X ⟶ Spec (.of R)) (x : X) (ι : B →+* R) :
    stalkScalar (f ≫ Spec.map (CommRingCat.ofHom ι)) x = (stalkScalar f x).comp ι := by
  have hh : (Scheme.ΓSpecIso (.of B)).inv ≫
      (f ≫ Spec.map (CommRingCat.ofHom ι)).appTop ≫ X.presheaf.germ ⊤ x (by trivial) =
      CommRingCat.ofHom ι ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by trivial) := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg CommRingCat.Hom.hom hh

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

private lemma taylor_scalar (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k))
    (hκ : IsOriginTaylor k M s hs (Ψ.comp φ) κ) :
    κ.comp (originScalar k M s hs) = PowerSeries.C := by
  let x := Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k))
  let η := φ.comp (algebraMap (OriginStalk k M s hs) (genericScheme k M).functionField)
  have hgeom : Spec.map (CommRingCat.ofHom η) ≫ (genericScheme k M).fromSpecStalk x ≫
      (genericStructure k M ≫ genericBase k) =
      Spec.map (CommRingCat.ofHom ((chartToField k).comp
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k))) := by
    change Spec.map (CommRingCat.ofHom (algebraMap (OriginStalk k M s hs) _) ≫
      CommRingCat.ofHom φ) ≫ _ ≫ _ = _
    have hi : Spec.map (CommRingCat.ofHom (algebraMap (OriginStalk k M s hs)
        (genericScheme k M).functionField)) ≫ (genericScheme k M).fromSpecStalk x =
        (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk
        ((_root_.genericPoint_spec (genericScheme k M)).specializes trivial)
    rw [Spec.map_comp, Category.assoc, ← Category.assoc _ _ (genericStructure k M ≫ _), hi]
    have hp : genericStructure k M ≫ genericBase k = genericInclusion k M ≫ M.p :=
      CategoryTheory.Limits.pullback.condition.symm
    rw [hp, ← Category.assoc _ (genericInclusion k M), ← Category.assoc, hφ,
      Category.assoc, hχ]
    exact (Spec.map_comp _ _).symm
  have hv := stalk_scalar (genericStructure k M ≫ genericBase k) x η
    ((chartToField k).comp (ArithmeticThetaAnnularTorsionPrereqR0053.base k)) hgeom
  change η.comp (stalkScalar (genericStructure k M ≫ Spec.map
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) x) = _ at hv
  rw [stalkScalar_comp] at hv
  have ht : (Ψ.comp η).comp (originScalar k M s hs) =
      (HahnSeries.ofPowerSeries ℤ (LaurentSeries k)).comp PowerSeries.C := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries k)
    intro b
    change Ψ (η (originScalar k M s hs (algebraMap (PowerSeries k) (LaurentSeries k) b))) = _
    rw [show η (originScalar k M s hs (algebraMap (PowerSeries k) (LaurentSeries k) b)) =
      chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) from
      RingHom.congr_fun hv b]
    rw [show Ψ (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) =
      toIterated k (σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) from
      RingHom.congr_fun hΨ _]
    rw [hσ.1]
    simp only [toIterated, RingHom.comp_apply, PowerSeries.map_C]
    rfl
  apply RingHom.ext
  intro c
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k)
  exact (hκ.1 _).trans (RingHom.congr_fun ht c)

end ActualOriginAugmentedTaylorR0162

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ActualOriginAugmentedTaylorR0162

/-- The accepted actual identity Taylor map is an augmented algebra map for
exactly the structural-germ scalar action, with its regular nonzero ideal. -/
theorem actual_origin_augmented_taylor :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ArithmeticThetaConormalInitialR0162.OriginAugmentedTaylor k M s hs.1 := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _
  obtain ⟨g, hg, _⟩ := geometric_discriminant_initial k r hr h3 he T M hM s hs G hG
  obtain ⟨χ, φ, σ, Ψ, κ, hχ, hφ, hσ, hΨ, hκ, _⟩ := hg.2
  have hscalar := taylor_scalar k M s hs.1 (χ (zeroIndex r hr)) (hχ _).1
    (φ (zeroIndex r hr)) (hφ _) σ hσ Ψ hΨ κ hκ
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs.1) :=
    (originScalar k M s hs.1).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs.1) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs.1).toAlgebra
  let κa : OriginStalk k M s hs.1 →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k) :=
    { κ with commutes' := fun c => RingHom.congr_fun hscalar c }
  let εa : OriginStalk k M s hs.1 →ₐ[LaurentSeries k] LaurentSeries k :=
    { (Scheme.stalkClosedPointTo (Origin k M s hs.1)).hom with
      commutes' := by
        intro c
        change Scheme.stalkClosedPointTo (Origin k M s hs.1)
          (originScalar k M s hs.1 c) = c
        rw [← hκ.2.1]
        exact (congrArg PowerSeries.constantCoeff (RingHom.congr_fun hscalar c)).trans
          (PowerSeries.constantCoeff_C c) }
  have hker : ideal εa = IsLocalRing.maximalIdeal (OriginStalk k M s hs.1) := by
    apply IsLocalRing.ker_eq_maximalIdeal
    intro c
    exact ⟨algebraMap (LaurentSeries k) (OriginStalk k M s hs.1) c, εa.commutes c⟩
  let e := Origin k M s hs.1
  let x := e (IsLocalRing.closedPoint (LaurentSeries k))
  letI : IsClosedImmersion e := genericPoint_closed k M hM s hs.1
  have hx : IsClosed ({x} : Set (genericScheme k M)) := by
    have heq : Set.range e = {x} := Set.range_eq_singleton fun a =>
      congrArg e (Subsingleton.elim a (IsLocalRing.closedPoint (LaurentSeries k)))
    rw [← heq]
    exact e.isClosedEmbedding.isClosed_range
  letI : SmoothOfRelativeDimension 1 (genericStructure k M) :=
    generic_relative_one k h3 M hM s hs
  letI : IsIntegral (CategoryTheory.Limits.pullback M.p (genericBase k)) :=
    inferInstanceAs (IsIntegral (genericScheme k M))
  letI : IsDiscreteValuationRing (OriginStalk k M s hs.1) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      (genericStructure k M) x hx
  refine ⟨εa, κa, ⟨rfl, χ, φ, σ, Ψ, hχ, hφ, hσ, hΨ, hκ⟩, hker, ?_, ?_, ?_⟩
  · rw [hker]
    infer_instance
  · rw [hker]
    exact IsDiscreteValuationRing.not_a_field _
  · refine ⟨hκ.2.1, ?_⟩
    intro a n
    rw [hker]
    exact hκ.2.2 a n

end ArithmeticThetaConormalInitialR0162
#print axioms ArithmeticThetaConormalInitialR0162.actual_origin_augmented_taylor

