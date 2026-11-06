import SchemeSchrodingerDefinitionsR0261
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion

/-! Identity evaluation: canonical-map comparisons and local restriction providers. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeSchrodingerR0261
namespace SchemeThetaIdentityEvaluation
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259
open Scheme.Modules

lemma pullbackId_section {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) :
    ((pullbackId X).hom.app M).app ((𝟙 X) ⁻¹ᵁ U)
      (pullbackLocalSection (𝟙 X) s) = s := by
  have h := unit_conjugateEquiv (CategoryTheory.Adjunction.id (C := X.Modules))
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  have h2 := congrArg (fun f => Scheme.Modules.Hom.app f U s) h
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    pushforward_map_app, pushforwardId_inv_app_app] at h2
  exact h2.symm

lemma pullbackId_inv_section {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackId X).inv.app M).app ⊤ s =
      (pullbackLocalSection (𝟙 X) s : Γ((pullback (𝟙 X)).obj M, ⊤)) := by
  conv_lhs => rw [← pullbackId_section M ⊤ s]
  change (((pullbackId X).hom.app M) ≫ ((pullbackId X).inv.app M)).app ⊤ _ = _
  rw [(pullbackId X).hom_inv_id_app]
  rfl

lemma pullbackCongr_inv_section {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCongr h).inv.app M).app ⊤
      (pullbackLocalSection g s : Γ((pullback g).obj M, ⊤)) =
      (pullbackLocalSection f s : Γ((pullback f).obj M, ⊤)) := by
  subst g
  simp [pullbackCongr]

lemma pullbackComp_inv_section {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp f g).inv.app M).app ⊤
      (pullbackLocalSection (f ≫ g) s : Γ((pullback (f ≫ g)).obj M, ⊤)) =
      (pullbackLocalSection f (pullbackLocalSection g s) :
        Γ((pullback f).obj ((pullback g).obj M), ⊤)) := by
  rw [← pullbackComp_hom_app_pullbackLocalSection f g M ⊤ s]
  change (((pullbackComp f g).hom.app M) ≫ ((pullbackComp f g).inv.app M)).app ⊤ _ = _
  rw [(pullbackComp f g).hom_inv_id_app]
  rfl

/-- The serialized evaluation map is exactly restriction of top sections. -/
lemma evaluation_top {S : Scheme.{u}} (E : Family S) (m : ℕ)
    (s : Γ(V E m, ⊤)) :
    (evaluation E m).app ⊤ s =
      (pullbackLocalSection E.zero (s : Γ(thetaLine E m, ⊤)) :
        Γ((pullback E.zero).obj (thetaLine E m), ⊤)) := by
  change ((pullback E.zero).map ((pullbackPushforwardAdjunction E.p).counit.app
    (thetaLine E m))).app ⊤
      (((pullbackComp E.zero E.p).inv.app (V E m)).app ⊤
        (((pullbackCongr (E.law.one (𝟙 S)).property).inv.app (V E m)).app ⊤
          (((pullbackId S).inv.app (V E m)).app ⊤ s))) = _
  rw [pullbackId_inv_section, pullbackCongr_inv_section]
  erw [pullbackComp_inv_section E.zero E.p (V E m) s]
  exact (pullbackLocalSection_app E.zero
    ((pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m))
    (pullbackLocalSection E.p s)).symm.trans
      (congrArg (pullbackLocalSection E.zero) (counit_app_pullbackLocalSection E.p s))

/-- The accepted positive filtration gives every value at the identity in
all degrees at least two over a Noetherian rational framed base. -/
lemma noetherian_origin_surjective (R : Type u) [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (Q : FramedCurve R) (m : ℕ) (hm : 2 ≤ m) :
    Function.Surjective (pullbackLocalSection Q.zero
      (L := (Q.zero.ker ^ m).invModule) (U := ⊤)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact (noetherian_pole_filtration R Q n (by omega)).2

/-- A surjective map on top sections onto a trivial line is already a sheaf
split epimorphism. No affineness or surjectivity on other opens is assumed. -/
lemma epi_of_surjective_top_of_frame {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (η : N ≅ 𝟙_ X.Modules)
    (hφ : Function.Surjective (φ.app ⊤)) : Epi φ := by
  let v := η.inv.app ⊤ (unitSection ⊤)
  obtain ⟨s, hs⟩ := hφ v
  let t := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.sectionHom s
  have ht : t ≫ φ = η.inv := by
    apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.hom_eq_of_top_unit
    change φ.app ⊤ (t.app ⊤ (unitSection ⊤)) = v
    rw [ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.sectionHom_app_one]
    exact hs
  have hsplit : η.hom ≫ t ≫ φ = 𝟙 N := by rw [ht, η.hom_inv_id]
  exact ⟨fun a b hab => by
    calc
      a = (η.hom ≫ t ≫ φ) ≫ a := by rw [hsplit, Category.id_comp]
      _ = (η.hom ≫ t ≫ φ) ≫ b := by simpa only [Category.assoc] using congrArg (fun f => η.hom ≫ t ≫ f) hab
      _ = b := by rw [hsplit, Category.id_comp]⟩

/-- The exact evaluation map is epi whenever its restriction is surjective
and its identity fibre has a frame. Local frames will suffice after descent. -/
lemma evaluation_epi_of_frame {S : Scheme.{u}} (E : Family S) (m : ℕ)
    (η : (pullback E.zero).obj (thetaLine E m) ≅ 𝟙_ S.Modules)
    (h : Function.Surjective (pullbackLocalSection E.zero
      (L := thetaLine E m) (U := ⊤))) : Epi (evaluation E m) := by
  apply epi_of_surjective_top_of_frame (evaluation E m) η
  intro y
  obtain ⟨s, hs⟩ := h y
  exact ⟨s, (evaluation_top E m s).trans hs⟩

/-- Transport through an actual line isomorphism preserves identity restriction. -/
lemma restriction_surjective_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (η : M ≅ N)
    (h : Function.Surjective (pullbackLocalSection f (L := M) (U := ⊤))) :
    Function.Surjective (pullbackLocalSection f (L := N) (U := ⊤)) :=
  ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration.surjective_pullback_of_iso f η h

/-- A framed base line can be tensored into the positive pole line without
altering surjectivity. The frame is used only in this local helper. -/
lemma noetherian_twisted_origin_surjective (R : Type u) [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (Q : FramedCurve R) (m : ℕ) (hm : 2 ≤ m)
    (H : (Base R).Modules) (η : H ≅ 𝟙_ (Base R).Modules) :
    Function.Surjective (pullbackLocalSection Q.zero
      (L := tensorObj (Q.zero.ker ^ m).invModule ((pullback Q.structureMap).obj H))
      (U := ⊤)) := by
  let M := (Q.zero.ker ^ m).invModule
  let δ : tensorObj M ((pullback Q.structureMap).obj H) ≅ M :=
    (Iso.refl M ⊗ᵢ ((pullback Q.structureMap).mapIso η ≪≫ pullbackUnitIso Q.structureMap)) ≪≫ ρ_ M
  exact restriction_surjective_iso Q.zero δ.symm (noetherian_origin_surjective R Q m hm)

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames

/-- Surjective restriction to a framed identity fibre supplies an actual
section morphism whose pullback to that fibre is invertible. -/
lemma exists_section_iso_at {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (η : (pullback f).obj M ≅ 𝟙_ X.Modules)
    (h : Function.Surjective (pullbackLocalSection f (L := M) (U := ⊤))) :
    ∃ t : 𝟙_ Y.Modules ⟶ M, IsIso ((pullback f).map t) := by
  obtain ⟨s, hs⟩ := h (η.inv.app ⊤ (unitSection ⊤))
  let t := sectionHom s
  have ht : pullbackSection f t = η.inv := by
    apply hom_eq_of_top_unit
    rw [pullbackSection_app_top, sectionHom_app_one]
    exact hs
  have he : (pullback f).map t = (pullbackUnitIso f).hom ≫ η.inv := by
    rw [← ht]
    simp only [pullbackSection, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨t, ?_⟩
  rw [he]
  infer_instance

/-- A section generating at the identity remains generating after any
commuting base change, including nonflat base change. -/
lemma section_iso_at_baseChange {S T X Y : Scheme.{u}}
    (z : S ⟶ X) (z' : T ⟶ Y) (b : T ⟶ S) (f : Y ⟶ X)
    (hz : z' ≫ f = b ≫ z) {M N : X.Modules} (t : M ⟶ N)
    [IsIso ((pullback z).map t)] :
    IsIso ((pullback z').map ((pullback f).map t)) := by
  let η : pullback f ⋙ pullback z' ≅ pullback z ⋙ pullback b :=
    pullbackComp z' f ≪≫ pullbackCongr hz ≪≫ (pullbackComp b z).symm
  exact (NatIso.isIso_map_iff η t).mpr (by
    change IsIso ((pullback b).map ((pullback z).map t))
    infer_instance)

/-- A genuine pole section generating at the identity on a Noetherian framed
family; the morphism is suitable for arbitrary geometric base change. -/
lemma noetherian_origin_generator (R : Type u) [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (Q : FramedCurve R) (m : ℕ) (hm : 2 ≤ m) :
    ∃ t : 𝟙_ Q.target.Modules ⟶ (Q.zero.ker ^ m).invModule,
      IsIso ((pullback Q.zero).map t) := by
  obtain ⟨η⟩ := NoetherianPoleFiltration.origin_power_restriction_trivial R Q m (by omega)
  exact exists_section_iso_at Q.zero _ η (noetherian_origin_surjective R Q m hm)

/-- A section generating the actual identity fibre makes the serialized
counit-based evaluation an epimorphism. -/
lemma evaluation_epi_of_generator {S : Scheme.{u}} (E : Family S) (m : ℕ)
    (t : 𝟙_ E.curve.Modules ⟶ thetaLine E m)
    [IsIso ((pullback E.zero).map t)] : Epi (evaluation E m) := by
  let s : Γ(V E m, ⊤) := t.app ⊤ (unitSection ⊤)
  let a : 𝟙_ S.Modules ⟶ V E m := sectionHom s
  have h : a ≫ evaluation E m = pullbackSection E.zero t := by
    apply hom_eq_of_top_unit
    change (evaluation E m).app ⊤ (a.app ⊤ (unitSection ⊤)) = _
    rw [sectionHom_app_one, evaluation_top, pullbackSection_app_top]
  haveI : IsIso (pullbackSection E.zero t) := by
    dsimp only [pullbackSection]
    infer_instance
  haveI : Epi (a ≫ evaluation E m) := by rw [h]; infer_instance
  exact epi_of_epi a (evaluation E m)

/-- The actual origin ideal of a pointed framed curve commutes with the
specified Cartesian square. No commutativity of the group law is needed. -/
lemma framed_origin_comap {R A : Type u} [CommRing R] [CommRing A]
    (Q : FramedCurve R) (P : FramedCurve A) (b : Base A ⟶ Base R)
    (f : P.target ⟶ Q.target)
    (hc : CategoryTheory.IsPullback f P.structureMap Q.structureMap b)
    (hz : P.zero ≫ f = b ≫ Q.zero) : Q.zero.ker.comap f = P.zero.ker := by
  have houter : CategoryTheory.IsPullback (P.zero ≫ P.structureMap) b b
      (Q.zero ≫ Q.structureMap) := by
    rw [P.zero_over, Q.zero_over]
    exact CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs : CategoryTheory.IsPullback P.zero b f Q.zero :=
    houter.of_right hz hc.flip
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  letI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp Q.zero Q.structureMap
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Q.zero f]
  rw [← Scheme.Hom.ker_comp_of_isIso hs.isoPullback.hom]
  rw [CategoryTheory.IsPullback.isoPullback_hom_fst]

/-- Dual Cartier powers are transported using the same pointed square. -/
def framed_originPowerComparison {R A : Type u} [CommRing R] [CommRing A]
    (Q : FramedCurve R) (P : FramedCurve A) (b : Base A ⟶ Base R)
    (f : P.target ⟶ Q.target)
    (hc : CategoryTheory.IsPullback f P.structureMap Q.structureMap b)
    (hz : P.zero ≫ f = b ≫ Q.zero) (m : ℕ) :
    (pullback f).obj (Q.zero.ker ^ m).invModule ≅ (P.zero.ker ^ m).invModule := by
  let e := ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.idealPullbackIso
    f (Q.zero.ker ^ m) (P.zero.ker ^ m)
    (Q.zero_ideal_invertible.pow m) (P.zero_ideal_invertible.pow m)
    (by rw [ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.comap_power,
      framed_origin_comap Q P b f hc hz])
  letI := ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140.dualComparison_isIso
    f (Q.zero.ker ^ m).module (Q.zero_ideal_invertible.pow m).isInvertible_module
  exact asIso (ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140.dualComparison f _) ≪≫
    ((MonoidalClosed.internalHom (C := P.target.Modules)).mapIso e.symm.op).app
      (𝟙_ P.target.Modules)

/-- Finite-type descent and the pointed Cartier comparison extend the actual
identity-generating pole section to arbitrary rational framed bases. -/
lemma arbitrary_origin_generator (R : Type u) [CommRing R] [Algebra ℚ R]
    (Q : FramedCurve R) (m : ℕ) (hm : 2 ≤ m) :
    ∃ t : 𝟙_ Q.target.Modules ⟶ (Q.zero.ker ^ m).invModule,
      IsIso ((pullback Q.zero).map t) := by
  obtain ⟨D⟩ := framed_finite_type_approximation R Q
  letI := D.commRing
  letI := D.rational
  letI := D.finiteType
  letI : IsNoetherianRing D.ring := Algebra.FiniteType.isNoetherianRing ℚ D.ring
  obtain ⟨t, ht⟩ := noetherian_origin_generator D.ring D.model m hm
  letI := ht
  let b := Spec.map (CommRingCat.ofHom D.scalar.toRingHom)
  let e := framed_originPowerComparison D.model Q b D.comparison D.cartesian D.zero_eq m
  let t' : 𝟙_ Q.target.Modules ⟶ (Q.zero.ker ^ m).invModule :=
    (pullbackUnitIso D.comparison).inv ≫ (pullback D.comparison).map t ≫ e.hom
  haveI : IsIso ((pullback Q.zero).map ((pullback D.comparison).map t)) :=
    section_iso_at_baseChange D.model.zero Q.zero b D.comparison D.zero_eq t
  refine ⟨t', ?_⟩
  dsimp only [t']
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Tensoring by a locally framed base line preserves the actual generating
section; this helper applies to arbitrary rational rings. -/
lemma arbitrary_twisted_origin_generator (R : Type u) [CommRing R] [Algebra ℚ R]
    (Q : FramedCurve R) (m : ℕ) (hm : 2 ≤ m)
    (H : (Base R).Modules) (η : H ≅ 𝟙_ (Base R).Modules) :
    ∃ t : 𝟙_ Q.target.Modules ⟶
      tensorObj (Q.zero.ker ^ m).invModule ((pullback Q.structureMap).obj H),
      IsIso ((pullback Q.zero).map t) := by
  obtain ⟨t, ht⟩ := arbitrary_origin_generator R Q m hm
  letI := ht
  let M := (Q.zero.ker ^ m).invModule
  let δ : tensorObj M ((pullback Q.structureMap).obj H) ≅ M :=
    (Iso.refl M ⊗ᵢ ((pullback Q.structureMap).mapIso η ≪≫ pullbackUnitIso Q.structureMap)) ≪≫ ρ_ M
  refine ⟨t ≫ δ.inv, ?_⟩
  rw [Functor.map_comp]
  infer_instance

/-- The actual conormal of a framed smooth curve is trivial over any ring. -/
lemma framed_conormal_trivial {R : Type u} [CommRing R] (Q : FramedCurve R) :
    Nonempty ((pullback Q.zero).obj Q.zero.ker.module ≅ 𝟙_ (Base R).Modules) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one
  letI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  letI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp Q.zero Q.structureMap
  have hΩ : IsInvertible Q.structureMap.kaehler :=
    (isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (Q.structureMap.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  letI := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.section_conormal_isIso
    Q.structureMap Q.zero Q.zero_over Q.zero_ideal_invertible hΩ
  obtain ⟨η⟩ := Q.hodge_trivial
  exact ⟨asIso (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap
    Q.structureMap Q.zero) ≪≫ η.symm⟩

attribute [local instance] SchemeLocal.FramedChart.commRing

/-- The family on a framed chart retains its given geometric maps and law. -/
def chartFamily {S : Scheme.{u}} (E : Family S) (C : SchemeLocal.FramedChart E) :
    Family (Base C.ring) where
  curve := C.Q.target
  p := C.Q.structureMap
  law := {
    mul := C.Q.law.mul
    one := C.Q.law.one
    inv := C.Q.law.inv
    mul_assoc := C.Q.law.mul_assoc
    one_mul := C.Q.law.one_mul
    mul_one := C.Q.law.mul_one
    inv_mul_cancel := C.Q.law.inv_mul_cancel
    mul_comm := C.comm
    mul_natural := C.Q.law.mul_natural }
  proper := C.Q.geometry.proper
  dimension := C.Q.smooth_dimension_one
  connected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) C.cartesian E.connected

private def unitPowerIso (X : Scheme.{u}) : (m : ℕ) → (𝟙_ X.Modules).tensorPow m ≅ 𝟙_ X.Modules
  | 0 => Iso.refl _
  | m + 1 => ((unitPowerIso X m) ⊗ᵢ Iso.refl _) ≪≫ ρ_ _

/-- A frame is chosen only on the actual framed chart's conormal Hodge line. -/
def chartHodgePowerFrame {S : Scheme.{u}} (E : Family S)
    (C : SchemeLocal.FramedChart E) (m : ℕ) :
    (ArithmeticThetaSchemeHodgeR0205.Cotangent (chartFamily E C)).tensorPow m ≅
      𝟙_ (Base C.ring).Modules :=
  tensorPowMapIso (framed_conormal_trivial C.Q).some m ≪≫ unitPowerIso _ m

/-- The actual theta line admits an identity-generating section on every
rational framed chart. The chart comparison retains the conormal Hodge factor. -/
lemma chart_theta_generator {S : Scheme.{u}} (E : Family S)
    (C : SchemeLocal.FramedChart E) [Algebra ℚ C.ring] (m : ℕ) (hm : 2 ≤ m) :
    ∃ t : 𝟙_ C.Q.target.Modules ⟶ (pullback C.comparison).obj (thetaLine E m),
      IsIso ((pullback C.Q.zero).map t) := by
  obtain ⟨t, ht⟩ := arbitrary_twisted_origin_generator C.ring C.Q m hm
    ((ArithmeticThetaSchemeHodgeR0205.Cotangent (chartFamily E C)).tensorPow m)
    (chartHodgePowerFrame E C m)
  letI := ht
  let η := SchemeThetaSectionCohomology.thetaComparison E (chartFamily E C)
    C.base C.comparison C.cartesian C.zero_eq m
  refine ⟨t ≫ η.inv, ?_⟩
  rw [Functor.map_comp]
  infer_instance

/-- A section generating along a map makes the pulled-back counit epi. -/
lemma epi_counit_at_generator {S T X : Scheme.{u}} (p : X ⟶ S) (z : T ⟶ X)
    (L : X.Modules) (t : 𝟙_ X.Modules ⟶ L) [IsIso ((pullback z).map t)] :
    Epi ((pullback z).map ((pullbackPushforwardAdjunction p).counit.app L)) := by
  let a := (pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ t)
  have ha : (pullback p).map a ≫ (pullbackPushforwardAdjunction p).counit.app L =
      (pullbackUnitIso p).hom ≫ t := by
    exact ((pullbackPushforwardAdjunction p).homEquiv_counit (g := a)).symm.trans
      (((pullbackPushforwardAdjunction p).homEquiv _ _).symm_apply_apply _)
  haveI : Epi ((pullback z).map ((pullback p).map a) ≫
      (pullback z).map ((pullbackPushforwardAdjunction p).counit.app L)) := by
    rw [← Functor.map_comp, ha, Functor.map_comp]
    infer_instance
  exact epi_of_epi ((pullback z).map ((pullback p).map a)) _

lemma epi_map_of_natIso {X Y : Scheme.{u}} {F G : X.Modules ⥤ Y.Modules}
    (e : F ≅ G) {M N : X.Modules} (f : M ⟶ N) [Epi (F.map f)] : Epi (G.map f) := by
  haveI : Epi (e.hom.app M ≫ G.map f) := by
    rw [← e.hom.naturality]
    infer_instance
  exact epi_of_epi (e.hom.app M) (G.map f)

/-- The generic open base-change counit equation transports an actual local
generator to epimorphy of the original counit pulled back to the chart. -/
lemma epi_counit_at_open_chart {S T X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ T) (b : T ⟶ S) [IsOpenImmersion b]
    (f : Y ⟶ X) (hc : IsPullback f q p b)
    (z : S ⟶ X) (z' : T ⟶ Y) (hz : z' ≫ f = b ≫ z)
    (L : X.Modules) (t : 𝟙_ Y.Modules ⟶ (pullback f).obj L)
    [IsIso ((pullback z').map t)] :
    Epi ((pullback b).map ((pullback z).map
      ((pullbackPushforwardAdjunction p).counit.app L))) := by
  let ε := (pullbackPushforwardAdjunction p).counit.app L
  let B := baseChangeHom hc.w L
  letI : IsIso B := isIso_baseChangeHom_of_isOpenImmersion hc L
  letI : Epi ((pullback z').map
      ((pullbackPushforwardAdjunction q).counit.app ((pullback f).obj L))) :=
    epi_counit_at_generator q z' _ t
  have h := baseChangeHom_counit hc.w L
  haveI : Epi ((pullback z').map ((pullbackTwoSquare hc.w).natTrans.app ((pushforward p).obj L)) ≫
      (pullback z').map ((pullback f).map ε)) := by
    rw [← Functor.map_comp]
    change Epi ((pullback z').map
      ((pullbackTwoSquare hc.w).natTrans.app ((pushforward p).obj L) ≫
        (pullback f).map ((pullbackPushforwardAdjunction p).counit.app L)))
    rw [← h, Functor.map_comp]
    infer_instance
  letI : Epi ((pullback z').map ((pullback f).map ε)) :=
    epi_of_epi ((pullback z').map ((pullbackTwoSquare hc.w).natTrans.app ((pushforward p).obj L))) _
  let η : pullback f ⋙ pullback z' ≅ pullback z ⋙ pullback b :=
    pullbackComp z' f ≪≫ pullbackCongr hz ≪≫ (pullbackComp b z).symm
  letI : Epi ((pullback f ⋙ pullback z').map ε) := by
    change Epi ((pullback z').map ((pullback f).map ε))
    infer_instance
  exact epi_map_of_natIso η ε

/-- Epimorphy is detected on the actual framed open charts. -/
lemma identity_counit_epi (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 2 ≤ m) :
    Epi ((pullback E.zero).map ((pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m))) := by
  let ε := (pullback E.zero).map ((pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m))
  have hlocal (C : SchemeLocal.FramedChart E) : Epi ((pullback C.base).map ε) := by
    letI : IsOpenImmersion C.base := C.openImmersion
    let scalar : k →+* C.ring := (Spec.preimage (C.base ≫ σ)).hom
    letI : Algebra k C.ring := scalar.toAlgebra
    letI : Algebra ℚ C.ring := Algebra.compHom C.ring (algebraMap ℚ k)
    obtain ⟨t, ht⟩ := chart_theta_generator E C m hm
    letI := ht
    exact epi_counit_at_open_chart E.p C.Q.structureMap C.base C.comparison
      C.cartesian E.zero C.Q.zero C.zero_eq (thetaLine E m) t
  refine ⟨fun g h heq => ?_⟩
  apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.hom_ext_pullback_cover
    (fun C : SchemeLocal.FramedChart E => Base C.ring) (fun C => C.base)
    (fun C => C.openImmersion)
  · intro s
    obtain ⟨C, x, hx⟩ := SchemeLocal.exists_framedChart E s
    exact ⟨C, x, hx⟩
  · intro C
    letI := hlocal C
    apply (cancel_epi ((pullback C.base).map ε)).mp
    simpa only [Functor.map_comp] using congrArg ((pullback C.base).map) heq

end SchemeThetaIdentityEvaluation

/-- Identity evaluation of the actual theta sheaf is locally surjective for
every degree at least two over every characteristic-zero scheme base. -/
theorem scheme_theta_identity_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ∀ E : ArithmeticThetaLocalWeierstrassR0203.Family S, ∀ (m : ℕ), 2 ≤ m →
        CategoryTheory.Epi (ArithmeticThetaSchemeSchrodingerR0261.evaluation E m) := by
  intro k _ _ S σ E m hm
  letI := SchemeThetaIdentityEvaluation.identity_counit_epi k S σ E m hm
  dsimp only [evaluation]
  infer_instance

end ArithmeticThetaSchemeSchrodingerR0261
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.evaluation_top
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.noetherian_origin_surjective

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.evaluation_epi_of_frame
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.noetherian_twisted_origin_surjective

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.noetherian_origin_generator
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.section_iso_at_baseChange
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.evaluation_epi_of_generator

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.arbitrary_origin_generator

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.arbitrary_twisted_origin_generator

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaIdentityEvaluation.chart_theta_generator

#print axioms ArithmeticThetaSchemeSchrodingerR0261.scheme_theta_identity_evaluation
