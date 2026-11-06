module

public import RelativeKatoDefinitionsR0169
public import Theorems.Thm_AlgebraicGeometry_Etale_of_forall_pullback_snd_localization_atPrime
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
public import ActualMultiplicationFieldNormR0150

@[expose] public section

-- Keep the original elaborated instance paths after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm

namespace RelativeMultiplicationDegree

/-- Local target tests for multiplication are pullbacks of multiplication on
 the group after base change to that local ring. -/
lemma etale_local_test {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)}
    (G : GoodReductionJacobian.RelativeGroupLaw R f)
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    [SmoothOfRelativeDimension 1 f] (n : ℕ) (hn : IsUnit (n : R))
    {S : Type u} [CommRing S] [IsLocalRing S] {Z : Scheme.{u}}
    (t : Spec (CommRingCat.of S) ⟶ A) (l : Z ⟶ A)
    (h : Z ⟶ Spec (CommRingCat.of S)) (hp : IsPullback l h (G.schemeNsmul n) t) :
    Etale h := by
  let ι := t ≫ f
  let H := G.baseChange ι
  have hcH : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S))
      (x y : SchemeHomOver s (pullback.snd f ι)), H.mul s x y = H.mul s y x := by
    intro T s x y
    simp only [H, GoodReductionJacobian.RelativeGroupLaw.baseChange_mul, hc]
  have hu : IsUnit (n : S) := by
    simpa only [map_natCast] using hn.map (Spec.preimage ι).hom
  letI : Etale (H.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
      H hcH 1 n hu
  have hb := (G.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι n).1
  let s : Spec (CommRingCat.of S) ⟶ pullback f ι :=
    pullback.lift t (𝟙 _) (by simp [ι])
  have hp' : IsPullback l h (G.schemeNsmul n) (s ≫ pullback.fst f ι) := by
    simpa only [s, pullback.lift_fst] using hp
  exact MorphismProperty.of_isPullback (P := @Etale) (hp'.of_right' hb) inferInstance

/-- Étaleness of multiplication is checked on affine target charts and their
localizations; the relative base itself need not be local. -/
lemma etale_nsmul_relative {R : Type u} [CommRing R] {A : Scheme.{u}}
    [IsLocallyNoetherian A]
    {f : A ⟶ Spec (CommRingCat.of R)}
    (G : GoodReductionJacobian.RelativeGroupLaw R f)
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    [SmoothOfRelativeDimension 1 f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) := by
  let m := G.schemeNsmul n
  letI : LocallyOfFiniteType (m ≫ f) := by
    dsimp [m]; rw [G.schemeNsmul_over]; infer_instance
  letI : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m f
  apply IsZariskiLocalAtTarget.of_openCover (P := @Etale) A.affineCover
  intro i
  let U := A.affineCover.X i
  let g := A.affineCover.pullbackHom m i
  let e := U.isoSpec
  letI : LocallyOfFinitePresentation g :=
    MorphismProperty.pullback_snd _ _ (inferInstance : LocallyOfFinitePresentation m)
  have he : Etale (g ≫ e.hom) := by
    apply Etale.of_forall_pullback_snd_localization_atPrime (R := Γ(U, ⊤))
    intro p hp
    let j := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (Localization.AtPrime p)))
    have hb : IsPullback (𝟙 _) (g ≫ e.hom) g e.inv :=
      IsPullback.of_horiz_isIso ⟨by simp [e]⟩
    have hs := (IsPullback.of_hasPullback (g ≫ e.hom) j).paste_horiz hb
    have ht := hs.paste_horiz (IsPullback.of_hasPullback m (A.affineCover.f i))
    exact etale_local_test G hc n hn _ _ _ ht
  letI := he
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) g e.hom inferInstance he

lemma kernel_rank_at (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (n : ℕ) (hn : 0 < n)
    [IsFinite (G.schemeNsmul n)] [Etale (G.schemeNsmul n)] :
    (G.schemeKerStr n).finrank
      (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure (FractionRing R)) ))
        (IsLocalRing.closedPoint (AlgebraicClosure (FractionRing R)))) = n^2 := by
  classical
  have ho : (G.one (𝟙 _)).val = (kwZeroSect R W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G ho
  let K := AlgebraicClosure (FractionRing R)
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  letI : CharZero K := Algebra.charZero_of_charZero (FractionRing R) K
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  have heone : ev K (G.one t) = 0 := by
    have H := hev.1 K (G.one t) (G.one t)
    change ev K (G.mul t (G.one t) (G.one t)) = _ at H
    rw [G.one_mul] at H
    exact (add_left_cancel (a := ev K (G.one t)) ((add_zero _).trans H)).symm
  have hens (P : SchemeHomOver t (structureMap R W)) (m : ℕ) :
      ev K (G.nsmul t m P) = m • ev K P := by
    induction m with
    | zero => simpa only [G.nsmul_zero, zero_smul] using heone
    | succ m ih =>
      rw [G.nsmul_succ]
      have H := hev.1 K (G.nsmul t m P) P
      change ev K (G.mul t (G.nsmul t m P) P) =
        ev K (G.nsmul t m P) + ev K P at H
      rw [H, ih, succ_nsmul]
  let e : SchemeHomOver t (G.schemeKerStr n) ≃
      Submodule.torsionBy ℤ (W.toProjective.baseChange K).toAffine.Point (n : ℤ) :=
    (kernelPointsEquiv G t n).trans (Equiv.subtypeEquiv (ev K) (by
      intro z
      rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
      constructor
      · intro hz
        exact (hens z n).symm.trans ((congrArg (fun P => ev K P) hz).trans heone)
      · intro hz
        apply (ev K).injective
        exact (hens z n).trans (hz.trans heone.symm)))
  apply (finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    (G.schemeKerStr n) K (algebraMap R K)).trans
  exact (Nat.card_congr e).trans
    (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num))


end RelativeMultiplicationDegree

/-- Positive multiplication on the entire relative curve, with its actual field action. -/
theorem relative_multiplication_degree :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G), ∀ (n : ℕ), 0 < n → AlgebraicGeometry.IsFinite (G.schemeNsmul n) ∧ AlgebraicGeometry.Etale (G.schemeNsmul n) ∧ AlgebraicGeometry.Surjective (G.schemeNsmul n) ∧ (∀ x, (G.schemeNsmul n).finrank x = n^2) ∧ ∃ φ : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField →+* (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField, ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul n) φ ∧ ArithmeticThetaGeneralEllipticKatoR0168.HasFieldDegree φ (n^2) := by
  intro R _ _ _ _ _ W _ _ _ G hG n hn
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hnunit : IsUnit (n : R) := by
    have hq : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    simpa only [map_natCast] using hq.map (algebraMap ℚ R)
  letI : Etale (G.schemeNsmul n) := by
    rw [← toGRJ_schemeNsmul]
    exact RelativeMultiplicationDegree.etale_nsmul_relative (toGRJ G) hG.2 n hnunit
  letI : IsProper (G.schemeNsmul n) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (G.schemeNsmul n) (structureMap R W) inferInstance
      (by rw [G.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (G.schemeNsmul n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  letI : IsFinite (G.schemeNsmul n) := .of_isProper_of_locallyQuasiFinite _
  have hrank : ∀ x, (G.schemeNsmul n).finrank x = n^2 := by
    let K := AlgebraicClosure (FractionRing R)
    let z : Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K)) (IsLocalRing.closedPoint K)
    intro x
    calc
      (G.schemeNsmul n).finrank x =
          (G.schemeNsmul n).finrank ((G.one (𝟙 _)).val z) :=
        (G.schemeNsmul n).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
      _ = (G.schemeKerStr n).finrank z := (Scheme.Hom.finrank_pullback_snd _ _ z).symm
      _ = n^2 := RelativeMultiplicationDegree.kernel_rank_at R W G hG n hn
  letI : Surjective (G.schemeNsmul n) :=
    (G.schemeNsmul n).one_le_finrank_iff_surjective.mp (by
      intro x
      rw [hrank x]
      exact Nat.one_le_pow 2 n hn)
  obtain ⟨φ, hφ⟩ := exists_fieldMap (G.schemeNsmul n)
  obtain ⟨hfin, hdeg, _⟩ := finite_etale_local_norm _ _ (G.schemeNsmul n) φ hφ
  have hd : fieldDegree φ = n^2 :=
    (hdeg (genericPoint (Curve R W))).symm.trans (hrank _)
  exact ⟨inferInstance, inferInstance, inferInstance, hrank, φ, hφ, hfin, hd⟩

#print axioms relative_multiplication_degree
end ArithmeticThetaRelativeKatoR0169
