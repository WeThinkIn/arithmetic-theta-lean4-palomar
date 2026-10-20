module

public import SchemeFourCoverR0216
public import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
public import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
public import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 200000

@[expose] public section


/-! Geometry of the actual four-marking cover over arbitrary scheme bases. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216.SchemeFourCoverGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175.Representability
open ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175

lemma etale_nsmul_relative {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)}
    (G : GoodReductionJacobian.RelativeGroupLaw R f)
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    [SmoothOfRelativeDimension 1 f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) := by
  let m := G.schemeNsmul n
  letI : LocallyOfFinitePresentation (m ≫ f) := by
    dsimp [m]; rw [G.schemeNsmul_over]; infer_instance
  letI : LocallyOfFinitePresentation m :=
    locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType (g := f) inferInstance inferInstance
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
    exact ArithmeticThetaRelativeKatoR0169.RelativeMultiplicationDegree.etale_local_test G hc n hn _ _ _ ht
  letI := he
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) g e.hom inferInstance he


namespace UniversalEvaluation
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

abbrev Coeff : Type u := MvPolynomial (Fin 5) (ULift.{u} ℤ)
def universal : WeierstrassCurve Coeff.{u} := ⟨X 0, X 1, X 2, X 3, X 4⟩
lemma discriminant_ne : universal.{u}.Δ ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ULift.{u} ℤ)) h
  norm_num [universal, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    Matrix.cons_val_succ, Matrix.cons_val_zero] at hh
  all_goals
    have hz : (64 : ℤ) = 0 := congrArg ULift.down hh
    norm_num at hz
abbrev Ring : Type u := Localization.Away universal.{u}.Δ
instance : IsDomain Coeff.{u} := by
  letI : IsDomain (ULift.{u} ℤ) := MulEquiv.isDomain ℤ ULift.ringEquiv.toMulEquiv
  exact inferInstanceAs (IsDomain (MvPolynomial (Fin 5) (ULift.{u} ℤ)))
instance : IsDomain Ring.{u} :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors discriminant_ne)
instance : IsNoetherianRing Coeff.{u} := by
  letI : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 5) (ULift.{u} ℤ)))
instance : IsNoetherianRing Ring.{u} :=
  IsLocalization.isNoetherianRing (Submonoid.powers universal.{u}.Δ) Ring.{u}
    (inferInstance : IsNoetherianRing Coeff.{u})
abbrev equation : WeierstrassCurve Ring.{u} := universal.{u}.map (algebraMap Coeff.{u} Ring.{u})
instance : equation.{u}.IsElliptic := ⟨by
  rw [WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit universal.{u}.Δ⟩

lemma classify {A : Type u} [CommRing A] (V : WeierstrassCurve A) [V.IsElliptic] :
    ∃ c : Ring.{u} →+* A, equation.{u}.map c = V := by
  let f : Coeff.{u} →+* A := MvPolynomial.eval₂Hom
    ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) ![V.a₁, V.a₂, V.a₃, V.a₄, V.a₆]
  have hf : universal.{u}.map f = V := by ext <;> simp [universal, f, WeierstrassCurve.map]
  have hu : IsUnit (f universal.{u}.Δ) := by
    rw [← WeierstrassCurve.map_Δ, hf]
    exact WeierstrassCurve.isUnit_Δ V
  refine ⟨IsLocalization.Away.lift universal.{u}.Δ hu, ?_⟩
  rw [equation, WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hf]

lemma exists_evaluation {A : Type u} [CommRing A] (V : WeierstrassCurve A) [V.IsElliptic] :
    ∃ (G : RelativeGroupLaw A (projModelStrCR V.toProjective))
      (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra A F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap A F)))
          (projModelStrCR V.toProjective) ≃ (V.toProjective.baseChange F).toAffine.Point),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A)),
        (G.one t).val = t ≫ (kwZeroSect A V).val) ∧ IsPointsEval V.toProjective G ev := by
  obtain ⟨G, _, hG⟩ :=
    exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
      equation.{u}.toProjective (projModel_pullback_iso_baseChange equation.{u}.toProjective)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists
      equation.{u} G (by simpa using hG (𝟙 _))
  obtain ⟨c, hc⟩ := classify V
  obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom equation.{u}.toProjective c
  have hP := isPullback_projMap_of_isCoefficientHom equation.{u}.toProjective c φ hφ hcoef
  obtain ⟨G', hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback c
    (projModelStrCR equation.{u}.toProjective) (projModelStrCR (equation.{u}.toProjective.map c))
    (Proj.map φ hφ) hP G
  have ho' := fun {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A)) =>
    one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback equation.{u}.toProjective c φ hφ hcoef
      hP G G' (fun t => hG t) (fun t => ho t) t
  obtain ⟨ev', hev'⟩ := exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
    equation.{u}.toProjective c φ hφ hcoef hP G G' (fun t x y => hm t x y) ev hev
  cases hc
  exact ⟨G', ev', fun t => ho' t, hev'⟩
end UniversalEvaluation

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
  (hG : IsOriginLaw R W G) (L : ℕ)

include hG in
lemma multiplication_finite_etale (hL : 0 < L) :
    IsFinite (G.schemeNsmul L) ∧ Etale (G.schemeNsmul L) := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hunit : IsUnit (L : R) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)) : IsUnit (L : ℚ)).map
        (algebraMap ℚ R)
  letI : Etale (G.schemeNsmul L) := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ_schemeNsmul]
    exact etale_nsmul_relative
      (ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G) hG.2 L hunit
  letI : IsProper (G.schemeNsmul L) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (G.schemeNsmul L) (structureMap R W) inferInstance
      (by rw [G.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (G.schemeNsmul L) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, inferInstance⟩

include hG in
lemma kernel_finite_etale (hL : 0 < L) : IsFinite (kp R W G L) ∧ Etale (kp R W G L) := by
  obtain ⟨hf, he⟩ := multiplication_finite_etale R W G hG L hL
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (kernel_cartesian R W G L) hf,
    MorphismProperty.of_isPullback (P := @Etale) (kernel_cartesian R W G L) he⟩

include hG in
/-- Every linear combination of the universal torsion pair remains killed. -/
lemma combination_killed (i j : ℕ) : G.nsmul (pp R W G L) L
    (G.mul _ (G.nsmul _ i (px R W G L)) (G.nsmul _ j (py R W G L))) = G.one _ := by
  let t := pp R W G L
  letI : CommGroup (SchemeHomOver t (structureMap R W)) :=
    { G.pointGroup t with mul_comm := hG.2 t }
  have hn (n : ℕ) (x : SchemeHomOver t (structureMap R W)) : G.nsmul t n x = x ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih]; rfl
  have hx : (px R W G L) ^ L = 1 := (hn L _).symm.trans (px_killed R W G hG L)
  have hy : (py R W G L) ^ L = 1 := (hn L _).symm.trans (py_killed R W G hG L)
  change G.nsmul t L (G.mul t (G.nsmul t i _) (G.nsmul t j _)) = G.one t
  rw [hn, hn, hn]
  change ((px R W G L) ^ i * (py R W G L) ^ j) ^ L = 1
  rw [mul_pow, ← pow_mul, Nat.mul_comm i L, pow_mul, hx,
    ← pow_mul, Nat.mul_comm j L, pow_mul, hy, one_pow, one_pow, one_mul]

/-- The zero section inside the finite étale torsion scheme. -/
def zeroInKernel : Base R ⟶ kernel R W G L :=
  klift R W G hG L (𝟙 _) (G.one _) (G.nsmul_unit _ L)

@[simp] lemma zeroInKernel_ki : zeroInKernel R W G hG L ≫ ki R W G L = origin R W := by
  rw [zeroInKernel, klift_ki, hG.1, Category.id_comp]
@[simp] lemma zeroInKernel_kp : zeroInKernel R W G hG L ≫ kp R W G L = 𝟙 _ :=
  klift_kp R W G hG L _ _ _

include hG in
lemma zeroInKernel_open (hL : 0 < L) : IsOpenImmersion (zeroInKernel R W G hG L) := by
  letI : Etale (kp R W G L) := (kernel_finite_etale R W G hG L hL).2
  exact section_open (kp R W G L) (zeroInKernel R W G hG L) (zeroInKernel_kp R W G hG L)

include hG in
lemma independent_clopen (hL : 0 < L) : IsClopen (independentOpen R W G L : Set (pairs R W G L)) := by
  refine ⟨?_, (independentOpen R W G L).isOpen⟩
  have hh (i j : ℕ) : IsClosed {z : pairs R W G L |
      combination R W G L i j z ∉ Set.range (origin R W)} := by
    let a := G.mul (pp R W G L) (G.nsmul _ i (px R W G L)) (G.nsmul _ j (py R W G L))
    let c := klift R W G hG L (pp R W G L) a (combination_killed R W G hG L i j)
    let e := zeroInKernel R W G hG L
    letI : IsOpenImmersion e := zeroInKernel_open R W G hG L hL
    have hi : IsClosedImmersion (ki R W G L) := by
      letI : IsProper (structureMap R W) :=
        WeierstrassProjModel.projModelStrCR_isProper W.toProjective
      have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect R W).property
      letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
      letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
      exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (kernel_cartesian R W G L).flip inferInstance
    letI := hi
    have heq : {z : pairs R W G L | combination R W G L i j z ∉ Set.range (origin R W)} =
        c ⁻¹' (Set.range e)ᶜ := by
      ext z
      apply not_congr
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, (ki R W G L).isClosedEmbedding.injective ?_⟩
        change (e ≫ ki R W G L) b = (c ≫ ki R W G L) z
        rw [show e ≫ ki R W G L = origin R W from zeroInKernel_ki R W G hG L,
          show c ≫ ki R W G L = a.val from klift_ki R W G hG L _ _ _]
        exact hb
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        have H := congrArg (ki R W G L) hb
        change (e ≫ ki R W G L) b = (c ≫ ki R W G L) z at H
        rw [show e ≫ ki R W G L = origin R W from zeroInKernel_ki R W G hG L,
          show c ≫ ki R W G L = a.val from klift_ki R W G hG L _ _ _] at H
        exact H
    rw [heq]
    exact (IsOpenImmersion.isOpen_range e).isClosed_compl.preimage c.continuous
  have H := isClosed_iInter fun ij : indices L => hh ij.val.1.val ij.val.2.val
  change IsClosed {z | ∀ ij : indices L, combination R W G L ij.val.1.val ij.val.2.val z ∉ Set.range (origin R W)}
  simpa only [Set.iInter_ofPred] using H

variable (hL : 0 < L)

include hL in
lemma constructed_finite_etale :
    IsFinite (Representability.level R W G hG L).projection ∧
    Etale (Representability.level R W G hG L).projection := by
  obtain ⟨hf,he⟩ := kernel_finite_etale R W G hG L hL
  letI := hf
  letI := he
  let U := Representability.independentOpen R W G L
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact (independent_clopen R W G hG L hL).1)
  change IsFinite (U.ι ≫ Representability.pp R W G L) ∧
    Etale (U.ι ≫ Representability.pp R W G L)
  have hf' : IsFinite (Representability.pp R W G L) := by
    dsimp [Representability.pp]; infer_instance
  have he' : Etale (Representability.pp R W G L) := by
    dsimp [Representability.pp]; infer_instance
  letI := hf'
  letI := he'
  exact ⟨inferInstance, inferInstance⟩

include hG hL in
lemma representing_finite_etale (Z : LevelScheme R W G L) (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) :
    IsFinite Z.projection ∧ Etale Z.projection := by
  obtain ⟨e,hp,_,_⟩ := representing_iso Z (Representability.level R W G hG L)
    hZ (Representability.represents R W G hG L)
  obtain ⟨hf,he⟩ := constructed_finite_etale R W G hG L hL
  letI := hf
  letI := he
  rw [← hp]
  exact ⟨inferInstance, inferInstance⟩

include hG hL in
lemma marking_card_geometric (K : Type u) [Field K] [IsAlgClosed K]
    [Algebra R K] [CharZero K] :
    Nat.card (FullLevel R W G L
      (Spec.map (CommRingCat.ofHom (algebraMap R (K))))) =
      levelDegree L := by
  classical
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  obtain ⟨G₀, ev, hzero, hev⟩ := UniversalEvaluation.exists_evaluation W
  have heq := WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
    W.toProjective (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
    G₀ G (fun t => hzero t) (fun t => hG.1 t)
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let E := (W.toProjective.baseChange K).toAffine.Point
  have hm (x y : SchemeHomOver t (structureMap R W)) :
      ev K (G.mul t x y) = ev K x + ev K y := by
    rw [← heq K x y]
    exact hev.1 K x y
  have hz : ev K (G.one t) = 0 := by
    have hh := hm (G.one t) (G.one t)
    rw [G.one_mul] at hh
    exact (add_left_cancel (a := ev K (G.one t)) ((add_zero _).trans hh)).symm
  have hd (d : ℕ) (hdiv : d ∣ L) :
      Nat.card (Submodule.torsionBy ℤ E (d : ℤ)) = d ^ 2 := by
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.ne_of_gt hL) hdiv
    exact WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine (Nat.cast_ne_zero.mpr hd0) (by norm_num)
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (Nat.ne_of_gt hL) hd
  have hc := hd L dvd_rfl
  let H := Submodule.torsionBy ℤ E (L : ℤ)
  letI : Finite H := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 (Nat.ne_of_gt hL))
  have hk (x : H) : L • x = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (L : ℤ) x
  exact (Nat.card_congr (fieldMarkEquiv (L := L) (hG := hG) (t := t)
    (ev := ev K) (hm := hm) (hz := hz))).trans (card_basisPair L hk hc e)


include hG hL in
lemma representing_rank (Z : LevelScheme R W G L)
    (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) :
    ∀ z, Z.projection.finrank z = levelDegree L := by
  obtain ⟨hf, he⟩ := representing_finite_etale R W G hG L hL Z hZ
  letI := hf
  letI := he
  intro z
  let K := AlgebraicClosure z.asIdeal.ResidueField
  letI : Algebra ℚ z.asIdeal.ResidueField := (algebraMap R z.asIdeal.ResidueField).comp
    (algebraMap ℚ R) |>.toAlgebra
  letI : CharZero z.asIdeal.ResidueField := Algebra.charZero_of_charZero ℚ _
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap z.asIdeal.ResidueField K).injective
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hz : t (IsLocalRing.closedPoint K) = z := by
    change PrimeSpectrum.comap (algebraMap R K) _ = z
    rw [IsScalarTower.algebraMap_eq R z.asIdeal.ResidueField K, PrimeSpectrum.comap_comp]
    exact Set.mem_singleton_iff.mp (PrimeSpectrum.residueField_comap z ▸
      Set.mem_range_self _)
  rw [← hz]
  exact (finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    Z.projection K (algebraMap R K)).trans
      ((Nat.card_congr (sectionsEquiv Z hZ t)).trans
        (marking_card_geometric R W G hG L hL K))


lemma levelDegree_four : levelDegree 4 = 96 := by
  have hk : ∀ x : ZMod 4 × ZMod 4, 4 • x = 0 := by decide
  have hc : Nat.card (ZMod 4 × ZMod 4) = 4 ^ 2 := by simp
  rw [← card_basisPair 4 hk hc (AddEquiv.refl (ZMod 4 × ZMod 4))]
  unfold BasisPair
  rw [Nat.card_eq_fintype_card]
  decide


include hG in
lemma affine_geometry (Z : LevelScheme R W G 4)
    (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) :
    IsFinite Z.projection ∧ Etale Z.projection ∧ Surjective Z.projection ∧
      ∀ z, Z.projection.finrank z = 96 := by
  obtain ⟨hf, he⟩ := representing_finite_etale R W G hG 4 (by omega) Z hZ
  letI := hf
  letI := he
  have hr : ∀ z, Z.projection.finrank z = 96 := by
    intro z
    rw [representing_rank R W G hG 4 (by omega) Z hZ, levelDegree_four]
  exact ⟨hf, he, Z.projection.one_le_finrank_iff_surjective.mp (by
    intro z; change 1 ≤ Z.projection.finrank z; rw [hr]; decide), hr⟩

section SchemeGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open SchemeFourCover
variable {S : Scheme.{u}} (E : Family S)

/-- Express the same universal marking by its maps into the original family. -/
def asLocal (D : Cover E) : LocalPointCover E (𝟙 S) where
  space := D.space
  projection := D.projection
  marking := (pushMarking E D.family D.projection D.comparison D.cartesian D.marking).cast E
    (Category.comp_id D.projection).symm

@[simp] lemma asLocal_x (D : Cover E) :
    (asLocal E D).marking.x.val = D.marking.x.val ≫ D.comparison := by
  simp only [asLocal, Marking.cast_x]; rfl
@[simp] lemma asLocal_y (D : Cover E) :
    (asLocal E D).marking.y.val = D.marking.y.val ≫ D.comparison := by
  simp only [asLocal, Marking.cast_y]; rfl

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)

include k σ in
lemma asLocal_represents (D : Cover E) (hD : Represents E D) :
    LocalPointRepresents E (asLocal E D) := by
  intro T t M
  let A := M.cast E (Category.comp_id t)
  let F := SchemeFamilyBaseChange.baseChangeFamily E t
  let f := pullback.fst E.p t
  have hc : Cartesian E F t f :=
    ⟨IsPullback.of_hasPullback E.p t,
      SchemeFamilyBaseChange.baseChangeLaw_zero E t,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative E t⟩
  let N := liftMarking E F t f hc A
  have hx : N.x.val ≫ f = M.x.val :=
    (liftPoint_comp E F t f hc A.x).trans (Marking.cast_x E _ _)
  have hy : N.y.val ≫ f = M.y.val :=
    (liftPoint_comp E F t f hc A.y).trans (Marking.cast_y E _ _)
  obtain ⟨q, ⟨h, hh, hf⟩, hu⟩ := hD T F N t f hc
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · rw [asLocal_x, ← Category.assoc, ← hh.2.2.2.1, Category.assoc, hf]
    exact hx
  · rw [asLocal_y, ← Category.assoc, ← hh.2.2.2.2, Category.assoc, hf]
    exact hy
  · intro q' hq'
    apply hu q'
    apply marked_factor E k σ D.family F D.projection D.comparison D.cartesian
      t f hc q'.val q'.property D.marking N
    · exact hx.trans (by simpa only [asLocal_x] using hq'.1.symm)
    · exact hy.trans (by simpa only [asLocal_y] using hq'.2.symm)


attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

def localCover (P : LocalPresentation k S σ E) : LocalPointCover E P.base :=
  localPointCover E (SchemeLocalClassifier.family P) P.base P.comparison
    ⟨P.cartesian, by rw [SchemeLocalClassifier.family_zero]; exact P.zero_eq, P.mul_eq⟩
    (affinePointCover E P)

lemma localCover_represents (P : LocalPresentation k S σ E) :
    LocalPointRepresents E (localCover E k σ P) :=
  localPointCover_represents E _ _ _ _ _ (affinePointCover_represents E P)

lemma localCover_geometry (P : LocalPresentation k S σ E) :
    IsFinite (localCover E k σ P).projection ∧ Etale (localCover E k σ P).projection ∧
      Surjective (localCover E k σ P).projection ∧
        ∀ z, (localCover E k σ P).projection.finrank z = 96 := by
  letI : Algebra ℚ P.ring := Algebra.compHom P.ring (algebraMap ℚ k)
  letI : P.equation.IsElliptic := P.elliptic
  exact affine_geometry P.ring P.equation P.law P.originLaw
    (Representability.level P.ring P.equation P.law P.originLaw 4)
    (Representability.represents P.ring P.equation P.law P.originLaw 4)

def presentation (s : S) : LocalPresentation k S σ E :=
  (scheme_local_weierstrass k S σ E s).choose

lemma presentation_covers (s : S) : s ∈ Set.range (presentation E k σ s).base :=
  (scheme_local_weierstrass k S σ E s).choose_spec

def presentationCover : S.OpenCover where
  I₀ := S
  X s := ArithmeticThetaLocalWeierstrassR0203.Base (presentation E k σ s).ring
  f s := (presentation E k σ s).base
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun s => ⟨s, presentation_covers E k σ s⟩,
      fun s => (presentation E k σ s).openImmersion⟩

include k σ in
lemma scheme_finite_etale (D : Cover E) (hD : Represents E D) :
    IsFinite D.projection ∧ Etale D.projection := by
  have hd := asLocal_represents E k σ D hD
  have hloc (s : S) :
      IsFinite ((presentationCover E k σ).pullbackHom D.projection s) ∧
        Etale ((presentationCover E k σ).pullbackHom D.projection s) := by
    let P := presentation E k σ s
    let C := localCover E k σ P
    have hp := LocalPointCover.map_isPullback E C (asLocal E D)
      (localCover_represents E k σ P) hd P.base (Category.comp_id P.base)
    change IsPullback _ C.projection D.projection P.base at hp
    obtain ⟨hf, he, _, _⟩ := localCover_geometry E k σ P
    letI := hf
    letI := he
    change IsFinite (pullback.snd D.projection P.base) ∧
      Etale (pullback.snd D.projection P.base)
    rw [← hp.isoPullback_inv_snd]
    exact ⟨inferInstance, inferInstance⟩
  exact ⟨IsZariskiLocalAtTarget.of_openCover (presentationCover E k σ) (fun s => (hloc s).1),
    IsZariskiLocalAtTarget.of_openCover (presentationCover E k σ) (fun s => (hloc s).2)⟩

include k σ in
lemma scheme_geometry (D : Cover E) (hD : Represents E D) : Geometry E D 96 := by
  obtain ⟨hf, he⟩ := scheme_finite_etale E k σ D hD
  letI := hf
  letI := he
  have hd := asLocal_represents E k σ D hD
  have hr (s : S) : D.projection.finrank s = 96 := by
    let P := presentation E k σ s
    let C := localCover E k σ P
    have hp := LocalPointCover.map_isPullback E C (asLocal E D)
      (localCover_represents E k σ P) hd P.base (Category.comp_id P.base)
    change IsPullback _ C.projection D.projection P.base at hp
    obtain ⟨x, hx⟩ := presentation_covers E k σ s
    rw [← hx, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp]
    exact (localCover_geometry E k σ P).2.2.2 x
  exact ⟨hf, he, D.projection.one_le_finrank_iff_surjective.mp (by
    intro s; change 1 ≤ D.projection.finrank s; rw [hr]; decide), hr⟩

end SchemeGeometry

#print axioms marking_card_geometric
#print axioms representing_rank
#print axioms scheme_geometry
#print axioms UniversalEvaluation.exists_evaluation
#print axioms levelDegree_four
#print axioms etale_nsmul_relative
#print axioms multiplication_finite_etale
#print axioms independent_clopen
#print axioms representing_finite_etale
end ArithmeticThetaEvenMarkingTorsorR0216.SchemeFourCoverGeometry

namespace ArithmeticThetaEvenMarkingTorsorR0216
/-- The actual full-four marking cover is finite étale and surjective of degree 96. -/
theorem scheme_four_cover_geometry :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∀ D : Cover E, Represents E D → Geometry E D 96 := by
  intro k _ _ S σ E D hD
  exact SchemeFourCoverGeometry.scheme_geometry E k σ D hD
#print axioms scheme_four_cover_geometry
end ArithmeticThetaEvenMarkingTorsorR0216
