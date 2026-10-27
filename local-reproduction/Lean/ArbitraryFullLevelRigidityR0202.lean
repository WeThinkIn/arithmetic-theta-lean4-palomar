import FullLevelAutomorphismRigidityR0176
import OrderedLegendreParameterRigidityR0177
import LegendreNormalFormR0177

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202.FullLevelRigidity
open Finset IsLocalRing

/-- Prime-to-residue-characteristic roots of unity have no infinitesimal
motion at the identity, without Noetherian or reduced hypotheses. -/
lemma root_eq_one_of_residue_eq_one {R : Type u} [CommRing R] [IsLocalRing R]
    (x : R) (n : ℕ) (hn : IsUnit (n : R))
    (hx : x ^ n = 1) (hres : residue R x = 1) : x = 1 := by
  have hsum : IsUnit (∑ i ∈ range n, x ^ i) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hn' := (hn.map (residue R)).ne_zero
    simpa only [map_sum, map_pow, hres, one_pow, sum_const, card_range,
      nsmul_eq_mul, mul_one, map_natCast] using hn'
  apply sub_eq_zero.mp
  apply hsum.mul_right_eq_zero.mp
  rw [geom_sum_mul, hx, sub_self]

/-- The discriminant forces the multiplier of any stabilizing variable
change to be a twelfth root of unity over the actual coefficient ring. -/
lemma stabilizer_multiplier_pow {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange R) (hC : C • W = W) :
    (C.u : R) ^ 12 = 1 := by
  have hd := congrArg WeierstrassCurve.Δ hC
  rw [WeierstrassCurve.variableChange_Δ] at hd
  have hi : (↑C.u⁻¹ : R) ^ 12 = 1 := by
    apply W.isUnit_Δ.mul_left_cancel
    simpa only [mul_one, one_mul, mul_comm] using hd
  have hp : (C.u : R) ^ 12 * (↑C.u⁻¹ : R) ^ 12 = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  simpa only [hi, mul_one] using hp

/-- Coefficient comparison after the multiplier is trivial. -/
lemma variableChange_eq_one_of_multiplier {R : Type u} [CommRing R]
    (h6 : IsUnit (6 : R)) (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) (hC : C • W = W) (hu : C.u = 1) :
    C = 1 := by
  have h23 : IsUnit ((2 : R) * 3) := by norm_num; exact h6
  have h2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left h23
  have h3 : IsUnit (3 : R) := isUnit_of_mul_isUnit_right h23
  have e1 := congrArg WeierstrassCurve.a₁ hC
  have e2 := congrArg WeierstrassCurve.a₂ hC
  have e3 := congrArg WeierstrassCurve.a₃ hC
  simp only [WeierstrassCurve.variableChange_def, hu, inv_one, Units.val_one,
    one_pow, one_mul] at e1 e2 e3
  have hs : C.s = 0 := by
    apply h2.mul_right_eq_zero.mp
    linear_combination e1
  have hr : C.r = 0 := by
    apply h3.mul_right_eq_zero.mp
    linear_combination e2 + (W.a₁ + C.s) * hs
  have ht : C.t = 0 := by
    apply h2.mul_right_eq_zero.mp
    linear_combination e3 - W.a₁ * hr
  obtain ⟨u, r, s, t⟩ := C
  simp only at hu hr hs ht
  subst hu hr hs ht
  exact WeierstrassCurve.VariableChange.one_def.symm

/-- A stabilizer is determined by its residue multiplier even for nonreduced,
non-Noetherian local rational algebras. -/
lemma local_stabilizer_eq_one {R : Type u} [CommRing R] [IsLocalRing R]
    [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange R) (hC : C • W = W)
    (hres : residue R (C.u : R) = 1) : C = 1 := by
  have h6 : IsUnit (6 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (6 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  have h12 : IsUnit (12 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (12 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  apply variableChange_eq_one_of_multiplier h6 W C hC
  apply Units.ext
  exact root_eq_one_of_residue_eq_one (C.u : R) 12 h12
    (stabilizer_multiplier_pow W C hC) hres

#print axioms local_stabilizer_eq_one
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel
open WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange.WMLocal

/-- The actual pointed isomorphism comes from a variable change over any local
ring. The polar-filtration argument needs no Artinian hypothesis. -/
theorem local_variableChange
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T) (_hΔ : IsUnit W.Δ) (hΔ' : IsUnit W'.Δ)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by
  classical

  obtain ⟨e, hec, heι⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv.solution T W W' Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.solution T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff.solution T W W' Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := WMLocal.triangular_of_coeff (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W' e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := WMLocal.symm_triangular (WMLocal.cZ W) (WMLocal.cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular.solution T W W' g w₁ w₂ r₁ s₁ t₁ hgx hgy
  subst hC

  obtain ⟨φ, hφ, hvc, _, _⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W.toProjective C
  refine ⟨C, rfl, φ, hφ, hvc, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]

  obtain ⟨a, haι, hac, hax, hay⟩ := WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom W.toProjective C φ hφ hvc
  have hec' : ∀ b : T, e.symm (WMLocal.cZ W b) = WMLocal.cZ (C • W) b := fun b => by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hec b).symm
  have hae : a = e.symm.toRingHom := by
    apply WMLocal.zChart_ringHom_ext W.toProjective
    · refine RingHom.ext fun b => ?_
      change a (WMLocal.cZ W b) = e.symm (WMLocal.cZ W b)
      rw [hec']
      exact hac b
    · change a (xOverZ W.toProjective) = e.symm (xOverZ W.toProjective)
      rw [hax, ex, hu2, hCr]
      rfl
    · change a (yOverZ W.toProjective) = e.symm (yOverZ W.toProjective)
      rw [hay, ey, hCs, hu3, hCt]
      rfl
  apply ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartExt.solution T (C • W)
  rw [haι, hae]

  have hcomp : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => ?_
    show e.symm (e z) = z
    exact e.symm_apply_apply z
  have hee : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  symm
  calc zChartι (C • W).toProjective ≫ Ψ.inv
      = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
          zChartι (C • W).toProjective ≫ Ψ.inv := by rw [hee, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι (C • W).toProjective) ≫ Ψ.inv) := by
        simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ((zChartι W.toProjective ≫ Ψ.hom) ≫ Ψ.inv) := by rw [heι]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ zChartι W.toProjective := by
        rw [Category.assoc, Ψ.hom_inv_id, Category.comp_id]

#print axioms local_variableChange

open CategoryTheory.Limits
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaRelativeKatoNaturalityR0170

lemma mul_val_congr (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
    {T : Scheme.{u}} {t t' : T ⟶ Base R} (ht : t = t')
    (x y : SchemeHomOver t (structureMap R W))
    (x' y' : SchemeHomOver t' (structureMap R W))
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (G.mul t x y).val = (G.mul t' x' y').val := by
  subst t'
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  subst x'
  subst y'
  rfl

/-- Transport the actual law and marking along a specified pointed Cartesian
comparison, retaining the equations of both full-level labels. -/
lemma transport_level {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (Ws : WeierstrassCurve S)
    (G : Law R W) (hG : IsOriginLaw R W G) (ι : R →+* S)
    (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) (baseMap R S ι))
    (he' : origin S Ws ≫ b = baseMap R S ι ≫ origin R W)
    (L : ℕ) (A : FullLevel R W G L (baseMap R S ι)) :
    ∃ H : Law S Ws, IsOriginLaw S Ws H ∧ IsBaseChange R W G S Ws H ι b ∧
      ∃ M : FullLevel S Ws H L (𝟙 (Base S)),
        M.x.val ≫ b = A.x.val ∧ M.y.val ≫ b = A.y.val := by
  let fs := structureMap S Ws
  obtain ⟨H, hm, ho⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      ι (structureMap R W) fs b hb G
  have hH : IsOriginLaw S Ws H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [ho, hG.1, Category.assoc, he', baseMap]
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z)
            (WeierstrassProjModel.kwZeroSect S Ws).property).trans
            (Category.comp_id t)).symm)
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hn := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp ι fs b hb G H hm ho
  let push (x : SchemeHomOver (𝟙 (Base S)) fs) :
      SchemeHomOver (baseMap R S ι) (structureMap R W) :=
    ⟨x.val ≫ b, by
      have hw : b ≫ structureMap R W = fs ≫ baseMap R S ι := hb.w
      rw [Category.assoc, hw, ← Category.assoc, x.property, Category.id_comp]⟩
  have hp_inj : Function.Injective push := by
    intro x y h
    apply Subtype.ext
    apply hb.hom_ext
    · exact congrArg Subtype.val h
    · exact x.property.trans y.property.symm
  have hp_one : push (H.one (𝟙 _)) = G.one (baseMap R S ι) := by
    apply Subtype.ext
    change (H.one (𝟙 _)).val ≫ b = _
    rw [hH.1, Category.id_comp, he', hG.1]
  have hp_mul (x y : SchemeHomOver (𝟙 (Base S)) fs) :
      push (H.mul (𝟙 _) x y) = G.mul (baseMap R S ι) (push x) (push y) := by
    apply Subtype.ext
    exact (hm (𝟙 _) x y).trans
      (mul_val_congr R W G (Category.id_comp _) _ _ _ _ rfl rfl)
  have hp_nsmul (x : SchemeHomOver (𝟙 (Base S)) fs) (n : ℕ) :
      push (H.nsmul (𝟙 _) n x) = G.nsmul (baseMap R S ι) n (push x) := by
    induction n with
    | zero => exact hp_one
    | succ n ih => rw [H.nsmul_succ, hp_mul, ih, G.nsmul_succ]
  let lift (x : SchemeHomOver (baseMap R S ι) (structureMap R W)) :
      SchemeHomOver (𝟙 (Base S)) fs :=
    ⟨hb.lift x.val (𝟙 _) (by exact x.property.trans (Category.id_comp _).symm), hb.lift_snd _ _ _⟩
  have hp_lift (x : SchemeHomOver (baseMap R S ι) (structureMap R W)) :
      push (lift x) = x := Subtype.ext (hb.lift_fst _ _ _)
  refine ⟨H, hH, ⟨hb, he', hn⟩, ?_⟩
  refine ⟨{
    x := lift A.x
    y := lift A.y
    killed_x := ?_
    killed_y := ?_
    avoids := ?_ }, ?_, ?_⟩
  · apply hp_inj
    rw [hp_nsmul, hp_lift, A.killed_x, hp_one]
  · apply hp_inj
    rw [hp_nsmul, hp_lift, A.killed_y, hp_one]
  · intro i j hij
    have hc : (H.mul (𝟙 _) (H.nsmul (𝟙 _) i.val (lift A.x))
        (H.nsmul (𝟙 _) j.val (lift A.y))).val ≫ b =
        (G.mul (baseMap R S ι) (G.nsmul (baseMap R S ι) i.val A.x)
          (G.nsmul (baseMap R S ι) j.val A.y)).val := by
      change (push _).val = _
      rw [hp_mul, hp_nsmul, hp_nsmul, hp_lift, hp_lift]
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ ⟨s,hs⟩
    apply Set.disjoint_left.mp (A.avoids i j hij)
    · exact ⟨t,rfl⟩
    · refine ⟨baseMap R S ι s, ?_⟩
      calc
        origin R W (baseMap R S ι s) = b (origin S Ws s) :=
          (congrArg (fun f => f s) he').symm
        _ = _ := (congrArg b hs).trans (congrArg (fun f => f t) hc)

  · exact hb.lift_fst _ _ _
  · exact hb.lift_fst _ _ _

#print axioms transport_level


open ArithmeticThetaLegendreAtlasR0176.FullLevelAutomorphismRigidity

lemma liftIso_over (R : Type u) [CommRing R] (W : WeierstrassCurve R) {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W) :
    (liftIso R W Ws ι b hb e he).hom ≫ structureMap S Ws = structureMap S Ws :=
  hb.lift_snd _ _ _

lemma liftIso_comp (R : Type u) [CommRing R] (W : WeierstrassCurve R) {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W) :
    (liftIso R W Ws ι b hb e he).hom ≫ b = b ≫ e.hom := hb.lift_fst _ _ _

lemma liftIso_origin (R : Type u) [CommRing R] (W : WeierstrassCurve R) {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (ho : origin S Ws ≫ b = ι ≫ origin R W)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W)
    (heO : origin R W ≫ e.hom = origin R W) :
    origin S Ws ≫ (liftIso R W Ws ι b hb e he).hom = origin S Ws := by
  apply hb.hom_ext
  · rw [Category.assoc, liftIso_comp, ← Category.assoc, ho, Category.assoc, heO]
  · rw [Category.assoc, liftIso_over]

/-- Every field specialization of a level-fixing pointed automorphism is the
identity. This is used only to determine residue coefficients, not to infer
an equality over a nonreduced base. -/
lemma field_specialization {R K : Type u} [CommRing R] [Field K] [Algebra ℚ K]
    (W : WeierstrassCurve R) (Wk : WeierstrassCurve K) [Wk.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (ι : R →+* K)
    (b : Curve K Wk ⟶ Curve R W)
    (hb : IsPullback b (structureMap K Wk) (structureMap R W) (baseMap R K ι))
    (hbO : origin K Wk ≫ b = baseMap R K ι ≫ origin R W)
    (L : ℕ) (hL : 3 ≤ L) (M : FullLevel R W G L (𝟙 (Base R)))
    (e : Curve R W ≅ Curve R W)
    (he : e.hom ≫ structureMap R W = structureMap R W)
    (ho : origin R W ≫ e.hom = origin R W)
    (hx : M.x.val ≫ e.hom = M.x.val) (hy : M.y.val ≫ e.hom = M.y.val) :
    (liftIso R W Wk (baseMap R K ι) b hb e he).hom = 𝟙 _ := by
  let A := BaseChange.restrict M (baseMap R K ι) (Category.comp_id _)
  obtain ⟨H, hH, hHG, N, hNx, hNy⟩ := transport_level W Wk G hG ι b hb hbO L A
  apply ArithmeticThetaLegendreAtlasR0176.full_level_automorphism_rigidity K Wk H hH L hL N
    (liftIso R W Wk (baseMap R K ι) b hb e he)
    (liftIso_over R W Wk (baseMap R K ι) b hb e he)
    (liftIso_origin R W Wk (baseMap R K ι) b hb hbO e he ho)
  · apply hb.hom_ext
    · rw [Category.assoc, liftIso_comp, ← Category.assoc, hNx]
      change (baseMap R K ι ≫ M.x.val) ≫ e.hom = baseMap R K ι ≫ M.x.val
      rw [Category.assoc, hx]
    · rw [Category.assoc, liftIso_over]
  · apply hb.hom_ext
    · rw [Category.assoc, liftIso_comp, ← Category.assoc, hNy]
      change (baseMap R K ι ≫ M.y.val) ≫ e.hom = baseMap R K ι ≫ M.y.val
      rw [Category.assoc, hy]
    · rw [Category.assoc, liftIso_over]

#print axioms field_specialization

open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts

/-- Extract the actual chart automorphism and its variable-change coefficients
without discarding the comparison with the original scheme isomorphism. -/
lemma local_chart_coefficients (T : Type u) [CommRing T] [IsLocalRing T]
    (W : WeierstrassCurve T)
    (Ψ : Curve T W ≅ Curve T W)
    (hΨ : Ψ.hom ≫ structureMap T W = structureMap T W)
    (hΨO : origin T W ≫ Ψ.hom = origin T W) :
    ∃ (e : ZChartRing W.toProjective ≃+* ZChartRing W.toProjective)
      (C : WeierstrassCurve.VariableChange T),
      (∀ t, e (cZ W t) = cZ W t) ∧
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W.toProjective =
        zChartι W.toProjective ≫ Ψ.hom) ∧
      C • W = W ∧
      e.symm (xOverZ W.toProjective) = cZ W ((C.u : T)^2) * xOverZ W.toProjective + cZ W C.r ∧
      e.symm (yOverZ W.toProjective) = cZ W ((C.u : T)^3) * yOverZ W.toProjective +
        cZ W ((C.u : T)^2 * C.s) * xOverZ W.toProjective + cZ W C.t := by
  obtain ⟨e, hec, heι⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv.solution T W W Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.solution T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff.solution T W W Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := WMLocal.triangular_of_coeff (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W.toProjective) (yOverZ W.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := WMLocal.symm_triangular (WMLocal.cZ W) (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W.toProjective) (yOverZ W.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular.solution T W W g w₁ w₂ r₁ s₁ t₁ hgx hgy
  refine ⟨e, C, hec, heι, hC, ?_, ?_⟩
  · simpa only [hu2, hCr] using ex
  · simpa only [hCs, hu3, hCt] using ey

/-- The two leading polar coefficients detect the multiplier of a triangular
chart endomorphism. This uses the actual Laurent embedding. -/
lemma triangle_leading_coefficients {T : Type u} [CommRing T]
    (W : WeierstrassCurve T) (a b r s t : T)
    (hx : xOverZ W.toProjective = cZ W a * xOverZ W.toProjective + cZ W r)
    (hy : yOverZ W.toProjective = cZ W b * yOverZ W.toProjective +
      cZ W s * xOverZ W.toProjective + cZ W t) : a = 1 ∧ b = 1 := by
  obtain ⟨lam, hc, hlx, hly⟩ := LaurentFiltration.WMLocal.exists_laurentEmbedding_core W
  obtain ⟨hxlow, hxlead, hylow, hylead⟩ :=
    LaurentFiltration.WMLocal.laurentEmbedding_lead W lam hlx hly
  have h2 := congrArg (fun z => (lam z).coeff (-2)) hx
  have h3 := congrArg (fun z => (lam z).coeff (-3)) hy
  simp only [map_add, map_mul, hc, HahnSeries.coeff_add, hxlead, hylead, HahnSeries.C_apply, HahnSeries.coeff_single] at h2 h3
  norm_num at h2 h3
  simp only [hxlead, hylead, hxlow (-3) (by norm_num), mul_one, mul_zero, add_zero, mul_neg_one] at h2 h3
  exact ⟨h2.symm, by linear_combination h3⟩

#print axioms local_chart_coefficients
#print axioms triangle_leading_coefficients


/-- The scalar map on the affine chart is forced by the specified base map. -/
lemma chart_scalar_naturality {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (σ : R →+* S)
    (b : Curve S V ⟶ Curve R W)
    (hb : b ≫ structureMap R W = structureMap S V ≫ baseMap R S σ)
    (a : ZChartRing W.toProjective →+* ZChartRing V.toProjective)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ zChartι W.toProjective =
      zChartι V.toProjective ≫ b) :
    ∀ r, a (cZ W r) = cZ V (σ r) := by
  have hm : Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom (cZ W)) =
      Spec.map (CommRingCat.ofHom (cZ V)) ≫ Spec.map (CommRingCat.ofHom σ) := by
    rw [← ChartEquiv.WMLocal.zChartι_comp_projModelStrCR W,
      ← Category.assoc, ha]
    change (zChartι V.toProjective ≫ b) ≫ structureMap R W = _
    rw [Category.assoc, hb, ← Category.assoc]
    change (zChartι V.toProjective ≫ projModelStrCR V.toProjective) ≫ _ = _
    rw [ChartEquiv.WMLocal.zChartι_comp_projModelStrCR V]
    rfl
  have hs : a.comp (cZ W) = (cZ V).comp σ :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective (by
      simpa only [Spec.map_comp] using hm :
        Spec.map (CommRingCat.ofHom (cZ W) ≫ CommRingCat.ofHom a) =
        Spec.map (CommRingCat.ofHom σ ≫ CommRingCat.ofHom (cZ V))))
  exact fun r => RingHom.congr_fun hs r

/-- Pointed full-level rigidity over a local rational ring, including all
nilpotent directions. -/
lemma local_rigidity (R : Type u) [CommRing R] [IsLocalRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (L : ℕ) (hL : 3 ≤ L) (M : FullLevel R W G L (𝟙 (Base R)))
    (Ψ : Curve R W ≅ Curve R W)
    (hΨ : Ψ.hom ≫ structureMap R W = structureMap R W)
    (hΨO : origin R W ≫ Ψ.hom = origin R W)
    (hMx : M.x.val ≫ Ψ.hom = M.x.val) (hMy : M.y.val ≫ Ψ.hom = M.y.val) :
    Ψ.hom = 𝟙 _ := by
  let K := ResidueField R
  let σ : R →+* K := residue R
  let Wk := W.map σ
  obtain ⟨b, a, hb, hbO, ha, hax, hay, _⟩ :=
    ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_comparison W σ
  change Spec.map (CommRingCat.ofHom a) ≫ zChartι W.toProjective =
    zChartι Wk.toProjective ≫ b at ha
  have hid := field_specialization W Wk G hG σ b hb hbO L hL M Ψ hΨ hΨO hMx hMy
  have hbfix : b ≫ Ψ.hom = b := by
    rw [← liftIso_comp R W Wk (baseMap R K σ) b hb Ψ hΨ, hid, Category.id_comp]
  obtain ⟨e, C, hec, hei, hC, hex, hey⟩ := local_chart_coefficients R W Ψ hΨ hΨO
  have hac := chart_scalar_naturality W Wk σ b hb.w a ha
  have hefix : a.comp e.toRingHom = a := by
    change (CommRingCat.ofHom (a.comp e.toRingHom)).hom = (CommRingCat.ofHom a).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    apply (cancel_mono (zChartι W.toProjective)).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hei,
      ← Category.assoc, ha, Category.assoc, hbfix]
  have hes (z : ZChartRing W.toProjective) : a (e.symm z) = a z := by
    have h := RingHom.congr_fun hefix (e.symm z)
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply] using h.symm
  have ex := congrArg a hex
  have ey := congrArg a hey
  simp only [map_add, hes, hax, hay] at ex ey
  rw [a.map_mul, hac, hax, hac] at ex
  rw [a.map_mul, a.map_mul, hac, hac, hac, hax, hay] at ey
  obtain ⟨hu2, hu3⟩ := triangle_leading_coefficients Wk
    (σ ((C.u : R)^2)) (σ ((C.u : R)^3)) (σ C.r) (σ ((C.u : R)^2 * C.s)) (σ C.t) ex ey
  have hu : σ (C.u : R) = 1 := by
    rw [map_pow] at hu2 hu3
    calc σ (C.u : R) = σ (C.u : R) ^ 2 * σ (C.u : R) := by rw [hu2, one_mul]
         _ = σ (C.u : R) ^ 3 := by ring
         _ = 1 := hu3
  have hCone : C = 1 := local_stabilizer_eq_one W C hC hu
  subst C
  simp only [WeierstrassCurve.VariableChange.one_def, Units.val_one, one_pow,
    map_one, map_zero, one_mul, zero_mul, add_zero] at hex hey
  have hei' : e.symm.toRingHom = RingHom.id _ := by
    apply VariableChange.WMLocal.zChart_ringHom_ext W.toProjective
    · apply RingHom.ext
      intro r
      change e.symm (cZ W r) = cZ W r
      exact e.injective (by rw [RingEquiv.apply_symm_apply, hec])
    · exact hex
    · exact hey
  have heid : e.toRingHom = RingHom.id _ := by
    apply RingHom.ext
    intro z
    have hh := RingHom.congr_fun hei' (e z)
    simpa using hh.symm
  apply ChartExt.solution R W
  rw [Category.comp_id, ← hei, heid]
  simp

#print axioms chart_scalar_naturality
#print axioms local_rigidity


/-- Equality after every local rational base change implies global equality.
The covering consists of base stalk spectra and is faithfully flat as a family. -/
lemma rigidity_of_local_rigidity (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (L : ℕ) (hL : 3 ≤ L) (M : FullLevel R W G L (𝟙 (Base R)))
    (e : Curve R W ≅ Curve R W)
    (he : e.hom ≫ structureMap R W = structureMap R W)
    (ho : origin R W ≫ e.hom = origin R W)
    (hx : M.x.val ≫ e.hom = M.x.val) (hy : M.y.val ≫ e.hom = M.y.val) :
    e.hom = 𝟙 _ := by
  classical
  let B := Base R
  let S (x : B) := B.presheaf.stalk x
  let σ (x : B) : R →+* S x := (StructureSheaf.toStalk R x).hom
  let t (x : B) := baseMap R (S x) (σ x)
  have ht (x : B) : t x = B.fromSpecStalk x := (Spec.fromSpecStalk_eq' _ _).symm
  let X (x : B) := pullback (structureMap R W) (t x)
  let q (x : B) : X x ⟶ Curve R W := pullback.fst _ _
  have hq (x : B) : q x ≫ e.hom = q x := by
    letI : Algebra ℚ (S x) := ((σ x).comp (algebraMap ℚ R)).toAlgebra
    let Ws := W.map (σ x)
    obtain ⟨b, _, hb, hbO, _⟩ :=
      ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_comparison W (σ x)
    let A := BaseChange.restrict M (t x) (Category.comp_id _)
    obtain ⟨H, hH, hHG, N, hNx, hNy⟩ := transport_level W Ws G hG (σ x) b hb hbO L A
    let es := liftIso R W Ws (t x) b hb e he
    have hes := liftIso_over R W Ws (t x) b hb e he
    have heo := liftIso_origin R W Ws (t x) b hb hbO e he ho
    have hex : N.x.val ≫ es.hom = N.x.val := by
      apply hb.hom_ext
      · rw [Category.assoc, liftIso_comp, ← Category.assoc, hNx]
        change (t x ≫ M.x.val) ≫ e.hom = t x ≫ M.x.val
        rw [Category.assoc, hx]
      · rw [Category.assoc, hes]
    have hey : N.y.val ≫ es.hom = N.y.val := by
      apply hb.hom_ext
      · rw [Category.assoc, liftIso_comp, ← Category.assoc, hNy]
        change (t x ≫ M.y.val) ≫ e.hom = t x ≫ M.y.val
        rw [Category.assoc, hy]
      · rw [Category.assoc, hes]
    have hid := local_rigidity (S x) Ws H hH L hL N es hes heo hex hey
    have hbfix : b ≫ e.hom = b := by
      rw [← liftIso_comp R W Ws (t x) b hb e he, hid, Category.id_comp]
    apply (cancel_epi hb.isoPullback.hom).mp
    change hb.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom =
      hb.isoPullback.hom ≫ pullback.fst _ _
    rw [← Category.assoc, hb.isoPullback_hom_fst, hbfix]
  have hflat (x : B) : Flat (t x) := by
    letI : Algebra R (S x) := (σ x).toAlgebra
    letI : IsLocalization.AtPrime (S x) x.asIdeal :=
      inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (S x) x.asIdeal.primeCompl)
  letI (x : B) : Flat (t x) := hflat x
  letI (x : B) : Flat (q x) := inferInstanceAs (Flat (pullback.fst (structureMap R W) (t x)))
  let p : (∐ X) ⟶ Curve R W := Sigma.desc q
  letI : Flat p := inferInstanceAs (Flat (Sigma.desc q))
  letI : Surjective p := Surjective.sigmaDesc_of_union_range_eq_univ (by
    apply Set.eq_univ_of_forall
    intro z
    let x : B := structureMap R W z
    have hp : t x (closedPoint (S x)) = x := by rw [ht]; exact Scheme.fromSpecStalk_closedPoint
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback (structureMap R W) (t x)) z (closedPoint (S x)) hp.symm
    exact Set.mem_iUnion.mpr ⟨x, v, hv⟩)
  letI : Epi p := Flat.epi_of_flat_of_surjective p
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro x
  simpa only [p, ← Category.assoc, Sigma.ι_desc, Category.comp_id] using hq x

end ArithmeticThetaArbitraryAffineR0202.FullLevelRigidity

namespace ArithmeticThetaArbitraryAffineR0202
/-- A pointed automorphism fixing a full level L ≥ 3 is the identity over
any commutative rational affine base, including nonreduced and zero rings. -/
theorem arbitrary_full_level_rigidity :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (e : CategoryTheory.Iso (ArithmeticThetaRelativeKatoR0169.Curve R W) (ArithmeticThetaRelativeKatoR0169.Curve R W)), CategoryTheory.CategoryStruct.comp (e.hom) (ArithmeticThetaRelativeKatoR0169.structureMap R W) = ArithmeticThetaRelativeKatoR0169.structureMap R W → CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin R W) (e.hom) = ArithmeticThetaRelativeKatoR0169.origin R W → CategoryTheory.CategoryStruct.comp (M.x.val) (e.hom) = M.x.val → CategoryTheory.CategoryStruct.comp (M.y.val) (e.hom) = M.y.val → e.hom = CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeKatoR0169.Curve R W) := by
  intro R _ _ W _ G hG L hL M e he ho hx hy
  exact FullLevelRigidity.rigidity_of_local_rigidity R W G hG L hL M e he ho hx hy

#print axioms arbitrary_full_level_rigidity
end ArithmeticThetaArbitraryAffineR0202





