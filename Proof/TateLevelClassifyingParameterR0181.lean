module

public import TateCuspDefinitionsR0181

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
namespace TateLevelClassifyingParameter
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLevelCompactificationR0179

/-- Specialize the accepted local classification and effective descent to the
specified Tate curve and the specified compatible quotient. -/
lemma classifying_exists_unique
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L) :
    ∃! b : Puncture k ⟶ OpenBase k L D, ClassifiesTate k L D E b := by
  letI := E.elliptic
  obtain ⟨N⟩ := compatible_local_coverage k L hL heven D.atlas D.two D.canonical
    D.cover D.quotient (LaurentSeries k) (TateCurve k L) E.law E.originLaw E.marking
  obtain ⟨b, f, hf⟩ := NormalAffineClassifyingConstruction.descend_local
    hL heven D.canonical E.originLaw N
  refine ⟨b, ⟨f, hf⟩, ?_⟩
  rintro b' ⟨f', hf'⟩
  exact (compatible_classifying_uniqueness k L hL heven D.atlas D.two D.canonical
    D.cover D.quotient (LaurentSeries k) (TateCurve k L) E.law E.originLaw E.marking
    b' b f' f hf' hf).1

open CategoryTheory.Limits
open ArithmeticThetaLegendreComparisonR0177
open CompatibleClassifyingUniqueness

/-- Lift the classified geometric point to the actual compatible cover. Its
coefficient parameter is the pullback along the prescribed descended map. -/
lemma parameter_lift
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (K : Type u) [Field K] [IsAlgClosed K] (σ : LaurentSeries k →+* K) :
    ∃ (α : LegendreRing k →+* K) (a : Base K ⟶ D.atlas.level.space)
      (P : Presentation k L D.atlas K α a)
      (g : Curve K ((legendre k).map α) ⟶ Curve (LaurentSeries k) (TateCurve k L)),
      a ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α) ∧
      CompatibleAt k L D.atlas D.two a ∧
      α (parameter k) = σ (pulledParameter k L D p b) ∧
      IsPullback g (structureMap K ((legendre k).map α))
        (structureMap (LaurentSeries k) (TateCurve k L)) (Spec.map (CommRingCat.ofHom σ)) ∧
      origin K ((legendre k).map α) ≫ g =
        Spec.map (CommRingCat.ofHom σ) ≫ origin (LaurentSeries k) (TateCurve k L) ∧
      P.marking.x.val ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ E.marking.x.val ∧
      P.marking.y.val ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ E.marking.y.val := by
  obtain ⟨f, hf⟩ := hb
  let i := Spec.map (CommRingCat.ofHom σ)
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨a₀, ha₀⟩ := lift_geometric_point D.quotient.quotient.q (i ≫ b)
  let a := a₀ ≫ D.cover.inclusion
  let α := (Spec.preimage (a ≫ D.atlas.level.projection)).hom
  have ha : a ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α) :=
    (Spec.map_preimage _).symm
  obtain ⟨P⟩ := presentation_exists k L D.atlas K α a ha
  have hai : a ≫ D.atlas.quotient.q = i ≫ (b ≫ D.quotient.inclusion) := by
    rw [show a = a₀ ≫ D.cover.inclusion from rfl, Category.assoc,
      D.quotient.cartesian.w, ← Category.assoc, ha₀, Category.assoc]
  obtain ⟨g, hg, hgo, hgx, hgy⟩ := comparison_to_source P E.marking i
    (b ≫ D.quotient.inclusion) f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hai
  refine ⟨α, a, P, g, ha, compatible_comp D.two D.cover a₀, ?_, hg, hgo, hgx, hgy⟩
  have hmap : Spec.map (CommRingCat.ofHom α) = i ≫ (b ≫ p) := by
    rw [← ha]
    change (a₀ ≫ D.cover.inclusion) ≫ D.atlas.level.projection = _
    rw [Category.assoc, ← hp.1, ← Category.assoc, ha₀, Category.assoc]
  have hr : α = σ.comp (Spec.preimage (b ≫ p)).hom := by
    have hcat : CommRingCat.ofHom α =
        CommRingCat.ofHom (σ.comp (Spec.preimage (b ≫ p)).hom) := by
      apply Spec.map_injective
      calc
        _ = i ≫ (b ≫ p) := hmap
        _ = _ := by rw [CommRingCat.ofHom_comp, Spec.map_comp,
          CommRingCat.ofHom_hom, Spec.map_preimage]
    exact congrArg CommRingCat.Hom.hom hcat
  rw [hr]
  rfl

/-- A pointed projective isomorphism preserves the literal invariant ratio. -/
lemma invariant_of_pointed_iso
    (K : Type u) [Field K] (W V : WeierstrassCurve K)
    [W.IsElliptic] [V.IsElliptic]
    (e : Curve K W ≅ Curve K V)
    (he : e.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K V) :
    W.c₄ ^ 3 / W.Δ = V.c₄ ^ 3 / V.Δ := by
  obtain ⟨C, hC, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange.solution
      K W V W.isUnit_Δ V.isUnit_Δ e he ho
  rw [← hC, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_Δ,
    mul_pow, ← pow_mul]
  exact (mul_div_mul_left _ _ (pow_ne_zero 12 (Units.ne_zero C.u⁻¹))).symm

/-- Evaluate the universal Legendre invariant without making a choice of a
permutation of its three branch points. -/
lemma legendre_invariant
    (K : Type u) [Field K] [CharZero K] (a : K) :
    (legendreAt K a).c₄ ^ 3 / (legendreAt K a).Δ =
      256 * (1-a+a^2)^3 / (a^2*(1-a)^2) := by
  have hc : (legendreAt K a).c₄ = 16 * (1-a+a^2) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, legendreAt]
    ring
  have hd : (legendreAt K a).Δ = 16 * (a^2*(1-a)^2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, legendreAt]
    ring
  rw [hc, hd, mul_pow]
  rw [show (16 : K)^3 = 16 * 256 by norm_num, mul_assoc]
  exact mul_div_mul_left _ _ (by norm_num : (16 : K) ≠ 0)

/-- Compare a given Cartesian presentation with coefficient base change. -/
lemma coefficient_iso
    {R K : Type u} [CommRing R] [CommRing K]
    (W : WeierstrassCurve R) (V : WeierstrassCurve K) (σ : R →+* K)
    (g : Curve K V ⟶ Curve R W)
    (hg : IsPullback g (structureMap K V) (structureMap R W)
      (Spec.map (CommRingCat.ofHom σ)))
    (hgo : origin K V ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ origin R W) :
    ∃ (e : Curve K V ≅ Curve K (W.map σ)),
      e.hom ≫ structureMap K (W.map σ) = structureMap K V ∧
      origin K V ≫ e.hom = origin K (W.map σ) := by
  obtain ⟨c, _, hc, hco, _⟩ := NormalFormConstruction.coefficient_comparison W σ
  obtain ⟨e, hep, hec⟩ := OrderedLegendreParameterRigidity.cartesian_iso
    (structureMap R W) (structureMap R W) (structureMap K V)
    (structureMap K (W.map σ)) (Spec.map (CommRingCat.ofHom σ))
    g c hg hc (Iso.refl _) (Category.id_comp _)
  simp only [Iso.refl_hom, Category.comp_id] at hec
  refine ⟨e, hep, ?_⟩
  apply hc.hom_ext
  · rw [Category.assoc, hec, hgo, hco]
  · rw [Category.assoc, hep, BaseChange.origin_over, BaseChange.origin_over]

/-- The invariant comparison for every marking, over the original Laurent
series field. Algebraic closure is used only to lift the finite cover. -/
lemma classifying_j
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    legendreJ k (pulledParameter k L D p b) = tateJ k L := by
  let K := AlgebraicClosure (LaurentSeries k)
  let σ := algebraMap (LaurentSeries k) K
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  letI : CharZero K := charZero_of_injective_ringHom σ.injective
  letI := E.elliptic
  obtain ⟨α, a, P, g, ha, hcompat, hα, hg, hgo, hgx, hgy⟩ :=
    parameter_lift k L D E p hp b hb K σ
  obtain ⟨e, hep, heo⟩ := coefficient_iso (TateCurve k L) ((legendre k).map α) σ g hg hgo
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  letI : ((legendre k).map α).IsElliptic := inferInstance
  have hj := invariant_of_pointed_iso K ((legendre k).map α) ((TateCurve k L).map σ)
    e hep heo
  have hleg : (legendre k).map α = legendreAt K (α (parameter k)) := by
    ext <;> simp [legendre, legendreAt] <;> ring
  rw [hleg, legendre_invariant, hα, WeierstrassCurve.map_c₄,
    WeierstrassCurve.map_Δ] at hj
  apply σ.injective
  simpa only [legendreJ, tateJ, map_div₀, map_mul, map_pow, map_sub, map_add,
    map_one, map_ofNat] using hj

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts
open OrderedLegendreParameterRigidity

/-- Extract the affine x transformation and its quadratic-coefficient equation
from the accepted polar-filtration and variable-change results. -/
lemma affine_x_transform
    (K : Type u) [Field K] [CharZero K] (W V : WeierstrassCurve K)
    (hw1 : W.a₁ = 0) (hv1 : V.a₁ = 0)
    (f : Curve K W ≅ Curve K V)
    (hf : f.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ f.hom = origin K V) :
    ∃ (e : ChartRing K V ≃+* ChartRing K W) (a : Kˣ) (r : K),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartInclusion K V =
        chartInclusion K W ≫ f.hom ∧
      e (xOverZ V.toProjective) = scalar W (a : K) * xOverZ W.toProjective + scalar W r ∧
      V.a₂ = (a : K) * W.a₂ - 3*r := by
  obtain ⟨e, hec, hei⟩ := ChartEquiv.solution K W V f hf ho
  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := exists_ringHom_originChartRing_powerSeries W
  obtain ⟨l, hlc, hlx, hly, hF2, hF3⟩ := LaurentFiltration.solution K W Φ hΦc hΦx hΦz
  obtain ⟨hx1, hx2, hy1, hy2⟩ := LaurentCoeff.solution K W V f hf ho
    e.toRingHom hei Φ hΦc hΦx hΦz l hlc hlx hly
  obtain ⟨a, b, r, s, t, hx, hy⟩ := VariableChange.WMLocal.triangular_of_coeff
    (scalar W) (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ V.toProjective) (yOverZ V.toProjective) e.toRingHom l
    hF2 hF3 hx1 hx2 hy1 hy2
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx hy
  obtain ⟨g, gx, gy⟩ := VariableChange.WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv
    W V e hec a b r s t hx hy
  obtain ⟨C, hC, hu, hCr, hCs, hCt⟩ := Triangular.solution K W V g a⁻¹ b⁻¹
    (-((↑(a⁻¹) : K) * r)) (-((↑(b⁻¹) : K) * s * (↑(a⁻¹) : K))) ((↑(b⁻¹) : K) * (s * (↑(a⁻¹) : K) * r - t)) gx gy
  have hi : (↑C.u⁻¹ : K)^2 = (a : K) := by
    have h := congrArg Inv.inv hu.1
    simpa only [inv_pow, Units.val_inv_eq_inv_val, inv_inv] using h
  have hs : C.s = 0 := by
    have h := congrArg WeierstrassCurve.a₁ hC
    rw [WeierstrassCurve.variableChange_a₁, hw1, hv1, zero_add] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (Units.ne_zero _))).resolve_left
      (by norm_num)
  have h2 := congrArg WeierstrassCurve.a₂ hC
  rw [WeierstrassCurve.variableChange_a₂, hi, hs, hCr] at h2
  have hai : (a : K) * ((↑(a⁻¹) : K) : K) = 1 := Units.mul_inv a
  refine ⟨e, a, r, hei, hx, ?_⟩
  calc
    V.a₂ = (a : K) * (W.a₂ + 3 * (-((↑(a⁻¹) : K) * r))) := by simpa using h2.symm
    _ = (a : K) * W.a₂ - 3 * (((a : K) * (↑(a⁻¹) : K)) * r) := by ring
    _ = _ := by rw [hai, one_mul]

/-- The two ordered affine points and the quadratic coefficient determine the
Legendre parameter under any pointed projective isomorphism. -/
lemma ordered_parameter_of_iso
    (K : Type u) [Field K] [CharZero K] (W V : WeierstrassCurve K)
    (lam e0 e1 e2 y0 y1 : K)
    (hw1 : W.a₁ = 0) (hv1 : V.a₁ = 0)
    (hw2 : W.a₂ = -(lam+1)) (hv2 : V.a₂ = -(e0+e1+e2))
    (p0 p1 : Base K ⟶ Curve K W) (q0 q1 : Base K ⟶ Curve K V)
    (hp0 : HasCoordinates K W p0 0 0) (hp1 : HasCoordinates K W p1 1 0)
    (hq0 : HasCoordinates K V q0 e0 y0) (hq1 : HasCoordinates K V q1 e1 y1)
    (f : Curve K W ≅ Curve K V)
    (hf : f.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ f.hom = origin K V)
    (h0 : p0 ≫ f.hom = q0) (h1 : p1 ≫ f.hom = q1) :
    lam = (e2-e0)/(e1-e0) := by
  obtain ⟨e, a, r, hei, hx, hcoeff⟩ := affine_x_transform K W V hw1 hv1 f hf ho
  obtain ⟨hp0o, χ0, rfl, χ0x, χ0y⟩ := hp0
  obtain ⟨hp1o, χ1, rfl, χ1x, χ1y⟩ := hp1
  obtain ⟨hq0o, ψ0, rfl, ψ0x, ψ0y⟩ := hq0
  obtain ⟨hq1o, ψ1, rfl, ψ1x, ψ1y⟩ := hq1
  have hc0 := evaluation_scalar W χ0 hp0o
  have hc1 := evaluation_scalar W χ1 hp1o
  have hχ0 := evaluation_comp W V f.hom e.toRingHom hei χ0 ψ0 h0
  have hχ1 := evaluation_comp W V f.hom e.toRingHom hei χ1 ψ1 h1
  have ev0 (z : ChartRing K V) : χ0 (e z) = ψ0 z := RingHom.congr_fun hχ0 z
  have ev1 (z : ChartRing K V) : χ1 (e z) = ψ1 z := RingHom.congr_fun hχ1 z
  have hr : r = e0 := by
    have h := congrArg χ0 hx
    simpa only [ev0, ψ0x, map_add, map_mul, hc0, χ0x, mul_zero, zero_add] using h.symm
  have ha : (a : K) + r = e1 := by
    have h := congrArg χ1 hx
    simpa only [ev1, ψ1x, map_add, map_mul, hc1, χ1x, mul_one] using h.symm
  rw [hw2, hv2] at hcoeff
  have hpar : lam * (e1-e0) = e2-e0 := by
    rw [← ha, ← hr, add_sub_cancel_right]
    linear_combination hcoeff - ha - hr
  apply (eq_div_iff _).mpr hpar
  rw [← ha, ← hr, add_sub_cancel_right]
  exact Units.ne_zero a

/-- The specified canonical marking fixes the first two half-level x
coordinates in the literal ordering used to define the Tate cubic. -/
lemma canonical_half_coordinates
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (E : TateLevel k L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (hcan : CanonicalMarking k L ζ E) :
    ∃ y0 y1 : LaurentSeries k,
      HasCoordinates (LaurentSeries k) (TateCurve k L)
        (E.law.nsmul (𝟙 _) (L/2) E.marking.x).val
        (ArithmeticThetaCompactifiedDifferentialR0145.root k L 0) y0 ∧
      HasCoordinates (LaurentSeries k) (TateCurve k L)
        (E.law.nsmul (𝟙 _) (L/2) E.marking.y).val
        (ArithmeticThetaCompactifiedDifferentialR0145.root k L 1) y1 := by
  have heq : L = L/2*2 := (Nat.div_mul_cancel (even_iff_two_dvd.mp heven)).symm
  have hz : ζ^(L/2) = -1 := (IsPrimitiveRoot.pow (by omega) hζ heq).eq_neg_one_of_two_right
  have hx := hcan ⟨L/2, by omega⟩ ⟨0, by omega⟩ (Or.inl (by dsimp; omega))
  have hy := hcan ⟨0, by omega⟩ ⟨L/2, by omega⟩ (Or.inr (by dsimp; omega))
  refine ⟨algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L 0 (-1)),
    algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L (L/2) 1), ?_, ?_⟩
  · simpa [coordinatePoint, E.law.nsmul_zero, E.law.mul_one, hz,
      ArithmeticThetaCompactifiedDifferentialR0145.root,
      ArithmeticThetaCubicModelR0144.rootSeries] using hx
  · simpa [coordinatePoint, E.law.nsmul_zero, E.law.one_mul,
      ArithmeticThetaCompactifiedDifferentialR0145.root,
      ArithmeticThetaCubicModelR0144.rootSeries] using hy

open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- The parameter is the complete ordered cross-ratio in the original field. -/
lemma canonical_parameter
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hcan : CanonicalMarking k L ζ E) :
    pulledParameter k L D p b =
      (ArithmeticThetaCompactifiedDifferentialR0145.root k L 2 -
        ArithmeticThetaCompactifiedDifferentialR0145.root k L 0) /
      (ArithmeticThetaCompactifiedDifferentialR0145.root k L 1 -
        ArithmeticThetaCompactifiedDifferentialR0145.root k L 0) := by
  let K := AlgebraicClosure (LaurentSeries k)
  let σ := algebraMap (LaurentSeries k) K
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  letI : CharZero K := charZero_of_injective_ringHom σ.injective
  letI := E.elliptic
  obtain ⟨α, a, P, g, ha, hcompat, hα, hg, hgo, hgx, hgy⟩ :=
    parameter_lift k L D E p hp b hb K σ
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  letI : ((legendre k).map α).IsElliptic := inferInstance
  obtain ⟨p0, p1, hp0, hp1, hn0, hn1⟩ := canonical_points P ha D.two D.canonical hcompat
  have hbase := MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    E.law P.law E.originLaw P.originLaw σ g hg hgo
  have hnx : p0 ≫ g = Spec.map (CommRingCat.ofHom σ) ≫
      (E.law.nsmul (𝟙 _) (L/2) E.marking.x).val := by
    rw [← hn0, ← comp_schemeNsmul, Category.assoc, hbase.2.2,
      ← Category.assoc, hgx, Category.assoc, comp_schemeNsmul]
  have hny : p1 ≫ g = Spec.map (CommRingCat.ofHom σ) ≫
      (E.law.nsmul (𝟙 _) (L/2) E.marking.y).val := by
    rw [← hn1, ← comp_schemeNsmul, Category.assoc, hbase.2.2,
      ← Category.assoc, hgy, Category.assoc, comp_schemeNsmul]
  obtain ⟨y0, y1, ht0, ht1⟩ := canonical_half_coordinates k L hL heven E ζ hζ hcan
  obtain ⟨c, _, hc, hco, _, _, _, hlift⟩ :=
    NormalFormConstruction.coefficient_comparison (TateCurve k L) σ
  obtain ⟨q0, hq0, heq0⟩ := hlift _ _ _ ht0
  obtain ⟨q1, hq1, heq1⟩ := hlift _ _ _ ht1
  obtain ⟨e, hep, hec⟩ := OrderedLegendreParameterRigidity.cartesian_iso
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap K ((legendre k).map α)) (structureMap K ((TateCurve k L).map σ))
    (Spec.map (CommRingCat.ofHom σ)) g c hg hc (Iso.refl _) (Category.id_comp _)
  simp only [Iso.refl_hom, Category.comp_id] at hec
  have heo : origin K ((legendre k).map α) ≫ e.hom =
      origin K ((TateCurve k L).map σ) := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hgo, hco]
    · rw [Category.assoc, hep, BaseChange.origin_over, BaseChange.origin_over]
  have he0 : p0 ≫ e.hom = q0 := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hnx, heq0]
    · rw [Category.assoc, hep, hp0.1, hq0.1]
  have he1 : p1 ≫ e.hom = q1 := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hny, heq1]
    · rw [Category.assoc, hep, hp1.1, hq1.1]
  have hparam := ordered_parameter_of_iso K ((legendre k).map α) ((TateCurve k L).map σ)
    (α (parameter k)) (σ (ArithmeticThetaCompactifiedDifferentialR0145.root k L 0))
    (σ (ArithmeticThetaCompactifiedDifferentialR0145.root k L 1))
    (σ (ArithmeticThetaCompactifiedDifferentialR0145.root k L 2)) (σ y0) (σ y1)
    (by simp [legendre]) (by simp [TateCurve, ArithmeticThetaCompactifiedDifferentialR0145.curve])
    (by simp [legendre]; ring)
    (by simp [TateCurve, ArithmeticThetaCompactifiedDifferentialR0145.curve]; ring)
    p0 p1 q0 q1 hp0 hp1 hq0 hq1 e hep heo he0 he1
  rw [hα] at hparam
  apply σ.injective
  simpa only [map_div₀, map_sub] using hparam

end TateLevelClassifyingParameter

/-- Classification of the specified Tate family, its actual invariant, and the
complete Legendre parameter with the canonical ordered labels. -/
theorem tate_level_classifying_parameter :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L), ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaTateCuspsR0181.TateLevel k L) (p : Quiver.Hom (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D) (ArithmeticThetaRelativeDiscriminantR0171.Base (ArithmeticThetaLegendreAtlasR0176.LegendreRing k))), ArithmeticThetaLevelCompactificationR0179.IsParameter k L D p → ∃! b : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Puncture k) (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D), ArithmeticThetaTateCuspsR0181.ClassifiesTate k L D E b ∧ ArithmeticThetaTateCuspsR0181.legendreJ k (ArithmeticThetaTateCuspsR0181.pulledParameter k L D p b) = ArithmeticThetaTateCuspsR0181.tateJ k L ∧ (∀ ζ : k, IsPrimitiveRoot ζ L → ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ E → ArithmeticThetaTateCuspsR0181.pulledParameter k L D p b = (ArithmeticThetaCompactifiedDifferentialR0145.root k L 2 - ArithmeticThetaCompactifiedDifferentialR0145.root k L 0) / (ArithmeticThetaCompactifiedDifferentialR0145.root k L 1 - ArithmeticThetaCompactifiedDifferentialR0145.root k L 0)) := by
  intro k _ _ L hL heven D E p hp
  obtain ⟨b, hb, huniq⟩ := TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E
  refine ⟨b, ⟨hb, TateLevelClassifyingParameter.classifying_j k L D E p hp b hb, ?_⟩, ?_⟩
  · intro ζ hζ hcan
    exact TateLevelClassifyingParameter.canonical_parameter k L hL heven D E p hp b hb ζ hζ hcan
  · intro b' hb'
    exact huniq b' hb'.1

#print axioms tate_level_classifying_parameter

end ArithmeticThetaTateCuspsR0181
