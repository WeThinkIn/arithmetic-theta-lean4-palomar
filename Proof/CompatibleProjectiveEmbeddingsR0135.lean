module

public import SpecialFiberCubicEmbeddingR0135

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Compatible embeddings of every actual infinitesimal polygon. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace ArithmeticThetaProjectiveEffectivityR0135.CompatibleProjectiveEmbeddingsR0135
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open ArithmeticThetaPolygonCohomologyR0131 ArithmeticThetaPolygonCartierR0133
open PositiveSectionsReductionR0134 SpecialFiberCubicEmbeddingR0135 PolygonCechObstructionR0131
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (a : Fin r → kˣ)
variable (b : CubicBases k r hr T a) (hb : CompatibleBases k T a b)

include hb in
lemma evaluate_reduce (n N : ℕ) (h : n ≤ N) (i : Fin r)
    (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) :
    truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h (evaluate k b N i p) =
      evaluate k b n i p := by
  have he : (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h).comp
      (evaluate k b N i) = evaluate k b n i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, evaluate, MvPolynomial.eval₂Hom_C]
      change truncReduce _ _ n N h (base k N (trunc _ _ N c)) =
        base k n (trunc _ _ n c)
      rw [reduce_base]
      rfl
    · intro j
      simpa [evaluate] using hb.2 n N h j i
  exact RingHom.congr_fun he p

lemma unit_of_reduce {S : Type u} [CommRing S] (t : S) (n : ℕ)
    (x : Trunc S t n) (hx : IsUnit (truncReduce S t 0 n (Nat.zero_le n) x)) :
    IsUnit x := by
  have htop : Ideal.map (truncReduce S t 0 n (Nat.zero_le n))
      (Ideal.span {x}) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.span_singleton_eq_top.mpr hx
  exact Ideal.span_singleton_eq_top.mp
    (PositiveGlobalGenerationR0134.ideal_top_of_reduction t n _ htop)

include hb in
lemma vertex_unit (h3 : 3 ≤ r) (i : Fin r) :
    ∃ v : MvPolynomial (Fin (3*r)) (PowerSeries k), v.IsHomogeneous 1 ∧
      evaluate k b 0 i v = 1 ∧ ∀ n, IsUnit (evaluate k b n i v) := by
  obtain ⟨v, hv, _, hi⟩ := exists_vertex_polynomial k h3 (T.overlap_spec 0) (b 0) (hb.1 0) i
  refine ⟨v, hv, hi, fun n => unit_of_reduce _ n _ ?_⟩
  rw [evaluate_reduce k T a b hb]
  change IsUnit ((MvPolynomial.eval₂Hom _ _) v)
  rw [hi]
  exact isUnit_one

lemma rightWeight_unit (n : ℕ) (i : Fin r) : IsUnit (rightWeight k r n hr a i) := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  have hn : IsNilpotent (LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T (-1)) := by
    refine ⟨n+1, ?_⟩
    rw [mul_pow, ← map_pow, parameter_pow, map_zero, zero_mul]
  have hu : IsUnit (-LaurentPolynomial.C
      (↑((markedUnit k n (a (next r hr (next r hr i))))⁻¹) : R k n)) :=
    (((markedUnit k n (a (next r hr (next r hr i))))⁻¹).isUnit.map LaurentPolynomial.C).neg
  have he : L (rightWeight k r n hr a i) =
      LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T (-1) +
        -LaurentPolynomial.C (↑((markedUnit k n (a (next r hr (next r hr i))))⁻¹) : R k n) := by
    change rx L (coordY k n - base k n _) = _
    rw [map_sub, rx_y hL, rx_base hL, sub_eq_add_neg]
  apply (isUnit_map_iff L _).mp
  rw [he]
  exact hn.isUnit_add_right_of_commute hu (Commute.all _ _)


lemma leftWeight_unit (n : ℕ) (i : Fin r) :
    IsUnit (leftWeight k r n hr (T.overlap n) a i) := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  have hm : IsUnit ((T.overlap n) (restriction k n false (markedEquation k n (a i)))) := by
    apply (isUnit_map_iff L _).mp
    change IsUnit (ry (T.overlap n) L (coordX k n - base k n _))
    rw [map_sub, ry_x (T.overlap_spec n) hL, ry_base (T.overlap_spec n) hL,
      sub_eq_add_neg]
    have hn : IsNilpotent (LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T 1) := by
      refine ⟨n+1, ?_⟩
      rw [mul_pow, ← map_pow, parameter_pow, map_zero, zero_mul]
    exact hn.isUnit_add_right_of_commute
      ((markedUnit k n (a i)).isUnit.map LaurentPolynomial.C).neg (Commute.all _ _)
  have hy : IsUnit ((T.overlap n) (restriction k n false (coordY k n))) := by
    apply (isUnit_map_iff L _).mp
    change IsUnit (ry (T.overlap n) L (coordY k n))
    rw [ry_y (T.overlap_spec n) hL]
    exact LaurentPolynomial.isUnit_T _
  exact ((((markedUnit k n (a (next r hr i)))⁻¹).isUnit.map (base k n)).map
    (restriction k n true)).neg.mul hm |>.mul hy

include hb in
lemma adjacent_maps (h3 : 3 ≤ r) (n : ℕ) (i : Fin r) :
    leftLeg k n (T.overlap n) ≫ chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n) i =
      rightLeg k n ≫ chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n) (next r hr i) := by
  obtain ⟨ur, hur⟩ := rightWeight_unit k a n i
  obtain ⟨ul, hul⟩ := leftWeight_unit k T a n i
  let e : B k n true →+* Γ(specB k n true, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).inv.hom
  let c : Γ(specB k n true, ⊤)ˣ := Units.map e ((ul * ur⁻¹)^3)
  let F := (leftLeg k n (T.overlap n)).appTop.hom.comp (coefficientChartMap k (b n) i)
  let G := (rightLeg k n).appTop.hom.comp (coefficientChartMap k (b n) (next r hr i))
  have hC (z : PowerSeries k) : F (MvPolynomial.C z) = G (MvPolynomial.C z) := by
    change (leftLeg k n (T.overlap n)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C z))) =
      (rightLeg k n).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C z)))
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, leftLeg, rightLeg]
    erw [spec_pullback_value, spec_pullback_value]
    congr 1
    exact RingHom.congr_fun (adjacent_base (T.overlap_spec n)) (trunc _ _ n z)
  have hX (j : Fin (3*r)) : F (MvPolynomial.X j) = G (MvPolynomial.X j) * (c : Γ(specB k n true, ⊤)) := by
    change (leftLeg k n (T.overlap n)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j))) =
      (rightLeg k n).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j))) * _
    simp only [MvPolynomial.eval₂Hom_X', leftLeg, rightLeg]
    erw [spec_pullback_value, spec_pullback_value]
    change e ((T.overlap n) (restriction k n false ((b n j).val i))) =
      e (restriction k n true ((b n j).val (next r hr i))) * e _
    rw [← map_mul]
    congr 1
    have hh := (compatible_iff_normalized_zero k r n hr (T.overlap n)
      (T.overlap_spec n) a 3 (b n j).val).mp (b n j).property i
    change _ * rightWeight k r n hr a i ^ 3 -
      _ * leftWeight k r n hr (T.overlap n) a i ^ 3 = 0 at hh
    rw [← hur, ← hul, sub_eq_zero] at hh
    apply (ur.isUnit.pow 3).mul_right_cancel
    simpa only [Units.val_pow_eq_pow_val, Units.val_mul, mul_pow, mul_assoc,
      ← mul_pow, Units.inv_mul, one_pow, mul_one] using hh
  obtain ⟨v, hv, _, huv⟩ := vertex_unit k T a b hb h3 i
  have hu : IsUnit ((leftLeg k n (T.overlap n)).appTop (coefficientChartMap k (b n) i v)) :=
    ((huv n).map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom).map
      (leftLeg k n (T.overlap n)).appTop.hom
  exact comp_eq_of_homogeneous_scale _ _
    (coefficientChartMap_irrelevant k h3 (T.overlap_spec n) (b n) (hb.1 n) i) v hv _ _
    (coefficientChartMap_irrelevant k h3 (T.overlap_spec n) (b n) (hb.1 n) (next r hr i)) c
    (homogeneous_scale F G c hC hX) hu


include hb in
/-- The maps are glued from the actual numerator evaluations. -/
def stageMorphism (h3 : 3 ≤ r) (n : ℕ) :
    (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r) :=
  (T.atlas n).desc (chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n))
    (adjacent_maps k T a b hb h3 n)

include hb in
lemma stage_realizes (h3 : 3 ≤ r) (n : ℕ) :
    RealizesEmbedding k (T.atlas n) (b n) (stageMorphism k T a b hb h3 n) := by
  intro i
  exact ⟨coefficientChartMap_irrelevant k h3 (T.overlap_spec n) (b n) (hb.1 n) i,
    (T.atlas n).chart_desc _ _ i⟩

include hb in
lemma stage_over (h3 : 3 ≤ r) (n : ℕ) :
    stageMorphism k T a b hb h3 n ≫ projectiveStructure (PowerSeries k) (3*r) =
      (T.atlas n).p ≫ baseInclusion k n := by
  apply (T.atlas n).hom_ext
  intro i
  rw [← Category.assoc, stageMorphism, (T.atlas n).chart_desc,
    chartMorphism_over, ← (T.atlas n).chart_over i, Category.assoc]

include hb in
lemma chart_transition (h3 : 3 ≤ r) (n N : ℕ) (h : n ≤ N) (i : Fin r) :
    chartReduction k n N h ≫ chartMorphism k h3 (T.overlap_spec N) (b N) (hb.1 N) i =
      chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n) i := by
  obtain ⟨v, hv, _, hu⟩ := vertex_unit k T a b hb h3 i
  have he (p) : (chartReduction k n N h).appTop (coefficientChartMap k (b N) i p) =
      (𝟙 (specA k n) : specA k n ⟶ specA k n).appTop (coefficientChartMap k (b n) i p) := by
    change (Spec.map (CommRingCat.ofHom (truncReduce _ _ n N h))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k N))).inv (evaluate k b N i p)) = _
    rw [spec_pullback_value, evaluate_reduce k T a b hb]
    simp only [Scheme.Hom.id_appTop]
    rfl
  have hs : ∀ d p, p.IsHomogeneous d →
      (chartReduction k n N h).appTop (coefficientChartMap k (b N) i p) =
      (𝟙 (specA k n) : specA k n ⟶ specA k n).appTop (coefficientChartMap k (b n) i p) *
        ((1 : Γ(specA k n, ⊤)ˣ) : Γ(specA k n, ⊤))^d := by
    intros; simpa using he _
  have hvu : IsUnit ((chartReduction k n N h).appTop (coefficientChartMap k (b N) i v)) :=
    ((hu N).map (Scheme.ΓSpecIso (CommRingCat.of (A k N))).inv.hom).map
      (chartReduction k n N h).appTop.hom
  simpa only [Category.id_comp, chartMorphism] using
    comp_eq_of_homogeneous_scale (chartReduction k n N h) _
      (coefficientChartMap_irrelevant k h3 (T.overlap_spec N) (b N) (hb.1 N) i)
      v hv (𝟙 (specA k n)) _
      (coefficientChartMap_irrelevant k h3 (T.overlap_spec n) (b n) (hb.1 n) i)
      1 hs hvu

include hb in
lemma stage_transition (h3 : 3 ≤ r) (n N : ℕ) (h : n ≤ N) :
    T.transition n N h ≫ stageMorphism k T a b hb h3 N =
      stageMorphism k T a b hb h3 n := by
  apply (T.atlas n).hom_ext
  intro i
  rw [← Category.assoc, (T.transition_spec n N h).2 i, Category.assoc,
    stageMorphism, (T.atlas N).chart_desc, stageMorphism, (T.atlas n).chart_desc,
    chart_transition k T a b hb]

include hb in
lemma stage_injective (h3 : 3 ≤ r) (n : ℕ) :
    Function.Injective (stageMorphism k T a b hb h3 n) := by
  have he : stageMorphism k T a b hb h3 0 =
      SpecialFiberCubicEmbeddingR0135.globalMorphism k h3 (T.overlap_spec 0)
        (T.atlas 0) (b 0) (hb.1 0) := by
    apply (T.atlas 0).hom_ext
    intro i
    rw [stageMorphism, SpecialFiberCubicEmbeddingR0135.globalMorphism,
      (T.atlas 0).chart_desc]
  have hi : Function.Injective (stageMorphism k T a b hb h3 0) := by
    rw [he]
    exact globalMorphism_injective k h3 (T.overlap_spec 0) (T.atlas 0) (b 0) (hb.1 0)
  have hs := reduction_surjective k r 0 n hr (Nat.zero_le n)
    (T.atlas 0) (T.atlas n) (T.transition 0 n (Nat.zero_le n))
    (T.transition_spec 0 n (Nat.zero_le n))
  intro x y hxy
  obtain ⟨x, rfl⟩ := hs x
  obtain ⟨y, rfl⟩ := hs y
  apply congrArg (T.transition 0 n (Nat.zero_le n))
  apply hi
  simpa only [← Scheme.Hom.comp_apply, stage_transition k T a b hb] using hxy

/-- Surjectivity lifts along the nilpotent parameter when the source contains
its prescribed power-series coefficient. -/
lemma surjective_of_special (n : ℕ)
    (f : MvPolynomial (Fin (3*r)) (PowerSeries k) →+* A k n)
    (f₀ : MvPolynomial (Fin (3*r)) (PowerSeries k) →+* A k 0)
    (hred : ∀ p, truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n) (f p) = f₀ p)
    (hs : Function.Surjective f₀)
    (ht : f (MvPolynomial.C PowerSeries.X) = base k n (parameter k n)) :
    Function.Surjective f := by
  let tM : MvPolynomial (Fin (3*r)) (PowerSeries k) →+ MvPolynomial (Fin (3*r)) (PowerSeries k) :=
    AddMonoidHom.mulLeft (MvPolynomial.C PowerSeries.X)
  let tV : A k n →+ A k n := AddMonoidHom.mulLeft (base k n (parameter k n))
  apply surjective_of_nilpotent_approximation f.toAddMonoidHom tM tV (q := n+1)
  · intro p
    exact (map_mul f _ _).trans (congrArg (fun q => q * f p) ht)
  · intro z
    obtain ⟨p, hp⟩ := hs (truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n) z)
    have hz : truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n) (z-f p) = 0 := by
      rw [map_sub, hred, hp, sub_self]
    obtain ⟨w, hw⟩ := (truncReduce_eq_zero_iff _ 0 n (Nat.zero_le n) (z-f p)).mp hz
    refine ⟨p, w, ?_⟩
    change z = f p + base k n (parameter k n) * w
    rw [node_parameter_power] at hw
    simpa using (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  · intro z
    have he : ∀ j, (tV^[j]) z = base k n (parameter k n)^j * z := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [Function.iterate_succ_apply', ih]
          change base k n (parameter k n) * (_ * z) = _
          rw [pow_succ' (base k n (parameter k n)) j, mul_assoc]
    rw [he, ← map_pow, parameter_pow, map_zero, zero_mul]


include hb in
/-- Normalizing by a lifted vertex gives a surjective affine coordinate map;
the finite geometric-series correction retains all nilpotent directions. -/
lemma stage_chart_surjectiveOnStalks (h3 : 3 ≤ r) (n : ℕ) (i : Fin r) :
    SurjectiveOnStalks (chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n) i) := by
  classical
  obtain ⟨v, hv, hi, hu⟩ := vertex_unit k T a b hb h3 i
  obtain ⟨w, hw⟩ := hu n
  let e : A k n →+* Γ(specA k n, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
  let g : MvPolynomial (Fin (3*r)) (PowerSeries k) →+* A k n :=
    MvPolynomial.eval₂Hom ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
      (fun j => (b n j).val i * (↑w⁻¹ : A k n))
  have hscale : ∀ d p, p.IsHomogeneous d → g p = evaluate k b n i p * (↑w⁻¹ : A k n)^d :=
    homogeneous_scale g (evaluate k b n i) (↑w⁻¹ : A k n)
      (fun z => by simp [g, evaluate]) (fun j => by simp [g, evaluate])
  have hgv : g v = 1 := by
    rw [hscale 1 v hv, pow_one, ← hw, Units.mul_inv]
  have hwinv : truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n) (↑w⁻¹ : A k n) = 1 := by
    have hh := congrArg (truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n)) w.mul_inv
    rw [map_mul, hw, evaluate_reduce k T a b hb, hi, map_one, one_mul] at hh
    exact hh
  have hred (p) : truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n) (g p) =
      evaluate k b 0 i p := by
    have he : (truncReduce _ (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n)).comp g =
        evaluate k b 0 i := by
      apply MvPolynomial.ringHom_ext
      · intro z
        simp only [RingHom.comp_apply, g, evaluate, MvPolynomial.eval₂Hom_C]
        rw [reduce_base]
        rfl
      · intro j
        simp only [RingHom.comp_apply, g, evaluate, MvPolynomial.eval₂Hom_X', map_mul,
          hwinv, mul_one, hb.2 0 n (Nat.zero_le n) j i]
    exact RingHom.congr_fun he p
  have hsur : Function.Surjective g := surjective_of_special k n g (evaluate k b 0 i)
    hred (chart_evaluation_surjective k h3 (T.overlap_spec 0) (b 0) (hb.1 0) i)
    (by simp only [g, MvPolynomial.eval₂Hom_C]; rfl)
  let f := e.comp g
  have hfv : f v = 1 := by change e (g v) = 1; rw [hgv, map_one]
  have hf : Ideal.map f (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k))).toIdeal = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f
      (HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega : 0 < (1 : ℕ)) hv))
    rw [hfv]
    exact isUnit_one
  have hfs : Function.Surjective f :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv).2.comp hsur
  have hsame : Proj.fromOfGlobalSections _ f hf =
      chartMorphism k h3 (T.overlap_spec n) (b n) (hb.1 n) i := by
    have hc : ∀ d p, p.IsHomogeneous d →
        (𝟙 (specA k n) : specA k n ⟶ specA k n).appTop (f p) =
        (𝟙 (specA k n) : specA k n ⟶ specA k n).appTop (coefficientChartMap k (b n) i p) *
          (↑(Units.map e.toMonoidHom w⁻¹) : Γ(specA k n, ⊤))^d := by
      intro d p hp
      simp only [Scheme.Hom.id_appTop, CommRingCat.id_apply]
      change e (g p) = e (evaluate k b n i p) * (e (↑w⁻¹ : A k n))^d
      rw [hscale d p hp, map_mul, map_pow]
    have huv : IsUnit ((𝟙 (specA k n) : specA k n ⟶ specA k n).appTop (f v)) := by
      simpa [hfv] using (isUnit_one : IsUnit (1 : Γ(specA k n, ⊤)))
    simpa only [Category.id_comp, chartMorphism] using comp_eq_of_homogeneous_scale
      (𝟙 (specA k n)) f hf v hv (𝟙 (specA k n)) (coefficientChartMap k (b n) i)
      (coefficientChartMap_irrelevant k h3 (T.overlap_spec n) (b n) (hb.1 n) i)
      (Units.map e.toMonoidHom w⁻¹) hc huv
  letI : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  letI := projectiveChartLift_closed f hf v hv hfv hfs
  rw [← hsame, ← projectiveChartLift_ι f hf v hv hfv]
  infer_instance

include hb in
lemma stage_closed (h3 : 3 ≤ r) (n : ℕ) :
    IsClosedImmersion (stageMorphism k T a b hb h3 n) := by
  haveI : SurjectiveOnStalks (stageMorphism k T a b hb h3 n) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks) (T.atlas n).openCover
    intro i
    change SurjectiveOnStalks ((T.atlas n).chart i ≫ stageMorphism k T a b hb h3 n)
    rw [stageMorphism, (T.atlas n).chart_desc]
    exact stage_chart_surjectiveOnStalks k T a b hb h3 n i
  letI := SurjectiveOnStalks.mono_of_injective (stage_injective k T a b hb h3 n)
  apply (IsClosedImmersion.iff_isProper_and_mono _).mpr
  refine ⟨?_, inferInstance⟩
  letI : IsProper (T.atlas n).p :=
    infinitesimal_polygon_proper k r hr h3 n _ (T.overlap_spec n) (T.atlas n)
  letI : IsClosedImmersion (baseInclusion k n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsProper (stageMorphism k T a b hb h3 n ≫ projectiveStructure (PowerSeries k) (3*r)) := by
    rw [stage_over]
    infer_instance
  haveI : IsSeparated (projectiveStructure (PowerSeries k) (3*r)) := by
    unfold projectiveStructure
    infer_instance
  exact IsProper.of_comp _ (projectiveStructure (PowerSeries k) (3*r))

end ArithmeticThetaProjectiveEffectivityR0135.CompatibleProjectiveEmbeddingsR0135

namespace ArithmeticThetaProjectiveEffectivityR0135
open CategoryTheory AlgebraicGeometry CompatibleProjectiveEmbeddingsR0135

/-- The supplied compatible cubic bases define closed projective embeddings
at every thickness, realizing every prescribed tower transition. -/
theorem compatible_projective_embeddings :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r → ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ) (b : ArithmeticThetaProjectiveEffectivityR0135.CubicBases k r hr T a), ArithmeticThetaProjectiveEffectivityR0135.CompatibleBases k T a b → ∃ j : ∀ n, (T.atlas n).X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace (PowerSeries k) (3*r), ArithmeticThetaProjectiveEffectivityR0135.ProjectiveSystem k T a b j := by
  intro k _ _ r hr h3 T a b hb
  refine ⟨stageMorphism k T a b hb h3, ?_⟩
  constructor
  · intro n
    exact ⟨stage_closed k T a b hb h3 n, stage_realizes k T a b hb h3 n,
      stage_over k T a b hb h3 n⟩
  · exact stage_transition k T a b hb h3

end ArithmeticThetaProjectiveEffectivityR0135

#print axioms ArithmeticThetaProjectiveEffectivityR0135.compatible_projective_embeddings
