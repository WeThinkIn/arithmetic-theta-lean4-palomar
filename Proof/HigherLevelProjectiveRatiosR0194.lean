module

public import FullLevelProjectiveRatiosR0194
public import CompactifiedLevelForgettingR0179
public import RamifiedLaurentExtensionR0155

@[expose] public section

/-! Pullback of arithmetic projective ratios along full-level reduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaSharpCoverR0194.HigherLevelProjectiveRatiosR0194
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open FullLevelProjectiveRatiosR0194

variable (k : Type) [Field k] [CharZero k]

lemma quotient_positive (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hdiv : 2*m ∣ L) : 0 < L/(2*m) :=
  Nat.div_pos (Nat.le_of_dvd hL hdiv) (Nat.mul_pos (by decide) hm)

/-- The exact full series is the specified substitution, including quotient one. -/
lemma levelUnary_expand (L m : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hdiv : 2*m ∣ L) (ν : Fin m) :
    ArithmeticThetaRamifiedPeriodR0154.baseMap k (L/(2*m))
      (quotient_positive L m hL hm hdiv) (levelUnary k (2*m) m ν) =
        levelUnary k L m ν := by
  rw [levelUnary_minimal k m hm]
  exact PowerSeries.expand_apply _ _ _

lemma levelUnary_denominator_ne_zero (L m : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hdiv : 2*m ∣ L) :
    algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ⟨0, hm⟩) ≠ 0 := by
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension
    k (L/(2*m)) (quotient_positive L m hL hm hdiv)
  rw [← levelUnary_expand k L m hm hL hdiv, ← hell.1]
  exact (map_ne_zero_iff ell ell.injective).mpr (minimal_denominator_ne_zero k m hm)

/-- Fraction-field extension transports the entire normalized ratio. -/
lemma normalized_ratio_expand (L m : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hdiv : 2*m ∣ L) (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k (L/(2*m))
      (quotient_positive L m hL hm hdiv) ell) (ν : Fin m) :
    ell (algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m ν) /
      algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m ⟨0, hm⟩)) =
    algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ν) /
      algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ⟨0, hm⟩) := by
  rw [map_div₀, hell, hell, levelUnary_expand k L m hm hL hdiv,
    levelUnary_expand k L m hm hL hdiv]

/-- Image membership uses precisely the field map induced by the given disk. -/
lemma projectiveRatios_of_field_range (L m : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hdiv : 2*m ∣ L) (D : LevelData k L) (X : Compactification k L D)
    (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X (V.disk (closedPoint k)))
    (hfac : f ≫ inclusion k L D X (V.disk (closedPoint k)) = V.disk)
    (hdom : IsDominant (genericInclusion k ≫ f))
    (θ : (Component k L D X (V.disk (closedPoint k))).functionField →+* LaurentSeries k)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫
      (Component k L D X (V.disk (closedPoint k))).fromSpecStalk
        (genericPoint (Component k L D X (V.disk (closedPoint k)))) =
      genericInclusion k ≫ f)
    (hrange : ∀ ν : Fin m, ∃ r : (Component k L D X (V.disk (closedPoint k))).functionField,
      θ r = algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ν) /
        algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ⟨0, hm⟩)) :
    ProjectiveRatios k L m hm D X V := by
  choose r hr using hrange
  refine ⟨f, hfac, hdom, r, ?_, ?_⟩
  · apply θ.injective
    rw [hr, map_one, div_self (levelUnary_denominator_ne_zero k L m hm hL hdiv)]
  · intro ν
    exact (rationalExpansion_iff k _ (genericInclusion k ≫ f) θ hθ _ _).mpr (hr ν)

#print axioms normalized_ratio_expand
#print axioms projectiveRatios_of_field_range

section RationalPullback
variable {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]

lemma dominant_generic (F : Y ⟶ Z) [IsDominant F] :
    F (genericPoint Y) = genericPoint Z := by
  apply ((genericPoint_spec Z).eq _).symm
  convert (genericPoint_spec Y).image F.continuous using 1
  rw [Set.image_univ, F.denseRange.closure_range]

/-- The pullback homomorphism is constructed from the geometric map on stalks. -/
lemma functionField_pullback (F : Y ⟶ Z) [IsDominant F] :
    ∃ φ : Z.functionField →+* Y.functionField,
      Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (genericPoint Z) =
        Y.fromSpecStalk (genericPoint Y) ≫ F := by
  apply GeometricComponentCuspBoundR0184.generic_field_factor
  rw [Scheme.Hom.comp_apply]
  erw [Scheme.fromSpecStalk_closedPoint]
  exact dominant_generic F

/-- Naturality of field pullback follows from the actual punctured-disk square. -/
lemma functionField_square (F : Y ⟶ Z)
    (φ : Z.functionField →+* Y.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (genericPoint Z) =
      Y.fromSpecStalk (genericPoint Y) ≫ F)
    (f : Puncture k ⟶ Y) (g : Puncture k ⟶ Z)
    (θY : Y.functionField →+* LaurentSeries k)
    (θZ : Z.functionField →+* LaurentSeries k)
    (hY : Spec.map (CommRingCat.ofHom θY) ≫ Y.fromSpecStalk (genericPoint Y) = f)
    (hZ : Spec.map (CommRingCat.ofHom θZ) ≫ Z.fromSpecStalk (genericPoint Z) = g)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hsquare : f ≫ F = Spec.map (CommRingCat.ofHom ell) ≫ g) :
    θY.comp φ = ell.comp θZ := by
  have he : CommRingCat.ofHom (θY.comp φ) = CommRingCat.ofHom (ell.comp θZ) := by
    apply Spec.map_injective
    apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [hφ, ← Category.assoc, hY, hZ]
    exact hsquare
  exact congrArg CommRingCat.Hom.hom he

lemma rationalExpansion_pullback (F : Y ⟶ Z)
    (φ : Z.functionField →+* Y.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (genericPoint Z) =
      Y.fromSpecStalk (genericPoint Y) ≫ F)
    (f : Puncture k ⟶ Y) (g : Puncture k ⟶ Z)
    (θY : Y.functionField →+* LaurentSeries k)
    (θZ : Z.functionField →+* LaurentSeries k)
    (hY : Spec.map (CommRingCat.ofHom θY) ≫ Y.fromSpecStalk (genericPoint Y) = f)
    (hZ : Spec.map (CommRingCat.ofHom θZ) ≫ Z.fromSpecStalk (genericPoint Z) = g)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hsquare : f ≫ F = Spec.map (CommRingCat.ofHom ell) ≫ g)
    (r : Z.functionField) (a : LaurentSeries k) (hr : RationalExpansion k Z g r a) :
    RationalExpansion k Y f (φ r) (ell a) := by
  apply (rationalExpansion_iff k Y f θY hY _ _).mpr
  have h := RingHom.congr_fun
    (functionField_square k F φ hφ f g θY θZ hY hZ ell hsquare) r
  exact h.trans (congrArg ell ((rationalExpansion_iff k Z g θZ hZ r a).mp hr))

end RationalPullback

#print axioms rationalExpansion_pullback

section CanonicalReduction
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

def reducedIndex (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (i : Fin d) : Fin L :=
  ⟨L/d*i.val, by
    have hq := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
    simpa only [Nat.div_mul_cancel hdL] using Nat.mul_lt_mul_of_pos_left i.isLt hq⟩

lemma reduced_primitiveRoot (L d : ℕ) (hL : 0 < L) (hdL : d ∣ L)
    (ζ : k) (hζ : IsPrimitiveRoot ζ L) : IsPrimitiveRoot (ζ^(L/d)) d :=
  IsPrimitiveRoot.pow hL hζ (Nat.div_mul_cancel hdL).symm

lemma reduced_coordinatePoint (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (T : TateLevel k L) (i j : Fin d) :
    coordinatePoint (LaurentSeries k) (TateCurve k L) T.law
      (LevelForgettingMap.reduceMarking hL hd hdL T.marking) i j =
    coordinatePoint (LaurentSeries k) (TateCurve k L) T.law T.marking
      (reducedIndex L d hL hd hdL i) (reducedIndex L d hL hd hdL j) := by
  simp only [coordinatePoint, LevelForgettingMap.reduceMarking, reducedIndex,
    LevelForgettingMap.nsmul_mul]

/-- Reduction retains the actual labels, with exactly the reduced root and exponent. -/
lemma reduced_coordinates (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (T : TateLevel k L) (ζ : k) (hmark : CanonicalMarking k L ζ T)
    (i j : Fin d) (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
    HasCoordinates (LaurentSeries k) (TateCurve k L)
      (coordinatePoint (LaurentSeries k) (TateCurve k L) T.law
        (LevelForgettingMap.reduceMarking hL hd hdL T.marking) i j)
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L (L/d*j.val) ((ζ^(L/d))^i.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L (L/d*j.val) ((ζ^(L/d))^i.val))) := by
  rw [reduced_coordinatePoint]
  have hq := (Nat.div_pos (Nat.le_of_dvd hL hdL) hd).ne'
  simpa only [reducedIndex, pow_mul] using hmark
    (reducedIndex L d hL hd hdL i) (reducedIndex L d hL hd hdL j)
    (hij.imp (Nat.mul_ne_zero hq) (Nat.mul_ne_zero hq))

end CanonicalReduction

section RamifiedCubic
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaRamifiedPeriodR0154

lemma rootSeries_expand (d r : ℕ) (hd : 0 < d) (he : Even d) (hr : 0 < r)
    (j : Fin 3) : baseMap k r hr (rootSeries k d j) = rootSeries k (r*d) j := by
  have hh : r*d/2 = r*(d/2) := Nat.mul_div_assoc r he.two_dvd
  have hd2 : d/2 < d := Nat.div_lt_self hd (by decide)
  have h2 : 0 < d/2 := Nat.div_pos (Nat.le_of_dvd hd he.two_dvd) (by decide)
  have hx0 := (ArithmeticThetaTateBridges.ramified_substitution r d 0 (-1 : k) hr
    ⟨hd, hd, neg_ne_zero.mpr one_ne_zero, by intro _; norm_num⟩).1
  have hx1 := (ArithmeticThetaTateBridges.ramified_substitution r d (d/2) (1 : k) hr
    ⟨hd, hd2, one_ne_zero, fun h => (h2.ne' h).elim⟩).1
  have hxm := (ArithmeticThetaTateBridges.ramified_substitution r d (d/2) (-1 : k) hr
    ⟨hd, hd2, neg_ne_zero.mpr one_ne_zero, fun h => (h2.ne' h).elim⟩).1
  unfold rootSeries
  split_ifs with h0 h1
  · simpa only [baseMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mul_zero] using hx0.symm
  · simpa only [baseMap, hh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx1.symm
  · simpa only [baseMap, hh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hxm.symm

/-- The fixed cubic itself is the base change under the same field substitution. -/
lemma tateCurve_map (d r : ℕ) (hd : 0 < d) (he : Even d) (hr : 0 < r)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell) :
    (TateCurve k d).map ell = TateCurve k (r*d) := by
  have hroot (j : Fin 3) : ell (root k d j) = root k (r*d) j := by
    rw [root, hell, rootSeries_expand k d r hd he hr, root]
  ext <;> simp only [TateCurve, curve, WeierstrassCurve.map, map_zero, map_neg,
    map_add, map_mul, hroot]

end RamifiedCubic

#print axioms reduced_coordinates
#print axioms tateCurve_map

section PointedCoefficientComparison
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

lemma coefficient_comparison (W W' : WeierstrassCurve (LaurentSeries k))
    (ell : LaurentSeries k →+* LaurentSeries k) (hW : W.map ell = W') :
    ∃ c : Curve (LaurentSeries k) W' ⟶ Curve (LaurentSeries k) W,
      IsPullback c (structureMap (LaurentSeries k) W') (structureMap (LaurentSeries k) W)
        (Spec.map (CommRingCat.ofHom ell)) ∧
      origin (LaurentSeries k) W' ≫ c = Spec.map (CommRingCat.ofHom ell) ≫ origin (LaurentSeries k) W ∧
      ∀ (P : Puncture k ⟶ Curve (LaurentSeries k) W) (x y : LaurentSeries k),
        HasCoordinates (LaurentSeries k) W P x y →
        ∀ P' : Puncture k ⟶ Curve (LaurentSeries k) W',
          HasCoordinates (LaurentSeries k) W' P' (ell x) (ell y) →
          P' ≫ c = Spec.map (CommRingCat.ofHom ell) ≫ P := by
  subst W'
  obtain ⟨φ, hφ, hc⟩ := exists_isCoefficientHom W.toProjective ell
  refine ⟨Proj.map φ hφ,
    isPullback_projMap_of_isCoefficientHom W.toProjective ell φ hφ hc,
    OrderedLegendreParameterRigidity.coefficient_origin W ell φ hφ hc, ?_⟩
  intro P x y hP P' hP'
  obtain ⟨Q, hQ, he⟩ := OrderedLegendreParameterRigidity.coefficient_coordinates
    W ell φ hφ hc P x y hP
  rw [TwoTorsionSplitCubicR0177.coordinates_ext hP' hQ]
  exact he

lemma tate_coefficient_comparison (d r : ℕ) (hd : 0 < d) (he : Even d) (hr : 0 < r)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k r hr ell) :
    ∃ c : Curve (LaurentSeries k) (TateCurve k (r*d)) ⟶ Curve (LaurentSeries k) (TateCurve k d),
      IsPullback c (structureMap (LaurentSeries k) (TateCurve k (r*d)))
        (structureMap (LaurentSeries k) (TateCurve k d)) (Spec.map (CommRingCat.ofHom ell)) ∧
      origin (LaurentSeries k) (TateCurve k (r*d)) ≫ c =
        Spec.map (CommRingCat.ofHom ell) ≫ origin (LaurentSeries k) (TateCurve k d) ∧
      ∀ (i : ℕ) (a : k), ArithmeticThetaTateSeries.Admissible d i a →
        ∀ (P : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k d))
          (P' : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k (r*d))),
          HasCoordinates (LaurentSeries k) (TateCurve k d) P
            (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX d i a))
            (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY d i a)) →
          HasCoordinates (LaurentSeries k) (TateCurve k (r*d)) P'
            (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX (r*d) (r*i) a))
            (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY (r*d) (r*i) a)) →
          P' ≫ c = Spec.map (CommRingCat.ofHom ell) ≫ P := by
  obtain ⟨c, hc, ho, hp⟩ := coefficient_comparison k (TateCurve k d) (TateCurve k (r*d)) ell
    (tateCurve_map k d r hd he hr ell hell)
  refine ⟨c, hc, ho, ?_⟩
  intro i a ha P P' hP hP'
  apply hp P _ _ hP P'
  have hs := ArithmeticThetaTateBridges.ramified_substitution r d i a hr ha
  rw [hell, hell]
  simpa only [ArithmeticThetaRamifiedPeriodR0154.baseMap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ← hs.1, ← hs.2] using hP'

end PointedCoefficientComparison

#print axioms tate_coefficient_comparison

section MarkedComparison
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

lemma tate_marked_comparison (d r : ℕ) (hd : 1 < d) (he : Even d) (hr : 0 < r)
    (T : TateLevel k d) (V : TateLevel k (r*d))
    (ζ : k) (hζ : IsPrimitiveRoot ζ (r*d))
    (hT : CanonicalMarking k d (ζ^r) T) (hV : CanonicalMarking k (r*d) ζ V)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k r hr ell) :
    ∃ c : Curve (LaurentSeries k) (TateCurve k (r*d)) ⟶ Curve (LaurentSeries k) (TateCurve k d),
      IsPullback c (structureMap (LaurentSeries k) (TateCurve k (r*d)))
        (structureMap (LaurentSeries k) (TateCurve k d)) (Spec.map (CommRingCat.ofHom ell)) ∧
      origin (LaurentSeries k) (TateCurve k (r*d)) ≫ c =
        Spec.map (CommRingCat.ofHom ell) ≫ origin (LaurentSeries k) (TateCurve k d) ∧
      (V.law.nsmul (𝟙 _) r V.marking.x).val ≫ c =
        Spec.map (CommRingCat.ofHom ell) ≫ T.marking.x.val ∧
      (V.law.nsmul (𝟙 _) r V.marking.y).val ≫ c =
        Spec.map (CommRingCat.ofHom ell) ≫ T.marking.y.val := by
  have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd
  have hrd : 0 < r*d := Nat.mul_pos hr hd0
  have hdiv : d ∣ r*d := dvd_mul_left d r
  have hquot : r*d/d = r := Nat.mul_div_cancel r hd0
  let N := LevelForgettingMap.reduceMarking hrd hd0 hdiv V.marking
  obtain ⟨c, hc, ho, hp⟩ := tate_coefficient_comparison k d r hd0 he hr ell hell
  have hζd : IsPrimitiveRoot (ζ^r) d := IsPrimitiveRoot.pow hrd hζ rfl
  have hζ0 : ζ^r ≠ 0 := (hζd.isUnit hd0.ne').ne_zero
  have hcoords (i j : Fin d) (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
      coordinatePoint (LaurentSeries k) (TateCurve k (r*d)) V.law N i j ≫ c =
        Spec.map (CommRingCat.ofHom ell) ≫
          coordinatePoint (LaurentSeries k) (TateCurve k d) T.law T.marking i j := by
    have ha : ArithmeticThetaTateSeries.Admissible d j.val ((ζ^r)^i.val) := by
      refine ⟨hd0, j.isLt, pow_ne_zero _ hζ0, ?_⟩
      intro hj
      exact hζd.pow_ne_one_of_pos_of_lt (hij.resolve_right (not_not.mpr hj)) i.isLt
    apply hp j.val ((ζ^r)^i.val) ha _ _ (hT i j hij)
    simpa only [hquot] using reduced_coordinates k (r*d) d hrd hd0 hdiv V ζ hV i j hij
  refine ⟨c, hc, ho, ?_, ?_⟩
  · have h := hcoords ⟨1, hd⟩ ⟨0, hd0⟩ (Or.inl Nat.one_ne_zero)
    simpa only [coordinatePoint, N, LevelForgettingMap.reduceMarking, hquot,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, V.law.mul_one, T.law.mul_one] using h
  · have h := hcoords ⟨0, hd0⟩ ⟨1, hd⟩ (Or.inr Nat.one_ne_zero)
    simpa only [coordinatePoint, N, LevelForgettingMap.reduceMarking, hquot,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, V.law.one_mul, T.law.one_mul] using h

end MarkedComparison

#print axioms tate_marked_comparison

section DiskSubstitution
open ArithmeticThetaRamifiedPeriodR0154

lemma laurent_constants (r : ℕ) (hr : 0 < r)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell)
    (a : k) : ell (algebraMap k (LaurentSeries k) a) = algebraMap k (LaurentSeries k) a := by
  change ell (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a)) = _
  rw [hell]
  simp only [baseMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.expand_C]
  rfl

lemma laurent_structure (r : ℕ) (hr : 0 < r)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell) :
    Spec.map (CommRingCat.ofHom ell) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (laurent_constants k r hr ell hell)

lemma disk_structure (r : ℕ) (hr : 0 < r) :
    baseMorphism k r hr ≫ diskStructure k = diskStructure k := by
  unfold baseMorphism diskStructure
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact PowerSeries.expand_C r hr.ne' a

lemma puncture_square (r : ℕ) (hr : 0 < r)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell) :
    Spec.map (CommRingCat.ofHom ell) ≫ genericInclusion k =
      genericInclusion k ≫ baseMorphism k r hr := by
  unfold genericInclusion baseMorphism
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext hell

lemma disk_closedPoint (r : ℕ) (hr : 0 < r) :
    baseMorphism k r hr (closedPoint k) = closedPoint k := by
  letI : IsLocalHom (baseMap k r hr) := ⟨by
    intro a ha
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have h := PowerSeries.isUnit_iff_constantCoeff.mp ha
    simpa only [baseMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      PowerSeries.constantCoeff_expand] using h⟩
  exact Spec_closedPoint

end DiskSubstitution

#print axioms puncture_square
#print axioms disk_closedPoint

section ReductionDisk
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaRamifiedPeriodR0154

lemma reduction_puncture (d r : ℕ) (hd : 1 < d) (he : Even d) (hr : 0 < r)
    (D : LevelData k (r*d)) (E : LevelData k d)
    (V : Test k (r*d) D) (T : Test k d E)
    (ζ : k) (hζ : IsPrimitiveRoot ζ (r*d))
    (hT : CanonicalMarking k d (ζ^r) T.level) (hV : CanonicalMarking k (r*d) ζ V.level)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell)
    (f : OpenBase k (r*d) D ⟶ OpenBase k d E)
    (hf : IsReduction k (r*d) D E f) :
    V.base ≫ f = Spec.map (CommRingCat.ofHom ell) ≫ T.base := by
  have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd
  have hrd : 0 < r*d := Nat.mul_pos hr hd0
  have hdiv : d ∣ r*d := dvd_mul_left d r
  have hquot : r*d/d = r := Nat.mul_div_cancel r hd0
  let N := LevelForgettingMap.reduceMarking hrd hd0 hdiv V.level.marking
  obtain ⟨c, hc, ho, hx, hy⟩ := tate_marked_comparison k d r hd he hr T.level V.level ζ hζ
    hT hV ell hell
  have hx' : N.x.val ≫ c = Spec.map (CommRingCat.ofHom ell) ≫ T.level.marking.x.val := by
    simpa only [N, LevelForgettingMap.reduceMarking, hquot] using hx
  have hy' : N.y.val ≫ c = Spec.map (CommRingCat.ofHom ell) ≫ T.level.marking.y.val := by
    simpa only [N, LevelForgettingMap.reduceMarking, hquot] using hy
  letI := V.level.elliptic
  exact hf.1.2 (LaurentSeries k) (TateCurve k (r*d)) V.level.law V.level.originLaw
    V.level.marking N rfl rfl V.base (Spec.map (CommRingCat.ofHom ell) ≫ T.base)
    V.map (c ≫ T.map) V.classifies
    (LevelForgettingMap.classifies_pullback k E (LaurentSeries k) (LaurentSeries k)
      (TateCurve k d) (TateCurve k (r*d)) T.level.law V.level.law T.level.marking N
      (Spec.map (CommRingCat.ofHom ell)) c hc ho hx' hy'
      (laurent_structure k r hr ell hell) T.base T.map T.classifies)

lemma reduction_disk (d r : ℕ) (hd : 1 < d) (he : Even d) (hr : 0 < r)
    (D : LevelData k (r*d)) (E : LevelData k d)
    (X : Compactification k (r*d) D) (Y : Compactification k d E)
    (V : DiskTest k (r*d) D X) (T : DiskTest k d E Y)
    (ζ : k) (hζ : IsPrimitiveRoot ζ (r*d))
    (hT : CanonicalMarking k d (ζ^r) T.level) (hV : CanonicalMarking k (r*d) ζ V.level)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell)
    (f : OpenBase k (r*d) D ⟶ OpenBase k d E) (hf : IsReduction k (r*d) D E f)
    (F : X.space ⟶ Y.space) (hF : ExtendsReduction k (r*d) D E X Y f F) :
    V.disk ≫ F = baseMorphism k r hr ≫ T.disk := by
  letI := Y.proper
  letI : IsDominant (genericInclusion k) :=
    CompactDiscriminantSectionR0182.specMap_dominant_of_injective _
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
  apply ext_of_isDominant_of_isSeparated Y.projection ?_ (genericInclusion k) ?_
  · rw [Category.assoc, hF.1, V.extends_eq.1, Category.assoc, T.extends_eq.1,
      disk_structure]
  · rw [← Category.assoc, V.extends_eq.2.1, Category.assoc, hF.2.1,
      ← Category.assoc, reduction_puncture k d r hd he hr D E V.toTest T.toTest ζ hζ hT hV ell hell f hf,
      Category.assoc, ← T.extends_eq.2.1, ← Category.assoc, puncture_square k r hr ell hell]
    exact Category.assoc _ _ _

end ReductionDisk

#print axioms reduction_disk

section ComponentTransport
open ArithmeticThetaRamifiedPeriodR0154

lemma component_map (L d : ℕ) (D : LevelData k L) (E : LevelData k d)
    (X : Compactification k L D) (Y : Compactification k d E)
    (F : X.space ⟶ Y.space) (x : X.space) (y : Y.space) (hxy : F x = y) :
    ∃ G : Component k L D X x ⟶ Component k d E Y y,
      G ≫ inclusion k d E Y y = inclusion k L D X x ≫ F := by
  let f := inclusion k L D X x ≫ F
  let U := f ⁻¹ᵁ componentOpen k d E Y y
  have hclosed : IsClosed (U : Set (Component k L D X x)) :=
    (CompactHodgeLatticeExtensionR0182.compactComponent_closed k d E Y y).preimage f.continuous
  have hne : (U : Set (Component k L D X x)).Nonempty := by
    refine ⟨⟨x, mem_irreducibleComponent⟩, ?_⟩
    change F x ∈ componentOpen k d E Y y
    rw [hxy]
    exact mem_irreducibleComponent
  have hU : (U : Set (Component k L D X x)) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, U.isOpen⟩ hne
  have hr : Set.range f ⊆ Set.range (inclusion k d E Y y) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ (U : Set (Component k L D X x)) := by rw [hU]; trivial
    exact hz
  exact ⟨IsOpenImmersion.lift (inclusion k d E Y y) f hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- Pullback of the already proved minimal-level functions through a geometric
disk square. The disk square is established above from both canonical labels. -/
lemma transport_projectiveRatios (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (D : LevelData k (r*(2*m))) (E : LevelData k (2*m))
    (X : Compactification k (r*(2*m)) D) (Y : Compactification k (2*m) E)
    (V : DiskTest k (r*(2*m)) D X) (T : DiskTest k (2*m) E Y)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k r hr ell)
    (F : X.space ⟶ Y.space)
    (hF : V.disk ≫ F = baseMorphism k r hr ≫ T.disk)
    (hR : ProjectiveRatios k (2*m) m hm E Y T) : ProjectiveRatios k (r*(2*m)) m hm D X V := by
  have hm2 : 0 < 2*m := Nat.mul_pos (by decide) hm
  have hL : 0 < r*(2*m) := Nat.mul_pos hr hm2
  have hdiv : 2*m ∣ r*(2*m) := dvd_mul_left _ _
  have hquot : r*(2*m)/(2*m) = r := Nat.mul_div_cancel r hm2
  obtain ⟨f, θY, hfac, hdom, hθY⟩ := component_field_factor k (r*(2*m)) D X V
  obtain ⟨g, θZ, hgfac, hgdom, hθZ⟩ := component_field_factor k (2*m) E Y T
  have hxy : F (V.disk (closedPoint k)) = T.disk (closedPoint k) := by
    have h := congrArg (fun a : Disk k ⟶ Y.space => a (closedPoint k)) hF
    exact h.trans (congrArg T.disk (disk_closedPoint k r hr))
  obtain ⟨G, hG⟩ := component_map k (r*(2*m)) (2*m) D E X Y F
    (V.disk (closedPoint k)) (T.disk (closedPoint k)) hxy
  have hsquare : (genericInclusion k ≫ f) ≫ G =
      Spec.map (CommRingCat.ofHom ell) ≫ (genericInclusion k ≫ g) := by
    apply (cancel_mono (inclusion k (2*m) E Y (T.disk (closedPoint k)))).mp
    simp only [Category.assoc, hG, hgfac]
    rw [← Category.assoc f (inclusion k (r*(2*m)) D X (V.disk (closedPoint k))) F, hfac, hF]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom ell)) (genericInclusion k) T.disk,
      puncture_square k r hr ell hell, Category.assoc]
  letI := hgdom
  letI : IsDominant (Spec.map (CommRingCat.ofHom ell)) :=
    CompactDiscriminantSectionR0182.specMap_dominant_of_injective ell ell.injective
  letI : IsDominant ((genericInclusion k ≫ f) ≫ G) := by rw [hsquare]; infer_instance
  letI : IsDominant G := IsDominant.of_comp (genericInclusion k ≫ f) G
  obtain ⟨φ, hφ⟩ := functionField_pullback G
  have hcomm := functionField_square k G φ hφ (genericInclusion k ≫ f)
    (genericInclusion k ≫ g) θY θZ hθY hθZ ell hsquare
  have hrat := (projectiveRatios_iff_field_range k m hm E Y T g hgfac hgdom θZ hθZ).mp hR
  apply projectiveRatios_of_field_range k (r*(2*m)) m hm hL hdiv D X V f hfac hdom θY hθY
  intro ν
  obtain ⟨a, ha⟩ := hrat ν
  refine ⟨φ a, ?_⟩
  change (θY.comp φ) a = _
  rw [hcomm, RingHom.comp_apply, ha]
  apply normalized_ratio_expand k (r*(2*m)) m hm hL hdiv ell
  simpa only [hquot] using hell

end ComponentTransport

#print axioms transport_projectiveRatios

section Assembly
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaCompatibleLevelR0178

lemma higher_level_mul [IsAlgClosed k] (m r : ℕ) (hm : 0 < m) (he : Even m) (hr : 0 < r)
    (D : LevelData k (r*(2*m))) (X : Compactification k (r*(2*m)) D)
    (V : DiskTest k (r*(2*m)) D X) (ζ : k) (hζ : IsPrimitiveRoot ζ (r*(2*m)))
    (hV : CanonicalMarking k (r*(2*m)) ζ V.level) :
    ProjectiveRatios k (r*(2*m)) m hm D X V := by
  have hm2 : 0 < 2*m := Nat.mul_pos (by decide) hm
  have h3 : 3 ≤ 2*m := by obtain ⟨n, hn⟩ := he; omega
  have he2 : Even (2*m) := even_two.mul_right m
  have hL : 3 ≤ r*(2*m) := h3.trans (Nat.le_mul_of_pos_left _ hr)
  have heL : Even (r*(2*m)) := he2.mul_left r
  have hdiv : 2*m ∣ r*(2*m) := dvd_mul_left _ _
  obtain ⟨atlas⟩ := legendre_level_family_construction k (2*m) h3
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    normal_affine_classifying_construction k (2*m) h3 he2 atlas
  let E : LevelData k (2*m) := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion k (2*m) h3 he2 E
  have hζd : IsPrimitiveRoot (ζ^r) (2*m) := IsPrimitiveRoot.pow (Nat.mul_pos hr hm2) hζ rfl
  obtain ⟨Tlevel, hTlevel⟩ := tate_full_level_marking k (2*m) h3 he2 (ζ^r) hζd
  obtain ⟨b, hb, _⟩ := TateLevelClassifyingParameter.classifying_exists_unique k (2*m) h3 he2 E Tlevel
  obtain ⟨Ttest, hlevel, hbase⟩ := (tate_hodge_comparison_tests k (2*m) h3 he2 E).1 Tlevel b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension k (2*m) h3 he2 E Tlevel Y b hb
  let T : DiskTest k (2*m) E Y :=
    { toTest := Ttest, disk := disk, extends_eq := hbase.symm ▸ hdisk }
  have hT : CanonicalMarking k (2*m) (ζ^r) T.level := by
    change CanonicalMarking k (2*m) (ζ^r) Ttest.level
    rw [hlevel]
    exact hTlevel
  have hR := full_level_projective_ratios k m hm he E Y T (ζ^r) hζd hT
  obtain ⟨f, ⟨hf, F, hF, _⟩, _⟩ := compactified_level_forgetting k (r*(2*m)) hL heL
    (2*m) h3 he2 hdiv D E X Y
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k r hr
  apply transport_projectiveRatios k m r hm hr D E X Y V T ell hell.1 F _ hR
  exact reduction_disk k (2*m) r (by omega) he2 hr D E X Y V T ζ hζ hT hV ell hell.1 f hf F hF

end Assembly

#print axioms higher_level_mul
end ArithmeticThetaSharpCoverR0194.HigherLevelProjectiveRatiosR0194

namespace ArithmeticThetaSharpCoverR0194
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 HigherLevelProjectiveRatiosR0194

/-- Every divisible full level carries the pullbacks of the exact minimal-level
unary ratios, with the complete prescribed expansion on its original Tate disk. -/
theorem higher_level_projective_ratios :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ) (hm : 0 < m),
      0 < L → Even m → 2*m ∣ L →
      ∀ (D : LevelData k L) (X : Compactification k L D),
      ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
      CanonicalMarking k L ζ V.level → ProjectiveRatios k L m hm D X V := by
  intro k _ _ _ L m hm hL he hdiv
  obtain ⟨r, h⟩ := hdiv
  rw [Nat.mul_comm] at h
  subst L
  have hr : 0 < r := Nat.pos_of_mul_pos_right hL
  exact higher_level_mul k m r hm he hr

#print axioms higher_level_projective_ratios
end ArithmeticThetaSharpCoverR0194
