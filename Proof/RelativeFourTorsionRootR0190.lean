module

public import GlobalFourTorsionDefinitionsR0190
public import FullLevelDivisorReductionR0177

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaGlobalFourTorsionR0190
namespace RelativeFourTorsionRoot
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)
include hG

lemma coordinates (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) :
    ∃ (e : Fin 3 → R) (x y : R), Labels R W G L M e ∧ SplitCubic R W e ∧
      HasCoordinates R W (quarterPoint R W G L M) x y := by
  have h2 : 2 ∣ L := dvd_trans (by decide) h4
  obtain ⟨N, hNx, hNy⟩ := full_level_divisor_reduction R W G hG L 2 hL (by decide) h2 M
  obtain ⟨e, he⟩ := two_torsion_affine_coordinates R W G hG N
  have hs := two_torsion_split_cubic R W G hG N e he
  have hlabels : Labels R W G L M e := by
    intro i
    simpa only [twoPoint, hNx, hNy, twoLabel] using he i
  have hq : 0 < L / 4 := Nat.div_pos (Nat.le_of_dvd hL h4) (by decide)
  have hqlt : L / 4 < L := Nat.div_lt_self hL (by decide)
  have ha : Disjoint (Set.range (quarterPoint R W G L M)) (Set.range (origin R W)) := by
    simpa only [Fin.val_zero, G.nsmul_zero, G.one_mul, quarterPoint] using
      M.avoids ⟨0, hL⟩ ⟨L/4, hqlt⟩ (Or.inr (Nat.ne_of_gt hq))
  obtain ⟨χ, hχ⟩ := TwoTorsionAffineCoordinates.exists_chart_factorization W _ ha
  exact ⟨e, χ (xOverZ W.toProjective), χ (yOverZ W.toProjective), hlabels, hs,
    (G.nsmul (𝟙 _) (L/4) M.y).property, χ, hχ, rfl, rfl⟩

lemma double_quarter (L : ℕ) (h4 : 4 ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) :
    G.nsmul (𝟙 _) 2 (G.nsmul (𝟙 _) (L/4) M.y) = G.nsmul (𝟙 _) (L/2) M.y := by
  letI := FullLevelCyclicLiftsR0175.sectionGroup G hG
  have hn : L/4*2 = L/2 := by omega
  simp only [FullLevelTorsionSplittingR0175.nsmul_pow, ← pow_mul, hn]

/-- Evaluation uses the given scheme law and the actual chart maps, over every
residue field as well as the fraction field. -/
lemma field_double (F : Type u) [Field F] [DecidableEq F] [Algebra R F]
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hd : G.nsmul (𝟙 _) 2 P = Q) (x y t z : R)
    (hP : HasCoordinates R W P.val x y) (hQ : HasCoordinates R W Q.val t z) :
    let V := (W.toProjective.baseChange F).toAffine
    let f := algebraMap R F
    f y ≠ V.negY (f x) (f y) ∧
      V.addX (f x) (f x) (V.slope (f x) (f x) (f y) (f y)) = f t := by
  classical
  let f := algebraMap R F
  let b := Spec.map (CommRingCat.ofHom f)
  let P' := schemeHomOverComp b (Category.comp_id b) P
  let Q' := schemeHomOverComp b (Category.comp_id b) Q
  obtain ⟨ev, hev, _, hc⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by simpa [origin] using hG.1 (𝟙 (Base R)))
  have hfac (S : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) (a c : R)
      (hS : HasCoordinates R W S.val a c) :
      ∃ h, ev F (schemeHomOverComp b (Category.comp_id b) S) =
        WeierstrassCurve.Affine.Point.some (f a) (f c) h := by
    obtain ⟨_, χ, hχ, hx, hy⟩ := hS
    have hχ' : (schemeHomOverComp b (Category.comp_id b) S).val =
        Spec.map (CommRingCat.ofHom (f.comp χ)) ≫ zChartι W.toProjective := by
      change b ≫ S.val = _
      rw [hχ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    obtain ⟨h, hh⟩ := hc F _ (f.comp χ) hχ'
    simp only [RingHom.comp_apply, hx, hy] at h hh
    exact ⟨h, hh⟩
  obtain ⟨hp, hep⟩ := hfac P x y hP
  obtain ⟨hq, heq⟩ := hfac Q t z hQ
  have hdd : G.mul b P' P' = Q' := by
    have h := G.nsmul_natural (𝟙 _) b b (Category.comp_id b) 2 P
    rw [hd] at h
    simpa only [show 2 = 1+1 from rfl, G.nsmul_succ, G.nsmul_one_apply, G.nsmul_zero, G.one_mul] using h.symm
  have he : WeierstrassCurve.Affine.Point.some (f x) (f y) hp +
      WeierstrassCurve.Affine.Point.some (f x) (f y) hp =
      WeierstrassCurve.Affine.Point.some (f t) (f z) hq := by
    rw [← hep, ← heq, ← hev.1 F P' P', hdd]
  have hn : f y ≠ ((W.toProjective.baseChange F).toAffine).negY (f x) (f y) := by
    intro hn
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hn] at he
    exact WeierstrassCurve.Affine.Point.some_ne_zero hq he.symm
  refine ⟨hn, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn] at he
  exact (WeierstrassCurve.Affine.Point.some.inj he).1

lemma ordinate_unit
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hd : G.nsmul (𝟙 _) 2 P = Q) (x y t z : R)
    (hP : HasCoordinates R W P.val x y) (hQ : HasCoordinates R W Q.val t z) :
    IsUnit (completedY R W x y) := by
  classical
  have hn (F : Type u) [Field F] [Algebra R F] :
      algebraMap R F (completedY R W x y) ≠ 0 := by
    have hh := (field_double W G hG F P Q hd x y t z hP hQ).1
    change algebraMap R F y ≠ -algebraMap R F y -
      algebraMap R F W.a₁ * algebraMap R F x - algebraMap R F W.a₃ at hh
    intro hz
    apply hh
    have hhalf := congrArg (algebraMap R F)
      (TwoTorsionSplitCubicR0177.half_identity (R := R))
    simp only [map_mul, map_ofNat, map_one] at hhalf
    simp only [completedY, map_add, map_mul] at hz
    linear_combination 2 * hz -
      (algebraMap R F W.a₁ * algebraMap R F x + algebraMap R F W.a₃) * hhalf
  by_contra hu
  obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {completedY R W x y}) (fun h => hu (Ideal.span_singleton_eq_top.mp h))
  letI : I.IsMaximal := hI
  letI := Ideal.Quotient.field I
  apply hn (R ⧸ I)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))


omit hG in
lemma completed_duplication {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (V : WeierstrassCurve.Affine F) (r s t x y : F)
    (ha : V.a₂ + V.a₁^2/4 = -(r+s+t))
    (hb : V.a₄ + V.a₁*V.a₃/2 = r*s+r*t+s*t)
    (hc : V.a₆ + V.a₃^2/4 = -(r*s*t))
    (he : V.Equation x y) (hn : y ≠ V.negY x y) :
    V.addX x x (V.slope x x y y) - r =
      (((x-r)^2 - (r-s)*(r-t))/(2*(y+(V.a₁*x+V.a₃)/2)))^2 := by
  let Y := y+(V.a₁*x+V.a₃)/2
  let S := ArithmeticThetaFourTorsion.splitCurve r s t
  have ha' : V.a₂ = -(r+s+t)-V.a₁^2/4 := by linear_combination ha
  have hb' : V.a₄ = r*s+r*t+s*t-V.a₁*V.a₃/2 := by linear_combination hb
  have hc' : V.a₆ = -(r*s*t)-V.a₃^2/4 := by linear_combination hc
  have hy : Y ≠ 0 := by
    intro hz
    apply hn
    change y = -y - V.a₁*x - V.a₃
    dsimp [Y] at hz
    linear_combination 2*hz
  have hnS : Y ≠ S.negY x Y := by
    change Y ≠ -Y - 0*x - 0
    intro h
    apply hy
    linear_combination (1/2 : F)*h
  have hden : y - V.negY x y ≠ 0 := sub_ne_zero.mpr hn
  have hden' : 2*Y ≠ 0 := mul_ne_zero (by norm_num) hy
  have heS : S.Equation x Y := by
    rw [WeierstrassCurve.Affine.equation_iff] at he ⊢
    simp only [S, ArithmeticThetaFourTorsion.splitCurve, zero_mul, add_zero]
    rw [ha', hb', hc'] at he
    dsimp [Y]
    linear_combination he
  have hslope : V.slope x x y y = S.slope x x Y Y - V.a₁/2 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hnS]
    simp only [S, ArithmeticThetaFourTorsion.splitCurve, WeierstrassCurve.Affine.negY,
      zero_mul, sub_zero, sub_neg_eq_add]
    rw [ha', hb']
    have hD : y - (-y - V.a₁*x - V.a₃) = 2*Y := by dsimp [Y]; ring
    rw [hD, ← two_mul Y]
    field_simp
    dsimp [Y]
    ring
  have hX : V.addX x x (V.slope x x y y) = S.addX x x (S.slope x x Y Y) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX, S, ArithmeticThetaFourTorsion.splitCurve,
      zero_mul, add_zero]
    rw [ha']
    ring
  rw [hX]
  exact ArithmeticThetaFourTorsion.duplication_coordinate F r s t x Y heS hy


lemma numerator_square (L : ℕ) (h4 : 4 ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) (e : Fin 3 → R) (x y g : R)
    (he : Labels R W G L M e) (hs : SplitCubic R W e)
    (hp : HasCoordinates R W (quarterPoint R W G L M) x y)
    (hg : 2 * completedY R W x y * g = (x-e 0)^2 - (e 0-e 1)*(e 0-e 2)) :
    g^2 = e 1-e 0 := by
  classical
  let F := FractionRing R
  let f : R →+* F := algebraMap R F
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let P := G.nsmul (𝟙 (Base R)) (L/4) M.y
  let Q := G.nsmul (𝟙 (Base R)) (L/2) M.y
  have hq : HasCoordinates R W Q.val (e 1)
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 1 + W.a₃)) := he 1
  have hd : G.nsmul (𝟙 _) 2 P = Q := double_quarter W G hG L h4 M
  obtain ⟨hn, hx⟩ := field_double W G hG F P Q hd x y _ _ hp hq
  have hne (i j : Fin 3) (hij : i ≠ j) : e i ≠ e j :=
    sub_ne_zero.mp (hs.1 i j hij).ne_zero
  obtain ⟨ha, hb, hc⟩ := TwoTorsionSplitCubicR0177.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
    (e 0) (e 1) (e 2) (hne 0 1 (by decide)) (hne 1 2 (by decide))
    (hne 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))
  have hrat (q : ℚ) : f (algebraMap ℚ R q) = (q : F) :=
    map_ratCast (f.comp (algebraMap ℚ R)) q
  have haF := congrArg f ha
  have hbF := congrArg f hb
  have hcF := congrArg f hc
  simp only [map_add, map_neg, map_mul, map_pow, hrat] at haF hbF hcF
  norm_num at haF hbF hcF
  let V := (W.toProjective.baseChange F).toAffine
  have heq : V.Equation (f x) (f y) := by
    have h := congrArg f ((WeierstrassCurve.Affine.equation_iff ..).mp
      (TwoTorsionSplitCubicR0177.equation hp))
    rw [WeierstrassCurve.Affine.equation_iff]
    change f y ^ 2 + f W.a₁ * f x * f y + f W.a₃ * f y =
      f x ^ 3 + f W.a₂ * f x ^ 2 + f W.a₄ * f x + f W.a₆
    simpa only [map_add, map_mul, map_pow] using h
  have hid := completed_duplication V (f (e 0)) (f (e 1)) (f (e 2)) (f x) (f y)
    (by change f W.a₂ + (f W.a₁)^2/4 = _; linear_combination haF)
    (by change f W.a₄ + f W.a₁*f W.a₃/2 = _; linear_combination hbF)
    (by change f W.a₆ + (f W.a₃)^2/4 = _; linear_combination hcF) heq hn
  rw [hx] at hid
  have hY : f (completedY R W x y) = f y + (V.a₁*f x+V.a₃)/2 := by
    change f (completedY R W x y) = f y + (f W.a₁*f x+f W.a₃)/2
    simp only [completedY, map_add, map_mul, hrat]
    norm_num
    ring
  have hu := ordinate_unit W G hG P Q hd x y _ _ hp hq
  have hden : 2*(f y+(V.a₁*f x+V.a₃)/2) ≠ 0 := by
    rw [← hY]
    exact mul_ne_zero (by norm_num) (hu.map f).ne_zero
  have hgf : f g = ((f x-f (e 0))^2-(f (e 0)-f (e 1))*(f (e 0)-f (e 2))) /
      (2*(f y+(V.a₁*f x+V.a₃)/2)) := by
    apply (eq_div_iff hden).mpr
    have h := congrArg f hg
    simp only [map_mul, map_ofNat, map_pow, map_sub, hY] at h
    linear_combination h
  apply IsFractionRing.injective R F
  change f (g^2) = f (e 1-e 0)
  rw [map_pow, map_sub, hgf]
  exact hid.symm

end RelativeFourTorsionRoot

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open RelativeFourTorsionRoot

/-- The source root exists as a unit on the entire rational relative base,
with coordinates from the actual quarter-level section. -/
theorem relative_four_torsion_root :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : Law R W) (hG : IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L →
      ∀ (M : FullLevel R W G L (𝟙 (Base R))),
      ∃ (e : Fin 3 → R) (x y g : R), RootData R W G L M e x y g := by
  intro R _ _ _ _ _ W _ G hG L hL h4 M
  obtain ⟨e, x, y, he, hs, hp⟩ := coordinates W G hG L hL h4 M
  let P := G.nsmul (𝟙 (Base R)) (L/4) M.y
  let Q := G.nsmul (𝟙 (Base R)) (L/2) M.y
  have hq : HasCoordinates R W Q.val (e 1)
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 1 + W.a₃)) := he 1
  have hd : G.nsmul (𝟙 _) 2 P = Q := double_quarter W G hG L h4 M
  have hu := ordinate_unit W G hG P Q hd x y _ _ hp hq
  have h2 : IsUnit (2 : R) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ R (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  obtain ⟨d, hd⟩ := h2.mul hu
  let n := (x-e 0)^2-(e 0-e 1)*(e 0-e 2)
  let g := (↑(d⁻¹) : R)*n
  have hg : 2*completedY R W x y*g = n := by
    rw [← hd]
    simp [g, ← mul_assoc]
  have hsq : g^2 = e 1-e 0 := numerator_square W G hG L h4 M e x y g he hs hp hg
  have hgu : IsUnit g := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    (hsq.symm ▸ hs.1 1 0 (by decide))
  exact ⟨e, x, y, g, he, hs, hp, hu, hgu, hg, hsq⟩

#print axioms relative_four_torsion_root

end ArithmeticThetaGlobalFourTorsionR0190
