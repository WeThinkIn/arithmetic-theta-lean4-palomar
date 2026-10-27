import ArbitrarySplitFiberBasisR0214
import ArbitraryFourCharacterDefinitionsR0214

/-! The unique normalized Miller phase on an arbitrary rational base.
The ordinate doubling identity is proved on the actual integral universal
chart and pulled back through its actual classifying map. All subsequent
half-point and Miller identities are polynomial identities in the base ring.
Field-valued points are used only for invertibility and pairing comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryGeometricPhase
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeFourCharacterR0211
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArbitraryFourTorsionRoot
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

lemma domain_field_y {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    (U : WeierstrassCurve T) [U.IsElliptic]
    (H : Law T U) (hH : (H.one (𝟙 _)).val = (kwZeroSect T U).val)
    (F : Type u) [Field F] [DecidableEq F] [Algebra T F]
    (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F)))
      (structureMap T U))
    (hd : H.mul _ P P = Q)
    (χ ψ : ChartRing T U →+* F)
    (hχ : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T U)
    (hψ : Q.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion T U) :
    let V := (U.toProjective.baseChange F).toAffine
    let x := χ (xOverZ U.toProjective)
    let y := χ (yOverZ U.toProjective)
    (2*y+V.a₁*x+V.a₃) * (ψ (yOverZ U.toProjective) + y +
      V.a₁ * ψ (xOverZ U.toProjective) + V.a₃) +
      (3*x^2+2*V.a₂*x+V.a₄-V.a₁*y)*(ψ (xOverZ U.toProjective)-x) = 0 := by
  classical
  obtain ⟨ev, hev, _, hc⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists U H hH
  obtain ⟨hp, hep⟩ := hc F P χ hχ
  obtain ⟨hq, heq⟩ := hc F Q ψ hψ
  have he : WeierstrassCurve.Affine.Point.some _ _ hp +
      WeierstrassCurve.Affine.Point.some _ _ hp =
      WeierstrassCurve.Affine.Point.some _ _ hq := by
    rw [← hep, ← heq, ← hev.1 F P P, hd]
  have hn : χ (yOverZ U.toProjective) ≠
      ((U.toProjective.baseChange F).toAffine).negY
        (χ (xOverZ U.toProjective)) (χ (yOverZ U.toProjective)) := by
    intro hn
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hn] at he
    exact WeierstrassCurve.Affine.Point.some_ne_zero hq he.symm
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn] at he
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj he
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, hx] at hy
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn] at hy
  have hd := sub_ne_zero.mpr hn
  simp only [WeierstrassCurve.Affine.negY] at hd hy
  dsimp only
  have hdiv :
      (χ (xOverZ U.toProjective) * (3*χ (xOverZ U.toProjective) +
        2*(U.toProjective.baseChange F).toAffine.a₂) +
        (U.toProjective.baseChange F).toAffine.a₄ -
        (U.toProjective.baseChange F).toAffine.a₁*χ (yOverZ U.toProjective)) *
        (ψ (xOverZ U.toProjective)-χ (xOverZ U.toProjective)) /
        (χ (yOverZ U.toProjective) - (-χ (yOverZ U.toProjective) -
          (U.toProjective.baseChange F).toAffine.a₁*χ (xOverZ U.toProjective) -
          (U.toProjective.baseChange F).toAffine.a₃)) =
        -(ψ (yOverZ U.toProjective)+χ (yOverZ U.toProjective)+
          (U.toProjective.baseChange F).toAffine.a₁*ψ (xOverZ U.toProjective)+
          (U.toProjective.baseChange F).toAffine.a₃) := by
    linear_combination -hy
  have hclear := (div_eq_iff hd).mp hdiv
  linear_combination hclear


lemma integral_y {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    (U : WeierstrassCurve T) [U.IsElliptic] (H : Law T U)
    (hH : (H.one (𝟙 _)).val = (kwZeroSect T U).val)
    {X : Scheme.{u}} [IsIntegral X] (t : X ⟶ Base T)
    (P Q : SchemeHomOver t (structureMap T U)) (hd : H.mul _ P P = Q)
    (p q : X ⟶ Spec (.of (ChartRing T U)))
    (hp : P.val = p ≫ chartInclusion T U) (hq : Q.val = q ≫ chartInclusion T U) :
    let χ := coordPull p
    let ψ := coordPull q
    let x := χ (xOverZ U.toProjective)
    let y := χ (yOverZ U.toProjective)
    let a₁ := χ (algebraMap T _ U.a₁)
    let a₂ := χ (algebraMap T _ U.a₂)
    let a₃ := χ (algebraMap T _ U.a₃)
    let a₄ := χ (algebraMap T _ U.a₄)
    let d := 2*y+a₁*x+a₃
    let n := 3*x^2+2*a₂*x+a₄-a₁*y
    d*(ψ (yOverZ U.toProjective)+y+a₁*ψ (xOverZ U.toProjective)+a₃) +
      n*(ψ (xOverZ U.toProjective)-x) = 0 := by
  classical
  dsimp only
  apply germ_injective_of_isIntegral X (genericPoint X) (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  let F := X.functionField
  let η := X.fromSpecStalk (genericPoint X)
  let f : T →+* F := (Spec.preimage (η ≫ t)).hom
  letI : Algebra T F := f.toAlgebra
  have hη : η ≫ t = Spec.map (CommRingCat.ofHom (algebraMap T F)) := (Spec.map_preimage _).symm
  let PF := schemeHomOverComp η hη P
  let QF := schemeHomOverComp η hη Q
  let χ : ChartRing T U →+* F := (Spec.preimage (η ≫ p)).hom
  let ψ : ChartRing T U →+* F := (Spec.preimage (η ≫ q)).hom
  have hpF : PF.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T U := by
    change η ≫ P.val = _
    rw [hp, ← Category.assoc]
    exact congrArg (· ≫ chartInclusion T U) (Spec.map_preimage _).symm
  have hqF : QF.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion T U := by
    change η ≫ Q.val = _
    rw [hq, ← Category.assoc]
    exact congrArg (· ≫ chartInclusion T U) (Spec.map_preimage _).symm
  have hdF : H.mul _ PF PF = QF := by
    rw [← H.mul_natural _ _ η hη, hd]
  have hc := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.chart_scalars
    U f PF χ hpF
  have h := domain_field_y U H hH F PF QF hdF χ ψ hpF hqF
  dsimp only at h
  have hχ := coordPull_generic p
  have hψ := coordPull_generic q
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_zero]
  have hχv (a) : (X.presheaf.germ ⊤ (genericPoint X) trivial) (coordPull p a) = χ a :=
    (RingHom.congr_fun hχ a).symm
  have hψv (a) : (X.presheaf.germ ⊤ (genericPoint X) trivial) (coordPull q a) = ψ a :=
    (RingHom.congr_fun hψ a).symm
  simp only [hχv, hψv]
  have hcv (a : T) : χ (algebraMap T _ a) = f a := RingHom.congr_fun hc a
  rw [hcv, hcv, hcv, hcv]
  exact h

lemma domain_base_y {T S : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    [CommRing S] (U : WeierstrassCurve T) [U.IsElliptic] (H : Law T U)
    (hH : (H.one (𝟙 _)).val = (kwZeroSect T U).val)
    (c : T →+* S)
    (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom c)) (structureMap T U))
    (hd : H.mul _ P P = Q) (χ ψ : ChartRing T U →+* S)
    (hp : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T U)
    (hq : Q.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion T U) :
    let x := χ (xOverZ U.toProjective)
    let y := χ (yOverZ U.toProjective)
    let d := 2*y+c U.a₁*x+c U.a₃
    let n := 3*x^2+2*c U.a₂*x+c U.a₄-c U.a₁*y
    d*(ψ (yOverZ U.toProjective)+y+c U.a₁*ψ (xOverZ U.toProjective)+c U.a₃) +
      n*(ψ (xOverZ U.toProjective)-x) = 0 := by
  classical
  let A := ChartRing T U
  let X := Spec (CommRingCat.of A)
  let j : X ⟶ Curve T U := chartInclusion T U
  let t := j ≫ structureMap T U
  let P₀ : SchemeHomOver t (structureMap T U) := ⟨j, rfl⟩
  let Q₀ := H.mul t P₀ P₀
  let D : X.Opens := Q₀.val ⁻¹ᵁ j.opensRange
  have hr : Set.range (D.ι ≫ Q₀.val) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact z.property
  let q : D.toScheme ⟶ X := IsOpenImmersion.lift j (D.ι ≫ Q₀.val) hr
  have hq₀ : q ≫ j = D.ι ≫ Q₀.val := IsOpenImmersion.lift_fac j _ hr
  let PD := schemeHomOverComp D.ι rfl P₀
  let QD := schemeHomOverComp D.ι rfl Q₀
  have hdD : H.mul _ PD PD = QD := (H.mul_natural _ _ D.ι rfl P₀ P₀).symm
  have hi :
      let χD := coordPull D.ι
      let ψD := coordPull q
      let x := χD (xOverZ U.toProjective)
      let y := χD (yOverZ U.toProjective)
      let a₁ := χD (algebraMap T _ U.a₁)
      let a₂ := χD (algebraMap T _ U.a₂)
      let a₃ := χD (algebraMap T _ U.a₃)
      let a₄ := χD (algebraMap T _ U.a₄)
      let d := 2*y+a₁*x+a₃
      let n := 3*x^2+2*a₂*x+a₄-a₁*y
      d*(ψD (yOverZ U.toProjective)+y+a₁*ψD (xOverZ U.toProjective)+a₃) +
        n*(ψD (xOverZ U.toProjective)-x) = 0 := by
    cases isEmpty_or_nonempty D with
    | inl h => exact Subsingleton.elim _ _
    | inr h =>
      letI : IsDomain A := isDomain_chart_of_isElliptic U 2
      letI : IsIntegral D := isIntegral_of_isOpenImmersion D.ι
      exact integral_y U H hH _ PD QD hdD D.ι q rfl hq₀.symm
  let b := Spec.map (CommRingCat.ofHom χ)
  have hb : b ≫ t = Spec.map (CommRingCat.ofHom c) := by
    change (b ≫ j) ≫ structureMap T U = _
    rw [← hp]
    exact P.property
  have hP : schemeHomOverComp b hb P₀ = P := Subtype.ext hp.symm
  have hQ : b ≫ Q₀.val = Q.val := by
    have h := H.mul_natural t _ b hb P₀ P₀
    rw [hP, hd] at h
    exact congrArg Subtype.val h
  have hrb : Set.range b ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change Q₀.val (b z) ∈ j.opensRange
    rw [← Scheme.Hom.comp_apply, hQ, hq]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)) z, rfl⟩
  let k : Base S ⟶ D.toScheme := IsOpenImmersion.lift D.ι b hrb
  have hk : k ≫ D.ι = b := IsOpenImmersion.lift_fac _ _ hrb
  have hkq : k ≫ q = Spec.map (CommRingCat.ofHom ψ) := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hq₀, ← Category.assoc, hk, hQ, hq]
  let ev : Γ(D, ⊤) →+* S := (Scheme.ΓSpecIso (.of S)).hom.hom.comp k.appTop.hom
  have heχ : ev.comp (coordPull D.ι) = χ := by
    rw [show ev.comp (coordPull D.ι) =
      (Scheme.ΓSpecIso (.of S)).hom.hom.comp (coordPull (k ≫ D.ι)) from
        congrArg ((Scheme.ΓSpecIso (.of S)).hom.hom.comp ·) (coordPull_comp D.ι k).symm,
      hk]
    exact coordPull_spec χ
  have heψ : ev.comp (coordPull q) = ψ := by
    rw [show ev.comp (coordPull q) =
      (Scheme.ΓSpecIso (.of S)).hom.hom.comp (coordPull (k ≫ q)) from
        congrArg ((Scheme.ΓSpecIso (.of S)).hom.hom.comp ·) (coordPull_comp q k).symm,
      hkq]
    exact coordPull_spec ψ
  have hc := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.chart_scalars U c P χ hp
  have hcv (a : T) : χ (algebraMap T _ a) = c a := RingHom.congr_fun hc a
  have hh := congrArg ev hi
  dsimp only at hh ⊢
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_zero] at hh
  have heχv (a) : ev (coordPull D.ι a) = χ a := RingHom.congr_fun heχ a
  have heψv (a) : ev (coordPull q a) = ψ a := RingHom.congr_fun heψ a
  simp only [heχv, heψv] at hh
  simp only [A, hcv] at hh
  exact hh

variable {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
  [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
include hG

lemma raw_y
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hd : G.nsmul (𝟙 _) 2 P = Q) (x y t z : R)
    (hp : HasCoordinates R W P.val x y) (hq : HasCoordinates R W Q.val t z) :
    let d := 2*y+W.a₁*x+W.a₃
    let n := 3*x^2+2*W.a₂*x+W.a₄-W.a₁*y
    d*(z+y+W.a₁*t+W.a₃)+n*(t-x) = 0 := by
  obtain ⟨c, hc⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_universal_map W
  subst W
  let U := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.SmoothUniversalCurve.{u}
  obtain ⟨H, hH⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_origin_law U
  have hmul : G.mul (𝟙 _) P P = Q := by
    simpa only [show 2 = 1+1 from rfl, G.nsmul_succ, G.nsmul_one_apply,
      G.nsmul_zero, G.one_mul] using hd
  obtain ⟨P', Q', χ, ψ, hdouble, hχ, hψ, hx, hy, ht, hz⟩ :=
    transport_double U H (fun s => hH s) c G hG P Q hmul x y t z hp hq
  have h := domain_base_y U H (by simpa using hH (𝟙 _)) c P' Q' hdouble χ ψ hχ hψ
  dsimp only at h
  rw [hx, hy, ht, hz] at h
  exact h


omit hG in
lemma coordinate_unique {P : Base R ⟶ ArithmeticThetaRelativeKatoR0169.Curve R W}
    {a b c d : R} (h : HasCoordinates R W P a b) (h' : HasCoordinates R W P c d) :
    a = c ∧ b = d := by
  exact ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    W.toProjective).2 ⟨P, h.1⟩ ⟨P, h'.1⟩ a b c d
      (TwoTorsionSplitCubicR0177.sectionThrough h)
      (TwoTorsionSplitCubicR0177.sectionThrough h')).mp rfl

omit hG in
lemma coordinates_unique (M : FullLevel R W G 4 (𝟙 (Base R)))
    {e e' : Fin 3 → R} {x y x' y' : Fin 2 → R}
    (h : Coordinates R W G M e x y) (h' : Coordinates R W G M e' x' y') :
    e = e' ∧ x = x' ∧ y = y' := by
  refine ⟨funext (fun i => (coordinate_unique W (h.1 i) (h'.1 i)).1), ?_, ?_⟩
  · funext i
    fin_cases i
    · exact (coordinate_unique W h.2.2.1 h'.2.2.1).1
    · exact (coordinate_unique W h.2.2.2 h'.2.2.2).1
  · funext i
    fin_cases i
    · exact (coordinate_unique W h.2.2.1 h'.2.2.1).2
    · exact (coordinate_unique W h.2.2.2 h'.2.2.2).2

omit hG in
lemma coefficient_identities (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y) :
    4*W.a₂+W.a₁^2 = -4*(e 0+e 1+e 2) ∧
    2*W.a₄+W.a₁*W.a₃ = 2*(e 0*e 1+e 0*e 2+e 1*e 2) ∧
    4*W.a₆+W.a₃^2 = -4*(e 0*e 1*e 2) := by
  obtain ⟨ha, hb, hc⟩ := ArbitrarySplitFiberBasis.coefficients W G M hC.1 hC.2.1
  have hhalf := TwoTorsionSplitCubicR0177.half_identity (R := R)
  have hquarter : 4*algebraMap ℚ R (1/4) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (4:ℚ)*(1/4)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  refine ⟨?_, ?_, ?_⟩
  · linear_combination 4*ha-W.a₁^2*hquarter
  · linear_combination 2*hb-W.a₁*W.a₃*hhalf
  · linear_combination 4*hc-W.a₃^2*hquarter

omit hG in
lemma completed_equation (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (i : Fin 2) :
    (completedY R W (x i) (y i))^2 = (x i-e 0)*(x i-e 1)*(x i-e 2) := by
  have hp : HasCoordinates R W (![M.x, M.y] i).val (x i) (y i) := by
    fin_cases i
    · exact hC.2.2.1
    · exact hC.2.2.2
  have he := (WeierstrassCurve.Affine.equation_iff ..).mp
    (TwoTorsionSplitCubicR0177.equation hp)
  obtain ⟨ha, hb, hc⟩ := coefficient_identities W G M e x y hC
  have hh := TwoTorsionSplitCubicR0177.half_identity (R := R)
  have h4 : IsUnit (4:R) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap ℚ R (1/4), ?_⟩
    have h := congrArg (algebraMap ℚ R) (show (4:ℚ)*(1/4)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  apply h4.mul_left_cancel
  dsimp [completedY]
  linear_combination 4*he+(x i)^2*ha+2*x i*hb+hc +
    (W.a₁*x i+W.a₃)*(4*y i+(2*algebraMap ℚ R (1/2)+1)*(W.a₁*x i+W.a₃))*hh

lemma ordinate_unit (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (i : Fin 2) : IsUnit (completedY R W (x i) (y i)) := by
  let P := ![M.x, M.y] i
  let Q := G.nsmul (𝟙 (Base R)) 2 P
  have hp : HasCoordinates R W P.val (x i) (y i) := by
    fin_cases i
    · exact hC.2.2.1
    · exact hC.2.2.2
  have hq : HasCoordinates R W Q.val (e i.castSucc)
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i.castSucc + W.a₃)) := by
    fin_cases i
    · exact hC.1 0
    · exact hC.1 1
  exact ArbitraryFourTorsionRoot.ordinate_unit W G hG P Q rfl _ _ _ _ hp hq

omit hG in
lemma unit_factor {A : Type u} [CommRing A] {a b : A} (h : IsUnit (a*b)) : IsUnit a := by
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp h
  exact isUnit_iff_exists_inv.mpr ⟨b*c, by simpa only [← mul_assoc] using hc⟩

lemma difference_unit (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (i : Fin 2) (j : Fin 3) : IsUnit (x i-e j) := by
  have h := (ordinate_unit W G hG M e x y hC i).pow 2
  rw [completed_equation W G M e x y hC i] at h
  fin_cases j
  · exact unit_factor (unit_factor h)
  · exact unit_factor (a := x i-e 1) (b := x i-e 0)
      (by simpa only [mul_comm] using unit_factor h)
  · exact unit_factor (a := x i-e 2) (b := (x i-e 0)*(x i-e 1))
      (by simpa only [mul_comm] using h)

omit hG in
/-- Polynomial elimination of the ordinate doubling law, without reducedness. -/
lemma half_polynomial {A : Type u} [CommRing A]
    (a₁ a₂ a₃ a₄ a₆ r s t x y z : A)
    (ha : 4*a₂+a₁^2 = -4*(r+s+t))
    (hb : 2*a₄+a₁*a₃ = 2*(r*s+r*t+s*t))
    (hc : 4*a₆+a₃^2 = -4*(r*s*t))
    (he : y^2+a₁*x*y+a₃*y = x^3+a₂*x^2+a₄*x+a₆)
    (hz : 2*z+a₁*r+a₃ = 0)
    (hd : (2*y+a₁*x+a₃)*(z+y+a₁*r+a₃) +
      (3*x^2+2*a₂*x+a₄-a₁*y)*(r-x) = 0) :
    2*(x-r)*((x-r)^2-(r-s)*(r-t)) = 0 := by
  let d := 2*y+a₁*x+a₃
  let n := 3*x^2+2*a₂*x+a₄-a₁*y
  let m := 3*x^2-2*(r+s+t)*x+(r*s+r*t+s*t)
  have hm : 2*m = 2*n+a₁*d := by
    dsimp [m, n, d]
    linear_combination -x*ha-hb
  have he' : d^2 = 4*(x-r)*(x-s)*(x-t) := by
    dsimp [d]
    linear_combination 4*he+x^2*ha+2*x*hb+hc
  have hd' : d*(z+y+a₁*r+a₃)+n*(r-x) = 0 := hd
  have hh : d^2+2*m*(r-x) = 0 := by
    dsimp [d] at *
    linear_combination 2*hd'-(2*y+a₁*x+a₃)*hz+(r-x)*hm
  dsimp [m] at hh
  linear_combination he'-hh

lemma half_relation (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y) :
    (x 0-e 0)^2 = (e 0-e 1)*(e 0-e 2) ∧
    (x 1-e 0)^2+2*(e 0-e 1)*(x 1-e 0)+(e 0-e 1)*(e 0-e 2) = 0 := by
  obtain ⟨ha, hb, hc⟩ := coefficient_identities W G M e x y hC
  have hh := TwoTorsionSplitCubicR0177.half_identity (R := R)
  have h2 : IsUnit (2:R) := isUnit_iff_exists_inv.mpr ⟨_, hh⟩
  have hp (i : Fin 2) :
      HasCoordinates R W (![M.x, M.y] i).val (x i) (y i) := by
    fin_cases i
    · exact hC.2.2.1
    · exact hC.2.2.2
  have hq (i : Fin 2) : HasCoordinates R W
      (G.nsmul (𝟙 (Base R)) 2 (![M.x, M.y] i)).val (e i.castSucc)
      (-(algebraMap ℚ R (1/2)) * (W.a₁*e i.castSucc+W.a₃)) := by
    fin_cases i
    · exact hC.1 0
    · exact hC.1 1
  have he (i : Fin 2) := (WeierstrassCurve.Affine.equation_iff ..).mp
    (TwoTorsionSplitCubicR0177.equation (hp i))
  have hd (i : Fin 2) := raw_y W G hG _ _ rfl _ _ _ _ (hp i) (hq i)
  have hz (i : Fin 3) :
      2*(-(algebraMap ℚ R (1/2))*(W.a₁*e i+W.a₃))+W.a₁*e i+W.a₃ = 0 := by
    linear_combination -(W.a₁*e i+W.a₃)*hh
  have h0 := half_polynomial W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (e 0) (e 1) (e 2)
    (x 0) (y 0) _ ha hb hc (he 0) (hz 0) (hd 0)
  have h1 := half_polynomial W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (e 1) (e 0) (e 2)
    (x 1) (y 1) _ (by linear_combination ha) (by linear_combination hb)
    (by linear_combination hc) (he 1) (hz 1) (hd 1)
  have h0' : (x 0-e 0)^2-(e 0-e 1)*(e 0-e 2) = 0 :=
    (h2.mul (difference_unit W G hG M e x y hC 0 0)).mul_left_cancel (by simpa using h0)
  have h1' : (x 1-e 1)^2-(e 1-e 0)*(e 1-e 2) = 0 :=
    (h2.mul (difference_unit W G hG M e x y hC 1 1)).mul_left_cancel (by simpa using h1)
  constructor
  · linear_combination h0'
  · linear_combination h1'

omit hG in
/-- A polynomial certificate for the cleared Miller ratio, valid in every
commutative ring. The hypotheses will be supplied by the actual half sections. -/
lemma miller_polynomial {A : Type u} [CommRing A] (a b u v p q : A)
    (hv : v^2 = a*b) (hu : u^2+2*a*u+a*b = 0)
    (hp : p^2 = v*(v+a)*(v+b)) (hq : q^2 = u*(u+a)*(u+b)) :
    (q*v-p*u)^2*(u+a)^2*(v+a)*(v+b)*q =
      v^2*u*(p*(u+a)-q*(v+a))^2*(u+b)*p := by
  linear_combination
    (-u*(a + u)*(-a^2*b*q*u - a^2*q*u*v + a*b*p*v^2 - a*b*q*u^2 - a*b*q*u*v - 2*a*b*q*v^2 + a*p*u*v^2 -
      a*q*u^2*v - 3*a*q*u*v^2 + b*p*u*v^2 - b*q*u^2*v - 2*b*q*v^3 + p*u^2*v^2 - q*u^2*v^2 - 2*q*u*v^3)) * hp +
    (-v*(a + v)*(2*a^2*b*p*u - a^2*b*q*v + 2*a^2*p*u*v - a^2*q*v^2 + 4*a*b*p*u^2 + a*b*p*u*v - 2*a*b*q*u*v +
      5*a*p*u^2*v - 2*a*q*u*v^2 + 2*b*p*u^3 + b*p*u*v^2 - b*q*u^2*v + 2*p*u^3*v + p*u^2*v^2 - q*u^2*v^2)) * hq
      +
    (-v*(a + v)*(4*a^4*b*p - 8*a^3*b^2*p - a^3*b^2*q - 2*a^3*b*p*u - a^3*b*p*v - a^3*b*q*v - 4*a^3*p*v^2 +
      4*a^2*b^3*p + a^2*b^3*q + 4*a^2*b^2*p*u + a^2*b^2*p*v - a^2*b^2*q*v + 2*a^2*b*p*u^2 + a^2*b*p*u*v +
      8*a^2*b*p*v^2 - a^2*b*q*u*v - a^2*b*q*v^2 + a^2*p*u^2*v + 2*a^2*p*u*v^2 + a^2*p*v^3 - a^2*q*u*v^2 +
      a^2*q*v^3 - 2*a*b^3*p*u + 2*a*b^3*q*v - a*b^2*p*u*v - 4*a*b^2*p*v^2 - a*b^2*q*u^2 + a*b^2*q*v^2 +
      2*a*b*p*u^3 + 2*a*b*p*u^2*v - 3*a*b*p*u*v^2 - a*b*p*v^3 - 3*a*b*q*u^2*v - 2*a*b*q*u*v^2 + a*b*q*v^3 +
      3*a*p*u^3*v - a*p*u^2*v^2 - 2*a*q*u^2*v^2 - 2*a*q*u*v^3 + 2*a*q*v^4 + 2*b^2*p*u^3 + 2*b^2*p*u*v^2 -
      2*b^2*q*u^2*v - 2*b^2*q*v^3 + 2*b*p*u^4 + 2*b*p*u^3*v + 3*b*p*u^2*v^2 + b*p*u*v^3 - b*q*u^3*v -
      3*b*q*u^2*v^2 - 2*b*q*u*v^3 - 2*b*q*v^4 + 2*p*u^4*v + p*u^3*v^2 + p*u^2*v^3 - q*u^3*v^2 - q*u^2*v^3 -
      2*q*u*v^4)) * hu +
    (a*v*(a - b)*(a + v)*(-4*a^2*b*p - 8*a^2*p*u + 4*a*b^2*p + a*b^2*q + 10*a*b*p*u + a*b*p*v + 2*a*b*q*u +
      a*b*q*v + 2*a*p*u*v + 2*a*q*u*v - 2*b^2*p*u + 2*b^2*q*v - b*p*u*v + 4*b*q*u*v + 2*b*q*v^2 + 4*q*u*v^2))
      * hv

omit hG in
lemma scalar_square {A : Type u} [CommRing A] (a b u v p q : A)
    (hv : v^2 = a*b) (hu : u^2+2*a*u+a*b = 0)
    (hp : p^2 = v*(v+a)*(v+b)) (hq : q^2 = u*(u+a)*(u+b)) :
    ((u+b)*p)^2+((v+b)*q)^2 = 0 := by
  linear_combination
    (u+b)^2*hp+(v+b)^2*hq+
    (u+b)*(v+b)*(u+b)*hv+(u+b)*(v+b)*(v+b)*hu


open RelativeGeometricPhase ArithmeticThetaMillerR0114

lemma ring_identities (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y) :
    let Y := fun i => completedY R W (x i) (y i)
    numerator e x Y * ((x 0-e 2)*Y 1) = denominator e x Y * ((x 1-e 2)*Y 0) ∧
      (((x 1-e 2)*Y 0)^2+((x 0-e 2)*Y 1)^2 = 0) := by
  let a := e 0-e 1
  let b := e 0-e 2
  let u := x 1-e 0
  let v := x 0-e 0
  let Y := fun i => completedY R W (x i) (y i)
  obtain ⟨hv, hu⟩ := half_relation W G hG M e x y hC
  have hp : (Y 0)^2 = v*(v+a)*(v+b) := by
    calc
      _ = (x 0-e 0)*(x 0-e 1)*(x 0-e 2) := completed_equation W G M e x y hC 0
      _ = _ := by dsimp [v,a,b]; ring
  have hq : (Y 1)^2 = u*(u+a)*(u+b) := by
    calc
      _ = (x 1-e 0)*(x 1-e 1)*(x 1-e 2) := completed_equation W G M e x y hC 1
      _ = _ := by dsimp [u,a,b]; ring
  have hm := miller_polynomial a b u v (Y 0) (Y 1) hv hu hp hq
  have hs := scalar_square a b u v (Y 0) (Y 1) hv hu hp hq
  constructor
  · convert hm using 1 <;> dsimp [numerator, denominator, tangentNumerator, a,b,u,v,Y] <;> ring
  · convert hs using 1 <;> dsimp [a,b,u,v,Y] <;> ring

lemma square_of_formula (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (z : R)
    (hden : IsUnit (denominator e x (fun i => completedY R W (x i) (y i))))
    (hz : denominator e x (fun i => completedY R W (x i) (y i))*z =
      numerator e x (fun i => completedY R W (x i) (y i))) : z^2 = -1 := by
  let Y := fun i => completedY R W (x i) (y i)
  let T := (x 0-e 2)*Y 1
  let S := (x 1-e 2)*Y 0
  have hT : IsUnit T := (difference_unit W G hG M e x y hC 0 2).mul
    (ordinate_unit W G hG M e x y hC 1)
  obtain ⟨hm, hs⟩ := ring_identities W G hG M e x y hC
  have he : z*T = S := by
    apply hden.mul_left_cancel
    calc
      denominator e x Y*(z*T) = (denominator e x Y*z)*T := by ring
      _ = numerator e x Y*T := by rw [hz]
      _ = denominator e x Y*S := hm
  have hs' : S^2+T^2 = 0 := hs
  have hz' : z^2+1 = 0 := by
    apply (hT.pow 2).mul_left_cancel
    change T^2*(z^2+1) = T^2*0
    linear_combination (z*T+S)*he+hs'
  linear_combination hz'

lemma pairing_formula (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F)
    (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e))
    (hb : FiberCoordinates R W e x y F ι b)
    (D : ArithmeticThetaGeometricPairingR0118.LocalData F (ι ∘ e)) :
    let Y := fun i => completedY R W (x i) (y i)
    ι (denominator e x Y) ≠ 0 ∧
    ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1) =
      ι (numerator e x Y) / ι (denominator e x Y) := by
  let Y := fun i => completedY R W (x i) (y i)
  obtain ⟨he, _, hbas⟩ := (arbitrary_split_fiber_basis R W G hG M).2 e x y hC F ι
  obtain ⟨hB, hl⟩ := hbas b hb
  have hh := ArbitrarySplitFiberBasis.fiber_half W G hG M e x y hC F ι
  have hhalf (i : Fin 2) : IsHalf F (ι ∘ e) i.castSucc (ι (x i)) (ι (Y i)) := by
    obtain ⟨h, hp, hd⟩ := hh i
    exact ⟨h, hp, hd⟩
  have hf := field_formula (ι ∘ e) (ι ∘ x) (ι ∘ Y) he (hhalf 0) (hhalf 1)
  rw [← map_denominator, ← map_numerator] at hf
  refine ⟨hf.1, ?_⟩
  rw [ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F (ι ∘ e) he D b hB]
  have hp : ArithmeticThetaMarkingR0115.phase F (ι ∘ e) b =
      millerRatio F (ι ∘ e) (ι (x 0)) (ι (Y 0)) (ι (x 1)) (ι (Y 1)) := by
    simp only [ArithmeticThetaMarkingR0115.phase, ArithmeticThetaMarkingR0115.tangent,
      hl, (hb 0).2.1, (hb 0).2.2, (hb 1).2.1, (hb 1).2.2,
      millerRatio, millerValue, Function.comp_apply, Y]
  exact hp.trans hf.2

lemma denominator_unit (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y) :
    IsUnit (denominator e x (fun i => completedY R W (x i) (y i))) := by
  classical
  let Y := fun i => completedY R W (x i) (y i)
  by_contra hu
  obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {denominator e x Y}) (fun h => hu (Ideal.span_singleton_eq_top.mp h))
  letI : I.IsMaximal := hI
  letI := Ideal.Quotient.field I
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  letI : Algebra ℚ (R ⧸ I) := (f.comp (algebraMap ℚ R)).toAlgebra
  letI : CharZero (R ⧸ I) := charZero_of_injective_algebraMap (algebraMap ℚ (R ⧸ I)).injective
  obtain ⟨he, ⟨b, hb, _⟩, _⟩ := (arbitrary_split_fiber_basis R W G hG M).2 e x y hC (R ⧸ I) f
  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character (R ⧸ I) (f ∘ e) he
  apply (pairing_formula W G hG M e x y hC (R ⧸ I) f b hb D).1
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))

lemma phase_exists_unique (M : FullLevel R W G 4 (𝟙 (Base R))) :
    ∃! z : R, MillerPhase R W G M z := by
  obtain ⟨e, x, y, hC⟩ := (arbitrary_split_fiber_basis R W G hG M).1
  let Y := fun i => completedY R W (x i) (y i)
  have hu := denominator_unit W G hG M e x y hC
  obtain ⟨d, hd⟩ := denominator_unit W G hG M e x y hC
  let z := (↑(d⁻¹) : R)*numerator e x Y
  have hz : denominator e x Y*z = numerator e x Y := by
    rw [← hd]
    simp [z, ← mul_assoc]
  refine ⟨z, ⟨⟨e,x,y,hC⟩, ?_⟩, ?_⟩
  · intro e' x' y' hC'
    obtain ⟨rfl,rfl,rfl⟩ := coordinates_unique W G M hC hC'
    exact ⟨hu,hz⟩
  · intro z' hz'
    apply hu.mul_left_cancel
    exact (hz'.2 e x y hC).2.trans hz.symm

lemma phase_geometric (M : FullLevel R W G 4 (𝟙 (Base R)))
    (z : R) (hz : MillerPhase R W G M z) : GeometricPhase R W G M z := by
  refine ⟨hz.1, ?_⟩
  intro e x y hC F _ _ _ f b hb D
  obtain ⟨hd, hp⟩ := pairing_formula W G hG M e x y hC F f b hb D
  rw [hp]
  apply (eq_div_iff hd).mpr
  have hh := congrArg f (hz.2 e x y hC).2
  simpa only [map_mul, mul_comm] using hh

end ArbitraryGeometricPhase

/-- The regular normalized Miller phase exists uniquely over every rational ring.
Its square identity is proved in that ring, and primitivity is restricted to
nontrivial rings. -/
theorem arbitrary_geometric_phase :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∃! z : R, ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z) ∧ (∀ z : R, ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z → ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z ∧ IsUnit z ∧ z^2 = -1 ∧ (Nontrivial R → IsPrimitiveRoot z 4)) := by
  intro R _ _ W _ G hG M
  refine ⟨ArbitraryGeometricPhase.phase_exists_unique W G hG M, ?_⟩
  intro z hz
  obtain ⟨e,x,y,hC⟩ := hz.1
  have hs := ArbitraryGeometricPhase.square_of_formula W G hG M e x y hC z
    (hz.2 e x y hC).1 (hz.2 e x y hC).2
  have hu : IsUnit z := isUnit_iff_exists_inv.mpr ⟨-z, by
    calc
      z*(-z) = -(z^2) := by ring
      _ = 1 := by rw [hs]; ring⟩
  refine ⟨ArbitraryGeometricPhase.phase_geometric W G hG M z hz, hu, hs, ?_⟩
  intro hn
  letI : Nontrivial R := hn
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  have hfour : z^4 = 1 := by
    calc
      z^4 = (z^2)^2 := by ring
      _ = 1 := by rw [hs]; ring
  have hord : orderOf z = 4 := orderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [show (2:ℕ)^1 = 2 by decide, hs]; norm_num) hfour
  rw [← hord]
  exact IsPrimitiveRoot.orderOf _

#print axioms arbitrary_geometric_phase
end ArithmeticThetaArbitraryFourCharacterR0214
