module

public import ArbitraryTwoCoordinatesR0202
public import ArbitrarySplitCubicR0202
public import RelativeFourTorsionRootR0190

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryFourTorsionRoot
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
  [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
include hG

/-- The accepted level-reduction argument works without domain assumptions. -/
lemma level_reduction (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) :
    ∃ N : FullLevel R W G d (𝟙 (Base R)),
      N.x = G.nsmul (𝟙 _) (L/d) M.x ∧ N.y = G.nsmul (𝟙 _) (L/d) M.y := by
  let := FullLevelCyclicLiftsR0175.sectionGroup G hG
  have hqd : L / d * d = L := Nat.div_mul_cancel hdL
  have hq : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
  have hlt (i : Fin d) : L / d * i.val < L := by
    have h := Nat.mul_lt_mul_of_pos_left i.isLt hq
    rwa [hqd] at h
  have hmul (n : ℕ) (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      G.nsmul (𝟙 (Base R)) n (G.nsmul (𝟙 (Base R)) (L / d) z) =
        G.nsmul (𝟙 (Base R)) (L / d * n) z := by
    simp only [FullLevelTorsionSplittingR0175.nsmul_pow, pow_mul]
  let N : FullLevel R W G d (𝟙 (Base R)) :=
    { x := G.nsmul (𝟙 (Base R)) (L / d) M.x
      y := G.nsmul (𝟙 (Base R)) (L / d) M.y
      killed_x := by rw [hmul, hqd, M.killed_x]
      killed_y := by rw [hmul, hqd, M.killed_y]
      avoids := by
        intro i j hij
        rw [hmul, hmul]
        apply M.avoids ⟨L / d * i.val, hlt i⟩ ⟨L / d * j.val, hlt j⟩
        rcases hij with hi | hj
        · exact Or.inl (Nat.mul_ne_zero (Nat.ne_of_gt hq) hi)
        · exact Or.inr (Nat.mul_ne_zero (Nat.ne_of_gt hq) hj) }
  exact ⟨N, rfl, rfl⟩

lemma coordinates (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) :
    ∃ (e : Fin 3 → R) (x y : R), Labels R W G L M e ∧ SplitCubic R W e ∧
      HasCoordinates R W (quarterPoint R W G L M) x y := by
  have h2 : 2 ∣ L := dvd_trans (by decide) h4
  obtain ⟨N, hNx, hNy⟩ := level_reduction W G hG L 2 hL (by decide) h2 M
  obtain ⟨e, he⟩ := ArithmeticThetaArbitraryAffineR0202.arbitrary_two_coordinates R W G hG N
  have hs := ArithmeticThetaArbitraryAffineR0202.arbitrary_split_cubic R W G hG N e he
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

omit hG in
/-- The field computation applies to arbitrary field-valued points of a domain-base
family, not merely to sections over the coefficient base. -/
lemma domain_field_double {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
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
    y ≠ V.negY x y ∧ V.addX x x (V.slope x x y y) = ψ (xOverZ U.toProjective) := by
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
  refine ⟨hn, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn] at he
  exact (WeierstrassCurve.Affine.Point.some.inj he).1

omit hG in
/-- Transport an actual doubling relation and both affine coordinate maps through
an actual Cartesian coefficient map. The test ring has no reducedness assumption. -/
lemma transport_double {T : Type u} [CommRing T]
    (U : WeierstrassCurve T) [U.IsElliptic]
    (H : Law T U)
    (hH : ∀ {S : Scheme.{u}} (s : S ⟶ Base T),
      (H.one s).val = s ≫ (kwZeroSect T U).val)
    (c : T →+* R)
    (G : Law R (U.map c)) (hG : IsOriginLaw R (U.map c) G)
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R (U.map c)))
    (hd : G.mul _ P P = Q) (x y t z : R)
    (hp : HasCoordinates R (U.map c) P.val x y)
    (hq : HasCoordinates R (U.map c) Q.val t z) :
    ∃ (P' Q' : SchemeHomOver (Spec.map (CommRingCat.ofHom c)) (structureMap T U))
      (χ ψ : ChartRing T U →+* R),
      H.mul _ P' P' = Q' ∧
      P'.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T U ∧
      Q'.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion T U ∧
      χ (xOverZ U.toProjective) = x ∧ χ (yOverZ U.toProjective) = y ∧
      ψ (xOverZ U.toProjective) = t ∧ ψ (yOverZ U.toProjective) = z := by
  obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom U.toProjective c
  have hcart := isPullback_projMap_of_isCoefficientHom U.toProjective c φ hφ hcoef
  obtain ⟨G', hmul, hone⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback c
    (projModelStrCR U.toProjective) (projModelStrCR (U.toProjective.map c))
    (Proj.map φ hφ) hcart H
  have hone' := fun {S : Scheme.{u}} (s : S ⟶ Base R) =>
    one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback U.toProjective c φ hφ hcoef hcart
      H G' (fun t => hH t) (fun t => hone t) s
  have he : (G.one (𝟙 (Base R))).val = (G'.one (𝟙 (Base R))).val := by
    rw [hG.1, hone']
    rfl
  have hd' : G'.mul (𝟙 (Base R)) P P = Q := by
    rw [← RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (U.toProjective.map c) G G' he]
    exact hd
  let push (S : SchemeHomOver (𝟙 (Base R)) (structureMap R (U.map c))) :
      SchemeHomOver (Spec.map (CommRingCat.ofHom c)) (structureMap T U) :=
    ⟨S.val ≫ Proj.map φ hφ, by
      change S.val ≫ Proj.map φ hφ ≫ projModelStrCR U.toProjective = _
      rw [hcart.w, ← Category.assoc]
      change (S.val ≫ structureMap R (U.map c)) ≫ _ = _
      rw [S.property, Category.id_comp]⟩
  have hd'' : H.mul _ (push P) (push P) = push Q := by
    have hex : ∃ P' Q' : SchemeHomOver ((𝟙 (Base R)) ≫ Spec.map (CommRingCat.ofHom c))
        (projModelStrCR U.toProjective),
        P'.val = P.val ≫ Proj.map φ hφ ∧ Q'.val = Q.val ≫ Proj.map φ hφ ∧
        H.mul _ P' P' = Q' := by
      refine ⟨⟨P.val ≫ Proj.map φ hφ, ?_⟩, ⟨Q.val ≫ Proj.map φ hφ, ?_⟩, rfl, rfl, ?_⟩
      · rw [Category.assoc, hcart.w, ← Category.assoc]
        exact congrArg (· ≫ Spec.map (CommRingCat.ofHom c)) P.property
      · rw [Category.assoc, hcart.w, ← Category.assoc]
        exact congrArg (· ≫ Spec.map (CommRingCat.ofHom c)) Q.property
      · apply Subtype.ext
        have h := hmul (𝟙 (Base R)) P P
        rw [hd'] at h
        exact h.symm
    rw [Category.id_comp] at hex
    obtain ⟨P', Q', hP', hQ', hh⟩ := hex
    have hPe : P' = push P := Subtype.ext hP'
    have hQe : Q' = push Q := Subtype.ext hQ'
    simpa only [hPe, hQe] using hh
  obtain ⟨θ, hθ, hxθ, hyθ⟩ := exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
    U.toProjective c φ hφ hcoef
  have hfac (S : SchemeHomOver (𝟙 (Base R)) (structureMap R (U.map c)))
      (χ : ChartRing R (U.map c) →+* R)
      (hχ : S.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R (U.map c)) :
      (push S).val = Spec.map (CommRingCat.ofHom (χ.comp θ)) ≫ chartInclusion T U := by
    change S.val ≫ Proj.map φ hφ = _
    rw [hχ, Category.assoc]
    change Spec.map (CommRingCat.ofHom χ) ≫ (zChartι (U.toProjective.map c) ≫ Proj.map φ hφ) = _
    rw [hθ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨_, χ, hχ, hx, hy⟩ := hp
  obtain ⟨_, ψ, hψ, ht, hz⟩ := hq
  exact ⟨push P, push Q, χ.comp θ, ψ.comp θ, hd'', hfac P χ hχ, hfac Q ψ hψ,
    by simpa only [RingHom.comp_apply, hxθ] using hx,
    by simpa only [RingHom.comp_apply, hyθ] using hy,
    by simpa only [RingHom.comp_apply, hxθ] using ht,
    by simpa only [RingHom.comp_apply, hyθ] using hz⟩

/-- Field specialization of doubling for an arbitrary coefficient ring, using
the universal coefficient map and its exact affine coordinate pullbacks. -/
lemma field_double (F : Type u) [Field F] [DecidableEq F] [Algebra R F]
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hd : G.nsmul (𝟙 _) 2 P = Q) (x y t z : R)
    (hp : HasCoordinates R W P.val x y) (hq : HasCoordinates R W Q.val t z) :
    let V := (W.toProjective.baseChange F).toAffine
    let f := algebraMap R F
    f y ≠ V.negY (f x) (f y) ∧
      V.addX (f x) (f x) (V.slope (f x) (f x) (f y) (f y)) = f t := by
  classical
  obtain ⟨c, hc⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_universal_map W
  subst W
  let U := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.SmoothUniversalCurve.{u}
  obtain ⟨H, hH⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_origin_law U
  have hmul : G.mul (𝟙 _) P P = Q := by
    simpa only [show 2 = 1+1 from rfl, G.nsmul_succ, G.nsmul_one_apply,
      G.nsmul_zero, G.one_mul] using hd
  obtain ⟨P', Q', χ, ψ, hdouble, hχ, hψ, hx, hy, ht, hz⟩ :=
    transport_double U H (fun s => hH s) c G hG P Q hmul x y t z hp hq
  let f := algebraMap R F
  letI : Algebra _ F := (f.comp c).toAlgebra
  let b := Spec.map (CommRingCat.ofHom f)
  have hb : b ≫ Spec.map (CommRingCat.ofHom c) =
      Spec.map (CommRingCat.ofHom (algebraMap _ F)) := by
    change Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom c) =
      Spec.map (CommRingCat.ofHom (f.comp c))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let PF := schemeHomOverComp b hb P'
  let QF := schemeHomOverComp b hb Q'
  have hdF : H.mul _ PF PF = QF := by
    rw [← H.mul_natural _ _ b hb, hdouble]
  have hfac (S : SchemeHomOver (Spec.map (CommRingCat.ofHom c)) (structureMap _ U))
      (θ : ChartRing _ U →+* R)
      (hθ : S.val = Spec.map (CommRingCat.ofHom θ) ≫ chartInclusion _ U) :
      (schemeHomOverComp b hb S).val =
        Spec.map (CommRingCat.ofHom (f.comp θ)) ≫ chartInclusion _ U := by
    change b ≫ S.val = _
    rw [hθ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have h := domain_field_double U H (by simpa using hH (𝟙 _)) F PF QF hdF
    (f.comp χ) (f.comp ψ) (hfac P' χ hχ) (hfac Q' ψ hψ)
  dsimp only at h
  simp only [RingHom.comp_apply, hx, hy, ht] at h
  exact h

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

#print axioms coordinates
#print axioms transport_double
#print axioms ordinate_unit

section IntegralScheme
omit hG
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

/-- The coordinate pullback on global sections, with the canonical Spec identification. -/
def coordPull {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

lemma coordPull_comp {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (g : Y ⟶ X) :
    coordPull (g ≫ f) = g.appTop.hom.comp (coordPull f) := by
  simp only [coordPull, Scheme.Hom.comp_appTop, Category.assoc, CommRingCat.hom_comp]
  rfl

lemma coordPull_spec {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.ΓSpecIso (.of B)).hom.hom.comp (coordPull (Spec.map (CommRingCat.ofHom f))) = f := by
  change ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec.map (CommRingCat.ofHom f)).appTop ≫ (Scheme.ΓSpecIso (.of B)).hom).hom = f
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

lemma coordPull_generic {A : Type u} [CommRing A] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom =
      (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (coordPull f) := by
  let q := X.fromSpecStalk (genericPoint X)
  have h := coordPull_spec (Spec.preimage (q ≫ f)).hom
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, coordPull_comp] at h
  rw [← h]
  ext a
  change (Scheme.ΓSpecIso X.functionField).hom
    (q.appTop (coordPull f a)) = _
  dsimp only [q]
  rw [Scheme.fromSpecStalk_appTop]
  simp only [CommRingCat.comp_apply]
  change (Scheme.ΓSpecIso X.functionField).hom
    ((Scheme.ΓSpecIso X.functionField).inv
      ((X.presheaf.germ ⊤ (genericPoint X) trivial) (coordPull f a))) = _
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso X.functionField).inv_hom_id _) 

lemma clear_duplication {K : Type u} [Field K] (a b x t n d : K) (hd : d ≠ 0)
    (h : (n/d)^2 + a*(n/d) - b - x - x = t) :
    d^2*(t+b+2*x) = n^2+a*n*d := by
  field_simp at h
  linear_combination -h

/-- The cleared tangent duplication identity on an integral test scheme. -/
lemma integral_double {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
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
    d^2 * (ψ (xOverZ U.toProjective) + a₂ + 2*x) = n^2 + a₁*n*d := by
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
  have h := domain_field_double U H hH F PF QF hdF χ ψ hpF hqF
  dsimp only at h
  obtain ⟨hn, hx⟩ := h
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn] at hx
  have hden : χ (yOverZ U.toProjective) -
      ((U.toProjective.baseChange F).toAffine).negY
        (χ (xOverZ U.toProjective)) (χ (yOverZ U.toProjective)) ≠ 0 := sub_ne_zero.mpr hn
  simp only [WeierstrassCurve.Affine.negY] at hden
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY] at hx
  have hχ := coordPull_generic p
  have hψ := coordPull_generic q
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have hχv (a) : (X.presheaf.germ ⊤ (genericPoint X) trivial) (coordPull p a) = χ a :=
    (RingHom.congr_fun hχ a).symm
  have hψv (a) : (X.presheaf.germ ⊤ (genericPoint X) trivial) (coordPull q a) = ψ a :=
    (RingHom.congr_fun hψ a).symm
  simp only [hχv, hψv]
  have hcv (a : T) : χ (algebraMap T _ a) = f a := RingHom.congr_fun hc a
  rw [hcv, hcv, hcv, hcv]
  change (2*χ (yOverZ U.toProjective) + f U.a₁*χ (xOverZ U.toProjective) + f U.a₃)^2 *
    (ψ (xOverZ U.toProjective) + f U.a₂ + 2*χ (xOverZ U.toProjective)) = _
  have hde : χ (yOverZ U.toProjective) -
      (-χ (yOverZ U.toProjective) - f U.a₁ * χ (xOverZ U.toProjective) - f U.a₃) =
      2*χ (yOverZ U.toProjective) + f U.a₁*χ (xOverZ U.toProjective) + f U.a₃ := by ring
  change _ - (-_ - f U.a₁ * _ - f U.a₃) ≠ 0 at hden
  change ( _ / (_ - (-_ - f U.a₁ * _ - f U.a₃)))^2 +
    f U.a₁ * (_ / (_ - (-_ - f U.a₁ * _ - f U.a₃))) - f U.a₂ - _ - _ = _ at hx
  rw [hde] at hx hden
  exact clear_duplication _ _ _ _ _ _ hden hx

/-- A universal chart identity is pulled back to an arbitrary test ring. The open
where the doubled point is affine is integral when nonempty; its empty case is
handled by its zero ring of sections. No reducedness is required of the test ring. -/
lemma domain_base_double {T S : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
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
    d^2 * (ψ (xOverZ U.toProjective) + c U.a₂ + 2*x) = n^2 + c U.a₁*n*d := by
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
      d^2*(ψD (xOverZ U.toProjective)+a₂+2*x) = n^2+a₁*n*d := by
    cases isEmpty_or_nonempty D with
    | inl h => exact Subsingleton.elim _ _
    | inr h =>
      letI : IsDomain A := isDomain_chart_of_isElliptic U 2
      letI : IsIntegral D := isIntegral_of_isOpenImmersion D.ι
      exact integral_double U H hH _ PD QD hdD D.ι q rfl hq₀.symm
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
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at hh
  have heχv (a) : ev (coordPull D.ι a) = χ a := RingHom.congr_fun heχ a
  have heψv (a) : ev (coordPull q a) = ψ a := RingHom.congr_fun heψ a
  simp only [heχv, heψv] at hh
  simp only [A, hcv] at hh
  exact hh


include hG in
/-- Cleared doubling in the original coefficient ring, including nilpotents. -/
lemma raw_double
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hd : G.nsmul (𝟙 _) 2 P = Q) (x y t z : R)
    (hp : HasCoordinates R W P.val x y) (hq : HasCoordinates R W Q.val t z) :
    let d := 2*y+W.a₁*x+W.a₃
    let n := 3*x^2+2*W.a₂*x+W.a₄-W.a₁*y
    d^2*(t+W.a₂+2*x) = n^2+W.a₁*n*d := by
  obtain ⟨c, hc⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_universal_map W
  subst W
  let U := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.SmoothUniversalCurve.{u}
  obtain ⟨H, hH⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_origin_law U
  have hmul : G.mul (𝟙 _) P P = Q := by
    simpa only [show 2 = 1+1 from rfl, G.nsmul_succ, G.nsmul_one_apply,
      G.nsmul_zero, G.one_mul] using hd
  obtain ⟨P', Q', χ, ψ, hdouble, hχ, hψ, hx, hy, ht, hz⟩ :=
    transport_double U H (fun s => hH s) c G hG P Q hmul x y t z hp hq
  have h := domain_base_double U H (by simpa using hH (𝟙 _)) c P' Q' hdouble χ ψ hχ hψ
  dsimp only at h
  rw [hx, hy, ht] at h
  exact h

/-- Pure polynomial elimination of the tangent numerator. -/
lemma split_raw_identity {A : Type u} [CommRing A]
    (a₁ a₂ a₃ a₄ a₆ r s t x y : A)
    (ha : 4*a₂+a₁^2 = -4*(r+s+t))
    (hb : 2*a₄+a₁*a₃ = 2*(r*s+r*t+s*t))
    (hc : 4*a₆+a₃^2 = -4*(r*s*t))
    (he : y^2+a₁*x*y+a₃*y = x^3+a₂*x^2+a₄*x+a₆)
    (hd : (2*y+a₁*x+a₃)^2*(s+a₂+2*x) =
      (3*x^2+2*a₂*x+a₄-a₁*y)^2 +
      a₁*(3*x^2+2*a₂*x+a₄-a₁*y)*(2*y+a₁*x+a₃)) :
    4*((x-r)^2-(r-s)*(r-t))^2 = 4*(2*y+a₁*x+a₃)^2*(s-r) := by
  let d := 2*y+a₁*x+a₃
  let n := 3*x^2+2*a₂*x+a₄-a₁*y
  let m := 3*x^2-2*(r+s+t)*x+(r*s+r*t+s*t)
  have hm : 2*m = 2*n+a₁*d := by
    dsimp [m, n, d]
    linear_combination -x*ha - hb
  have he' : d^2 = 4*(x-r)*(x-s)*(x-t) := by
    dsimp [d]
    linear_combination 4*he+x^2*ha+2*x*hb+hc
  have hd' : d^2*(s+a₂+2*x) = n^2+a₁*n*d := hd
  have hm' : 4*m^2 = 4*d^2*(s-(r+s+t)+2*x) := by
    linear_combination (2*m+2*n+a₁*d)*hm - 4*hd' + d^2*ha
  change 4*((x-r)^2-(r-s)*(r-t))^2 = 4*d^2*(s-r)
  dsimp [m] at hm'
  linear_combination hm' + 4*(2*x-s-t)*he'

end IntegralScheme

lemma numerator_square (L : ℕ) (h4 : 4 ∣ L)
    (M : FullLevel R W G L (𝟙 (Base R))) (e : Fin 3 → R) (x y g : R)
    (he : Labels R W G L M e) (hs : SplitCubic R W e)
    (hp : HasCoordinates R W (quarterPoint R W G L M) x y)
    (hu : IsUnit (completedY R W x y))
    (hg : 2 * completedY R W x y * g = (x-e 0)^2 - (e 0-e 1)*(e 0-e 2)) :
    g^2 = e 1-e 0 := by
  let P := G.nsmul (𝟙 (Base R)) (L/4) M.y
  let Q := G.nsmul (𝟙 (Base R)) (L/2) M.y
  have hq : HasCoordinates R W Q.val (e 1)
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 1 + W.a₃)) := he 1
  have hd : G.nsmul (𝟙 _) 2 P = Q := double_quarter W G hG L h4 M
  have hraw := raw_double W G hG P Q hd x y _ _ hp hq
  obtain ⟨ha, hb, hc⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitrarySplitCubic.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
    (e 0) (e 1) (e 2)
    (hs.1 0 1 (by decide)) (hs.1 1 2 (by decide)) (hs.1 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))
  have hhalf := TwoTorsionSplitCubicR0177.half_identity (R := R)
  have hquarter : 4*algebraMap ℚ R (1/4) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (4:ℚ)*(1/4)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  have ha' : 4*W.a₂+W.a₁^2 = -4*(e 0+e 1+e 2) := by
    linear_combination 4*ha-W.a₁^2*hquarter
  have hb' : 2*W.a₄+W.a₁*W.a₃ = 2*(e 0*e 1+e 0*e 2+e 1*e 2) := by
    linear_combination 2*hb-W.a₁*W.a₃*hhalf
  have hc' : 4*W.a₆+W.a₃^2 = -4*(e 0*e 1*e 2) := by
    linear_combination 4*hc-W.a₃^2*hquarter
  have heq := (WeierstrassCurve.Affine.equation_iff ..).mp
    (TwoTorsionSplitCubicR0177.equation hp)
  have hn := split_raw_identity W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (e 0) (e 1) (e 2) x y
    ha' hb' hc' heq hraw
  have hu4 : IsUnit (4:R) := isUnit_iff_exists_inv.mpr ⟨algebraMap ℚ R (1/4), hquarter⟩
  have hN : ((x-e 0)^2-(e 0-e 1)*(e 0-e 2))^2 =
      (2*y+W.a₁*x+W.a₃)^2*(e 1-e 0) := by
    apply hu4.mul_left_cancel
    simpa only [mul_assoc] using hn
  have hden : 2*completedY R W x y = 2*y+W.a₁*x+W.a₃ := by
    dsimp [completedY]
    linear_combination (W.a₁*x+W.a₃)*hhalf
  rw [← hden] at hN
  have hu2 : IsUnit (2:R) := isUnit_iff_exists_inv.mpr ⟨algebraMap ℚ R (1/2), hhalf⟩
  apply ((hu2.mul hu).pow 2).mul_left_cancel
  calc
    (2*completedY R W x y)^2*g^2 = (2*completedY R W x y*g)^2 := (mul_pow ..).symm
    _ = ((x-e 0)^2-(e 0-e 1)*(e 0-e 2))^2 := congrArg (·^2) hg
    _ = (2*completedY R W x y)^2*(e 1-e 0) := hN

end ArbitraryFourTorsionRoot

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190 ArbitraryFourTorsionRoot

/-- The actual quarter marking supplies the signed unit square root over every
commutative rational algebra, with the exact identity in the original ring. -/
theorem arbitrary_four_torsion_root :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : Law R W) (hG : IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L →
      ∀ (M : FullLevel R W G L (𝟙 (Base R))),
      ∃ (e : Fin 3 → R) (x y g : R), RootData R W G L M e x y g := by
  intro R _ _ W _ G hG L hL h4 M
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
  have hsq : g^2 = e 1-e 0 := numerator_square W G hG L h4 M e x y g he hs hp hu hg
  have hgu : IsUnit g := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    (hsq.symm ▸ hs.1 1 0 (by decide))
  exact ⟨e, x, y, g, he, hs, hp, hu, hgu, hg, hsq⟩

#print axioms arbitrary_four_torsion_root
end ArithmeticThetaArbitraryFourCharacterR0214
