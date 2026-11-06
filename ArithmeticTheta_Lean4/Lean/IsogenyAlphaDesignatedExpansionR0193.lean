import OpenIsogenyAlphaR0193

/-! Exact designated expansion of the normalized isogeny alpha. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaIsogenyHalfLinesR0193
namespace DesignatedExpansionProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

/-- Cancellation uses the actual degree, with no choice of a unit or sign. -/
lemma cancel_degree {K : Type} [Field K] [CharZero K]
    (H J : (Base K).Modules) (f : H ⟶ J)
    (η : Γ(H, ⊤)) (ω : Γ(J, ⊤)) (m : ℕ) (hm : 0 < m)
    (c : K) (hf : f.app ⊤ η = scalar K (m : K) • ω) :
    scalar K (m : K)⁻¹ • f.app ⊤ (scalar K c • η) = scalar K c • ω := by
  rw [Scheme.Modules.Hom.app_smul, hf, smul_smul, smul_smul]
  have he : scalar K (m : K)⁻¹ * scalar K c * scalar K (m : K) = scalar K c := by
    unfold scalar
    change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _ *
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _ *
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _
    rw [← map_mul, ← map_mul]
    congr 1
    have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    field_simp
  rw [he]

/-- A commuting square of sheaf morphisms transports a global section through
the original base change. -/
lemma transport_map {X Y : Scheme} (p : X ⟶ Y)
    (M N : Y.Modules) (M' N' : X.Modules)
    (eM : (Scheme.Modules.pullback p).obj M ≅ M')
    (eN : (Scheme.Modules.pullback p).obj N ≅ N')
    (f : M ⟶ N) (g : M' ⟶ N')
    (hsq : (Scheme.Modules.pullback p).map f ≫ eN.hom = eM.hom ≫ g)
    (s : Γ(M, ⊤)) :
    transportSection p N N' eN (f.app ⊤ s) =
      g.app ⊤ (transportSection p M M' eM s) := by
  unfold transportSection
  rw [Scheme.Modules.pullbackLocalSection_app]
  have he := congrArg (fun h => h.app (p ⁻¹ᵁ ⊤)
    (Scheme.Modules.pullbackLocalSection p s)) hsq
  change eN.hom.app _ (((Scheme.Modules.pullback p).map f).app _ _) =
    g.app _ (eM.hom.app _ _) at he
  rw [he]
  simp only [Scheme.Hom.preimage_top, InitialHodgeSection.res_self]


open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open CategoryTheory.Limits

/-- The comparison retains the quotient arrow, the complete point labels,
and the exact differential weight. -/
structure TateComparison (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (Q : CyclicQuotient k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k) where
  law : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k (L*m))
  originLaw : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k (L*m)) law
  test : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring Q.target
    (LaurentSeries k) (TateCurve k (L*m)) law
  scalar_eq : test.scalar = (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom
  differential : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k (L*m)
  normalized : ArithmeticThetaBoundaryHodgeR0182.Normalized k (L*m) differential
  map : Curve (LaurentSeries k) (TateCurve k L) ⟶ Curve (LaurentSeries k) (TateCurve k (L*m))
  over_eq : map ≫ structureMap (LaurentSeries k) (TateCurve k (L*m)) =
    structureMap (LaurentSeries k) (TateCurve k L)
  zero_eq : origin (LaurentSeries k) (TateCurve k L) ≫ map =
    origin (LaurentSeries k) (TateCurve k (L*m))
  square : V.map ≫ Q.arrow.map = map ≫ test.map
  weight : (PeriodDifferential.pointMap (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries k) (TateCurve k (L*m))) map over_eq
    (origin (LaurentSeries k) (TateCurve k L))
    (origin (LaurentSeries k) (TateCurve k (L*m))) zero_eq).app ⊤
      (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k (L*m) differential) =
    scalar (LaurentSeries k) (m : LaurentSeries k) •
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential
  coordinates : ∀ i j : Fin L, j.val ≠ 0 ∨ ζ^(i.val*m) ≠ 1 →
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k (L*m))
      (coordinatePoint (LaurentSeries k) (TateCurve k L) V.level.law V.level.marking i j ≫ map)
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX (L*m) (m*j.val) (ζ^(i.val*m))))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY (L*m) (m*j.val) (ζ^(i.val*m))))

lemma tate_comparison (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (hr : 0 < L) (hm : 0 < m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (Q : CyclicQuotient k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k)
    (hζ : IsPrimitiveRoot ζ L) (hmark : CanonicalMarking k L ζ V.level) :
    Nonempty (TateComparison k L m D Q V ζ) := by
  classical
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h3r : 3 ≤ L := by have := Nat.le_of_dvd hr hdiv; omega
  have hs : 0 < L*m := Nat.mul_pos hr hm
  have h3s : 3 ≤ L*m := by nlinarith
  have her : Even L := even_iff_two_dvd.mpr (dvd_trans (by use 4*m; omega) hdiv)
  have hes : Even (L*m) := her.mul_right m
  have hmr : m ∣ L := dvd_trans (by use 8; omega) hdiv
  let z : kˣ := (hζ.isUnit hr.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hr.ne').unit_spec
  have hzp : IsPrimitiveRoot (z : k) L := by simpa only [hz] using hζ
  have hzm : CanonicalMarking k L (z : k) V.level := by simpa only [hz] using hmark
  obtain ⟨T,M,hM⟩ := TateFullLevelMarking.model_exists k (L*m) h3s hs
  obtain ⟨U,A,hA⟩ := TateFullLevelMarking.model_exists k L h3r hr
  let p (i : Fin (L*m)) :=
    MarkedPointAddition.sectionAt k h3s M hM i 1
  have hp (i : Fin (L*m)) : MarkedLift k M i 1 (p i) :=
    MarkedPointAddition.sectionAt_spec k h3s M hM i 1
  let p₀ := p (zeroIndex (L*m) hs)
  have hp₀ : MarkedLift k M (zeroIndex (L*m) hs) 1 p₀ := hp _
  obtain ⟨q,hq,-⟩ := marked_section_algebraization k L hr h3r U A hA
    (zeroIndex L hr) 1
  obtain ⟨G,hG,-⟩ := actual_generic_group_law k (L*m) hs h3s T hes M hM p₀ hp₀
  obtain ⟨H,hH,-⟩ := actual_generic_group_law k L hr h3r U her A hA q hq
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3s M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3r A hA
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3s M hM p₀ hp₀
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3r A hA q hq
  letI : IsLocallyNoetherian (genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  letI : IsLocallyNoetherian (genericScheme k A) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k A)
  obtain ⟨XA,YA,hXA,hYA,EA,hEA,hOA,hcoordA,hframeA⟩ :=
    CubicComparison.model_iso_framed k L hr h3r her U A hA q hq
  obtain ⟨XM,YM,hXM,hYM,EM,hEM,hOM,hcoordM,hframeM⟩ :=
    CubicComparison.model_iso_framed k (L*m) hs h3s hes T M hM p₀ hp₀
  have hmarkA := CubicComparison.marking_of_coordinates k L hr A q hq
    V.level z hzp hzm EA hOA hcoordA
  obtain ⟨δ,hδ⟩ := CubicComparison.normalized_tate_frame k (L*m) h3s hes
  obtain ⟨δA,hδA,hgenA⟩ := hframeA V.differential V.normalized
  obtain ⟨δM,hδM,hgenM⟩ := hframeM δ hδ
  obtain ⟨dual,⟨hdualOver,hdual,hdual'⟩,-⟩ :=
    PeriodCollapse.dual_exists k h3r h3s hes M hM A hA p hp q hq G hG H hH
  have hdualZero : genericPoint k A q hq.1 ≫ dual = genericPoint k M p₀ hp₀.1 := by
    apply PeriodCollapse.dual_marked k hm h3s hes M hM A hA p₀ hp₀ G hG dual hdual
      (zeroIndex L hr) 1 q hq p₀
    simpa only [zeroIndex,Nat.mul_zero,one_pow] using hp₀
  have hdualWeight := PeriodDifferential.dual_hodge k h3r h3s her hes M hM A hA
    p₀ hp₀ q hq G hG H hH XM YM hXM hYM XA YA hXA hYA δM hδM δA hδA
    dual hdualOver hdualZero hdual'
  rw [ArithmeticThetaHodgeFourTorsionR0147.ActualFourTorsionHodgeRoot.hodgeSection_smul
    k A q hq.1 δA (m : LaurentSeries k)] at hdualWeight
  obtain ⟨e,he,heOver,heZero⟩ := ToricQuotient.compare k hm hmr h3r h3s her hes
    M hM A hA p hp q hq G hG H hH dual hdualOver hdual hdual'
    V z hzp EA hEA hOA hmarkA Q
  let B := V.base ≫ D.quotient.inclusion
  let ρ : D.atlas.quotient.ring →+* LaurentSeries k := (Spec.preimage B).hom
  have hB : baseMap D.atlas.quotient.ring (LaurentSeries k) ρ = B := Spec.map_preimage B
  let et := e ≪≫ EM
  have het : et.hom ≫ structureMap (LaurentSeries k) (TateCurve k (L*m)) =
      (baseChangeFamily Q.target B).projection := by
    change (e.hom ≫ EM.hom) ≫ _ = _
    rw [Category.assoc,hEM,heOver]
  have hetZero : zero (baseChangeFamily Q.target B) ≫ et.hom =
      origin (LaurentSeries k) (TateCurve k (L*m)) := by
    change _ ≫ (e.hom ≫ EM.hom) = _
    rw [← Category.assoc,heZero,hOM]
  obtain ⟨Gt,hGt,Ct,hCtScalar,hCtMap⟩ := TargetTest.of_iso_over Q.target B ρ hB
    (TateCurve k (L*m)) et het hetZero
  let ψ := EA.inv ≫ dual ≫ EM.hom
  have hψ : ψ ≫ structureMap (LaurentSeries k) (TateCurve k (L*m)) =
      structureMap (LaurentSeries k) (TateCurve k L) := by
    dsimp only [ψ]
    rw [Category.assoc,Category.assoc,hEM,hdualOver,← hEA,EA.inv_hom_id_assoc]
  have hψZero : origin (LaurentSeries k) (TateCurve k L) ≫ ψ =
      origin (LaurentSeries k) (TateCurve k (L*m)) := by
    rw [← hOA]
    simp only [ψ,Category.assoc,Iso.hom_inv_id_assoc]
    rw [← Category.assoc,hdualZero,hOM]
  have hψsquare : EA.hom ≫ ψ = dual ≫ EM.hom := by
    simp only [ψ,Iso.hom_inv_id_assoc]
  letI := V.level.elliptic
  letI := TateFullLevelMarking.elliptic k (L*m) h3s hes
  letI : SmoothOfRelativeDimension 1
      (structureMap (LaurentSeries k) (TateCurve k L)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
      (TateCurve k L).toProjective
  letI : SmoothOfRelativeDimension 1
      (structureMap (LaurentSeries k) (TateCurve k (L*m))) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
      (TateCurve k (L*m)).toProjective
  have hweight := PeriodDifferential.transfer_weight
    (K := LaurentSeries k)
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries k) (TateCurve k (L*m)))
    (genericStructure k A) (genericStructure k M) EA hEA EM hEM ψ hψ dual hdualOver
    (origin (LaurentSeries k) (TateCurve k L))
    (origin (LaurentSeries k) (TateCurve k (L*m)))
    (genericPoint k A q hq.1) (genericPoint k M p₀ hp₀.1)
    hOA hOM hψZero hdualZero hψsquare
    (hodgeGenerator k L V.differential) (hodgeGenerator k (L*m) δ)
    _ _ hgenA hgenM (scalar (LaurentSeries k) (m : LaurentSeries k)) hdualWeight
  have hmodelSquare : EA.hom ≫ V.map ≫ Q.arrow.map = dual ≫ EM.hom ≫ Ct.map := by
    rw [hCtMap]
    change EA.hom ≫ V.map ≫ Q.arrow.map =
      dual ≫ EM.hom ≫ (EM.inv ≫ e.inv) ≫ pullback.fst Q.target.projection B
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [← he]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    exact (Category.assoc EA.hom V.map Q.arrow.map).symm.trans
      (QuotientComparison.baseChangeArrow_fst D.atlas.descent.family Q.target Q.arrow B
        (genericStructure k A) (EA.hom ≫ V.map) (ToricQuotient.model_cartesian k L A V EA hEA)).symm
  have hmap : V.map ≫ Q.arrow.map = ψ ≫ Ct.map := by
    apply (cancel_epi EA.hom).mp
    calc
      EA.hom ≫ (V.map ≫ Q.arrow.map) = dual ≫ EM.hom ≫ Ct.map := hmodelSquare
      _ = EA.hom ≫ (ψ ≫ Ct.map) := by
        rw [← Category.assoc EA.hom ψ Ct.map,hψsquare,Category.assoc]
  refine ⟨⟨Gt, hGt, Ct, hCtScalar, δ, hδ, ψ, hψ, hψZero, hmap, hweight, ?_⟩⟩
  intro i j hne
  let j' : Fin (L*m) := ⟨m*j.val, by
    simpa only [Nat.mul_comm L m] using Nat.mul_lt_mul_of_pos_left j.isLt hm⟩
  let u := MarkedPointAddition.sectionAt k h3r A hA j (z^i.val)
  have hu := MarkedPointAddition.sectionAt_spec k h3r A hA j (z^i.val)
  let v := MarkedPointAddition.sectionAt k h3s M hM j' ((z^i.val)^m)
  have hv := MarkedPointAddition.sectionAt_spec k h3s M hM j' ((z^i.val)^m)
  have huv := PeriodCollapse.dual_marked k hm h3s hes M hM A hA p₀ hp₀ G hG
    dual hdual j (z^i.val) u hu v hv
  have hpt : coordinatePoint (LaurentSeries k) (TateCurve k L)
      V.level.law V.level.marking i j ≫ ψ = genericPoint k M v hv.1 ≫ EM.hom := by
    rw [← hmarkA i j u hu]
    simp only [ψ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, huv]
  rw [hpt]
  have hn : j'.val ≠ 0 ∨ (((z^i.val)^m : kˣ) : k) ≠ 1 := by
    rcases hne with hj | hz'
    · exact Or.inl (Nat.mul_ne_zero hm.ne' hj)
    · exact Or.inr (by simpa only [Units.val_pow_eq_pow_val, hz, ← pow_mul] using hz')
  simpa only [j', Units.val_pow_eq_pow_val, hz, ← pow_mul] using
    hcoordM j' ((z^i.val)^m) v hv hn


open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha

/-- Every combination of the prescribed target labels is the image of its
specified source lift. This statement uses the supplied quotient. -/
lemma target_combination (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D) (a b : ℕ) :
    (A.quotient.target.law.mul (𝟙 _)
      (A.quotient.target.law.nsmul (𝟙 _) b A.marking.x)
      (A.quotient.target.law.nsmul (𝟙 _) a A.marking.y)).val =
      liftPoint k L D.atlas m 4 a b ≫ A.quotient.arrow.map := by
  let E := SourceFamily k L D
  letI := sectionGroup E
  letI := sectionGroup A.quotient.target
  let F := pointHom E A.quotient.arrow A.quotient.hom (𝟙 _)
  let sx := D.atlas.marking.x ^ (L/(m*4))
  let sy := D.atlas.marking.y ^ (L/4)
  have hx : A.marking.x = F sx := by
    apply Subtype.ext
    change A.marking.x.val = sx.val ≫ A.quotient.arrow.map
    simpa only [ArithmeticThetaOpenHodgeR0180.liftPoint, Nat.mul_one, Nat.mul_zero,
      GoodReductionJacobian.RelativeGroupLaw.nsmul_zero,
      GoodReductionJacobian.RelativeGroupLaw.mul_one, nsmul_pow] using A.marked.1
  have hy : A.marking.y = F sy := by
    apply Subtype.ext
    change A.marking.y.val = sy.val ≫ A.quotient.arrow.map
    simpa only [ArithmeticThetaOpenHodgeR0180.liftPoint, Nat.mul_one, Nat.mul_zero,
      GoodReductionJacobian.RelativeGroupLaw.nsmul_zero,
      GoodReductionJacobian.RelativeGroupLaw.one_mul, nsmul_pow] using A.marked.2
  rw [nsmul_pow, nsmul_pow]
  change (A.marking.x ^ b * A.marking.y ^ a).val = _
  rw [hx, hy, ← map_pow, ← map_pow, ← map_mul]
  change (sx ^ b * sy ^ a).val ≫ A.quotient.arrow.map = _
  dsimp only [sx, sy, ArithmeticThetaOpenHodgeR0180.liftPoint]
  simp only [nsmul_pow, pow_mul]
  rfl

/-- The Cartesian target test identifies the full-four lift with the actual
image of the source labels. -/
lemma lifted_combination (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k)
    (C : TateComparison k L m D A.quotient V ζ)
    [hE : (TateCurve k (L*m)).IsElliptic] (a b : ℕ) :
    (C.law.mul (𝟙 _)
      (C.law.nsmul (𝟙 _) b (liftMarking C.law C.originLaw C.test A.marking).x)
      (C.law.nsmul (𝟙 _) a (liftMarking C.law C.originLaw C.test A.marking).y)).val =
    ArithmeticThetaFullLevelCoverR0175.liftPoint (LaurentSeries k) (TateCurve k L)
      V.level.law m 4 a b V.level.marking ≫ C.map := by
  apply C.test.cartesian.hom_ext
  · change _ ≫ C.test.map = (_ ≫ C.map) ≫ C.test.map
    rw [Category.assoc, ← C.square, ← Category.assoc, test_lift]
    dsimp only [liftMarking]
    rw [liftMarkPoint_combination C.law C.originLaw C.test A.marking,
      target_combination k L m D A a b, C.scalar_eq]
    have hb : baseMap D.atlas.quotient.ring (LaurentSeries k)
        (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom =
        V.base ≫ D.quotient.inclusion := Spec.map_preimage _
    simp only [hb, Category.assoc]
  · rw [Category.assoc, C.over_eq]
    exact (C.law.mul (𝟙 _) _ _).property.trans
      (V.level.law.mul (𝟙 _) _ _).property.symm


open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaTateSeries

local instance laurentCharZero (k : Type) [Field k] [CharZero k] :
    CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k

/-- The accepted signed coefficient identity applies to a four-marking as
soon as its literal doubled and quarter labels have been identified. -/
lemma signed_alpha_of_labels (k : Type) [Field k] [CharZero k]
    (s : ℕ) (hs : 0 < s) (h4 : 4 ∣ s)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k s))
    (B : FullLevel (LaurentSeries k) (TateCurve k s) G 4 (𝟙 _))
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k s)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k s δ)
    (a : Γ(Hodge (LaurentSeries k) (TateCurve k s), ⊤))
    (ha : RealizesAlpha (LaurentSeries k) (TateCurve k s) G 4 B a)
    (hl : ∀ i : Fin 3, ∃ y : LaurentSeries k,
      HasCoordinates (LaurentSeries k) (TateCurve k s)
        (twoLabel (LaurentSeries k) (TateCurve k s) G 4 B i) (root k s i) y)
    (hq : HasCoordinates (LaurentSeries k) (TateCurve k s)
      (quarterPoint (LaurentSeries k) (TateCurve k s) G 4 B)
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX s (s/4) (1:k)))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY s (s/4) (1:k)))) :
    a = scalar (LaurentSeries k)
      (algebraMap (PowerSeries k) (LaurentSeries k) (thetaAt k s ^ 2)) •
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k s δ := by
  obtain ⟨e, x, y, g, ε, hd, hε, ha⟩ := ha
  have he : ∀ i, e i = root k s i := by
    intro i
    obtain ⟨y', hy'⟩ := hl i
    exact (FourTorsionTateBehavior.coordinates_unique _ _ _ _ _ _ (hd.1 i) hy').1
  have hxy := FourTorsionTateBehavior.coordinates_unique _ _ _ _ _ _ hd.2.2.1 hq
  have hg : 2*g = algebraMap (PowerSeries k) (LaurentSeries k) (thetaAt k s ^ 2) := by
    obtain ⟨n, rfl⟩ := h4
    apply FourTorsionTateBehavior.literal_coefficient_signed k n (by omega) g
    have hh := hd.2.2.2.2.2.1
    simpa [completedY, TateCurve, curve, he, hxy.1, hxy.2, root, rootSeries,
      show 4*n/2 = 2*n by omega, show 4*n/4 = n by omega] using hh
  obtain ⟨χ, hχ, hx, hy⟩ := hd.2.2.1.2
  have hy0 : y ≠ 0 := by
    have hu := hd.2.2.2.1
    simpa only [completedY, TateCurve, curve, zero_mul, zero_add,
      mul_zero, add_zero] using hu.ne_zero
  have hgen := FourTorsionTateBehavior.normalized_hodge_eq k s δ ε hδ hε χ
    (by simpa only [hy] using hy0)
  rw [hgen, hg] at ha
  exact ha


lemma combination_coordinates (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k)
    (C : TateComparison k L m D A.quotient V ζ)
    [(TateCurve k (L*m)).IsElliptic] (a b : ℕ)
    (hi : L/(m*4)*b < L) (hj : L/4*a < L)
    (hne : L/4*a ≠ 0 ∨ ζ^((L/(m*4)*b)*m) ≠ 1) :
    HasCoordinates (LaurentSeries k) (TateCurve k (L*m))
      (C.law.mul (𝟙 _)
        (C.law.nsmul (𝟙 _) b (liftMarking C.law C.originLaw C.test A.marking).x)
        (C.law.nsmul (𝟙 _) a (liftMarking C.law C.originLaw C.test A.marking).y)).val
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (tateX (L*m) (m*(L/4*a)) (ζ^((L/(m*4)*b)*m))))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (tateY (L*m) (m*(L/4*a)) (ζ^((L/(m*4)*b)*m)))) := by
  rw [lifted_combination k L m D A V ζ C a b]
  exact C.coordinates ⟨L/(m*4)*b, hi⟩ ⟨L/4*a, hj⟩ hne

/-- Evaluate the intrinsic alpha through the given quotient comparison. -/
lemma comparison_alpha (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (hL : 0 < L) (hm : 0 < m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (A : OpenAlpha k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (ζ : k)
    (hζ : IsPrimitiveRoot ζ L)
    (C : TateComparison k L m D A.quotient V ζ) :
    transportSection (baseMap D.atlas.quotient.ring (LaurentSeries k) C.test.scalar)
      (hodge A.quotient.target) (Hodge (LaurentSeries k) (TateCurve k (L*m)))
      (comparison C.test) A.alpha =
    scalar (LaurentSeries k)
      (algebraMap (PowerSeries k) (LaurentSeries k) (thetaAt k (L*m)^2)) •
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k (L*m) C.differential := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h4m : m*4 ∣ L := dvd_trans (by use 2; omega) hdiv
  have h4 : 4 ∣ L := dvd_trans (dvd_mul_left 4 m) h4m
  have hq := Nat.div_mul_cancel h4m
  have hr := Nat.div_mul_cancel h4
  have hqpos : 0 < L/(m*4) := Nat.div_pos (Nat.le_of_dvd hL h4m) (by positivity)
  have hrpos : 0 < L/4 := Nat.div_pos (Nat.le_of_dvd hL h4) (by decide)
  have hq2 : L/(m*4)*2 < L := by nlinarith
  have hr2 : L/4*2 < L := by omega
  have hr1 : L/4 < L := by omega
  have he : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) h4)
  have hzhalf := primitive_half k L hL he ζ hζ
  have hhalf : L/2*2 = L := Nat.div_mul_cancel (even_iff_two_dvd.mp he)
  have hpow : (L/(m*4)*2)*m = L/2 := by nlinarith
  have hquarter : m*(L/4) = (L*m)/4 := by
    rw [Nat.mul_comm L m, Nat.mul_div_assoc m h4]
  have hhalf' : m*(L/4*2) = (L*m)/2 := by
    have hh : (L*m)/2*2 = L*m := Nat.div_mul_cancel
      (dvd_mul_of_dvd_left (even_iff_two_dvd.mp he) m)
    nlinarith
  have hs : 0 < L*m := Nat.mul_pos hL hm
  have hs3 : 3 ≤ L*m := by have := Nat.le_of_dvd hL hdiv; nlinarith
  letI := TateFullLevelMarking.elliptic k (L*m) hs3 (he.mul_right m)
  let B := liftMarking C.law C.originLaw C.test A.marking
  have ha := A.intrinsic.2 (LaurentSeries k) (TateCurve k (L*m)) C.law C.originLaw
    C.test B (liftMarkPoint_map C.law C.test A.marking.x)
      (liftMarkPoint_map C.law C.test A.marking.y)
  have hx := combination_coordinates k L m D A V ζ C 0 2 hq2
    (by simpa using hL) (Or.inr (by rw [hpow, hzhalf]; norm_num))
  have hy := combination_coordinates k L m D A V ζ C 2 0
    (by simpa using hL) hr2 (Or.inl (by omega))
  have hxy := combination_coordinates k L m D A V ζ C 2 2 hq2 hr2 (Or.inl (by omega))
  have hqt := combination_coordinates k L m D A V ζ C 1 0
    (by simpa using hL) (by simpa using hr1) (Or.inl (by omega))
  simp only [Nat.mul_zero, Nat.zero_mul, pow_zero, hpow, hzhalf, hhalf', Nat.mul_one,
    hquarter, C.law.nsmul_zero, C.law.mul_one, C.law.one_mul] at hx hy hxy hqt
  have hl : ∀ i : Fin 3, ∃ y : LaurentSeries k,
      HasCoordinates (LaurentSeries k) (TateCurve k (L*m))
        (twoLabel (LaurentSeries k) (TateCurve k (L*m)) C.law 4 B i)
        (root k (L*m) i) y := by
    intro i
    fin_cases i
    · refine ⟨algebraMap (PowerSeries k) (LaurentSeries k) (tateY (L*m) 0 (-1:k)), ?_⟩
      simpa [twoLabel, B, root, rootSeries] using hx
    · refine ⟨algebraMap (PowerSeries k) (LaurentSeries k) (tateY (L*m) ((L*m)/2) (1:k)), ?_⟩
      simpa [twoLabel, B, root, rootSeries] using hy
    · refine ⟨algebraMap (PowerSeries k) (LaurentSeries k) (tateY (L*m) ((L*m)/2) (-1:k)), ?_⟩
      simpa [twoLabel, B, root, rootSeries] using hxy
  have hq' : HasCoordinates (LaurentSeries k) (TateCurve k (L*m))
      (quarterPoint (LaurentSeries k) (TateCurve k (L*m)) C.law 4 B)
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX (L*m) ((L*m)/4) (1:k)))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY (L*m) ((L*m)/4) (1:k))) := by
    simpa only [quarterPoint, B, Nat.reduceDiv] using hqt
  have hex := signed_alpha_of_labels k (L*m) hs (dvd_mul_of_dvd_left h4 m)
    C.law B C.differential C.normalized _ ha hl hq'
  simpa only [transportSection, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top, InitialHodgeSection.res_self] using hex


open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Scalar cancellation after transport through a specified sheaf square. -/
lemma normalized_transport {S K : Type} [CommRing S] [Field K] [CharZero K]
    (ρ : S →+* K) (M N : (Base S).Modules) (Mt Nt : (Base K).Modules)
    (eM : (Scheme.Modules.pullback (baseMap S K ρ)).obj M ≅ Mt)
    (eN : (Scheme.Modules.pullback (baseMap S K ρ)).obj N ≅ Nt)
    (f : M ⟶ N) (g : Mt ⟶ Nt)
    (hsq : (Scheme.Modules.pullback (baseMap S K ρ)).map f ≫ eN.hom = eM.hom ≫ g)
    (α : Γ(M, ⊤)) (η : Γ(Mt, ⊤)) (ω : Γ(Nt, ⊤))
    (m : ℕ) (hm : 0 < m) (c : K) (v : S) (hv : ρ v = (m : K)⁻¹)
    (hα : transportSection (baseMap S K ρ) M Mt eM α = scalar K c • η)
    (hw : g.app ⊤ η = scalar K (m : K) • ω) :
    transportSection (baseMap S K ρ) N Nt eN (scalar S v • f.app ⊤ α) =
      scalar K c • ω := by
  rw [transportSection_smul, NormalizedSection.base_scalar, hv,
    transport_map _ M N Mt Nt eM eN f g hsq α, hα]
  exact cancel_degree (K := K) Mt Nt g η ω m hm c hw

set_option backward.isDefEq.respectTransparency true in
/-- Naturality and the exact degree weight evaluate the normalized pullback
through arbitrary actual source and target tests. -/
lemma normalized_test_formula_raw {S : Type} [CommRing S]
    (E T : EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] [CharZero K] (W Wt : WeierstrassCurve K)
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law K Wt)
    (ρ : S →+* K) (a : Curve K W ⟶ E.curve) (b : Curve K Wt ⟶ T.curve)
    (ha : IsPullback a (structureMap K W) E.projection (baseMap S K ρ))
    (hb : IsPullback b (structureMap K Wt) T.projection (baseMap S K ρ))
    (hao : origin K W ≫ a = baseMap S K ρ ≫ zero E)
    (hbo : origin K Wt ≫ b = baseMap S K ρ ≫ zero T)
    (han : ∀ n, G.schemeNsmul n ≫ a = a ≫ E.law.schemeNsmul n)
    (hbn : ∀ n, Gt.schemeNsmul n ≫ b = b ≫ T.law.schemeNsmul n)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt)
    (hψmap : a ≫ f.map = ψ ≫ b)
    (α : Γ(hodge T, ⊤)) (η : Γ(Hodge K Wt, ⊤)) (ω : Γ(Hodge K W, ⊤))
    (m : ℕ) (hm : 0 < m) (c : K) (v : S) (hv : ρ v = (m : K)⁻¹)
    (hα : transportSection (baseMap S K ρ) (hodge T) (Hodge K Wt)
      (comparison (⟨ρ,b,hb,hbo,hbn⟩ : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt)) α = scalar K c • η)
    (hweight : (PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
      ψ hψ (origin K W) (origin K Wt) hψo).app ⊤ η = scalar K (m : K) • ω) :
    transportSection (baseMap S K ρ) (hodge E) (Hodge K W)
      (comparison (⟨ρ,a,ha,hao,han⟩ : ArithmeticThetaOpenHodgeR0180.Test S E K W G)) (scalar S v • (familyHodgeMap f).app ⊤ α) = scalar K c • ω := by
  letI : Algebra S K := ρ.toAlgebra
  letI := E.smooth
  letI := T.smooth
  let Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G := ⟨ρ,a,ha,hao,han⟩
  let Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt := ⟨ρ,b,hb,hbo,hbn⟩
  let gK := PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
    ψ hψ (origin K W) (origin K Wt) hψo
  have hcomm : (Scheme.Modules.pullback (baseMap S K ρ)).map
      (familyHodgeMap f) ≫ (comparison Cs).hom = (comparison Ct).hom ≫ gK := by
    have hn := PeriodDifferential.pointMap_baseChange_naturality (A := S) (B := K)
      E.projection T.projection (structureMap K W) (structureMap K Wt)
      a b ha hb (zero E) (zero T) (origin K W) (origin K Wt) hao hbo
      f.map f.over_eq f.zero_eq ψ hψ hψo hψmap
    dsimp only [comparison, familyHodgeMap, PeriodDifferential.pointMap, Cs, Ct, gK] at hn ⊢
    exact hn
  exact normalized_transport (S := S) (K := K) ρ (hodge T) (hodge E)
    (Hodge K Wt) (Hodge K W) (comparison Ct) (comparison Cs)
    (familyHodgeMap f) gK hcomm α η ω m hm c v hv hα hweight

set_option backward.isDefEq.respectTransparency true in
lemma normalized_test_formula {S : Type} [CommRing S]
    (E T : EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] [CharZero K] (W Wt : WeierstrassCurve K)
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law K Wt)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt)
    (hscalar : Ct.scalar = Cs.scalar)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt)
    (hψmap : Cs.map ≫ f.map = ψ ≫ Ct.map)
    (α : Γ(hodge T, ⊤)) (η : Γ(Hodge K Wt, ⊤)) (ω : Γ(Hodge K W, ⊤))
    (m : ℕ) (hm : 0 < m) (c : K) (v : S) (hv : Cs.scalar v = (m : K)⁻¹)
    (hα : transportSection (baseMap S K Ct.scalar) (hodge T) (Hodge K Wt)
      (comparison Ct) α = scalar K c • η)
    (hweight : (PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
      ψ hψ (origin K W) (origin K Wt) hψo).app ⊤ η = scalar K (m : K) • ω) :
    transportSection (baseMap S K Cs.scalar) (hodge E) (Hodge K W)
      (comparison Cs) (scalar S v • (familyHodgeMap f).app ⊤ α) = scalar K c • ω := by
  rcases Cs with ⟨ρ,a,ha,hao,han⟩
  rcases Ct with ⟨ρt,b,hb,hbo,hbn⟩
  dsimp only [ArithmeticThetaOpenHodgeR0180.Test.scalar] at hscalar
  subst ρt
  exact normalized_test_formula_raw (S := S) E T f K W Wt G Gt ρ a b ha hb hao hbo han hbn
    ψ hψ hψo hψmap α η ω m hm c v hv hα hweight

/-- The source test is the original canonical marked Tate test. -/
def sourceTest (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring D.atlas.descent.family
      (LaurentSeries k) (TateCurve k L) V.level.law where
  scalar := (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom
  map := V.map
  cartesian := by
    have h : baseMap D.atlas.quotient.ring (LaurentSeries k)
        (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom =
        V.base ≫ D.quotient.inclusion := Spec.map_preimage _
    rw [h]
    exact V.classifies.2.1
  origin_eq := by
    have h : baseMap D.atlas.quotient.ring (LaurentSeries k)
        (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom =
        V.base ≫ D.quotient.inclusion := Spec.map_preimage _
    rw [h]
    exact V.classifies.2.2.1
  nsmul_eq := V.nsmul_eq

lemma source_test_transport (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (s : Γ(hodge D.atlas.descent.family, ⊤)) :
    (testIso k L V).hom.app ⊤
      (pullbackGlobalSection (V.base ≫ D.quotient.inclusion) (hodge D.atlas.descent.family) s) =
    transportSection (baseMap D.atlas.quotient.ring (LaurentSeries k) (sourceTest k L D V).scalar)
      (hodge D.atlas.descent.family) (Hodge (LaurentSeries k) (TateCurve k L))
      (comparison (sourceTest k L D V)) s := by
  let C := sourceTest k L D V
  have he : baseMap D.atlas.quotient.ring (LaurentSeries k) C.scalar =
      V.base ≫ D.quotient.inclusion := Spec.map_preimage _
  have heq := pullbackEqIso_section he.symm (hodge D.atlas.descent.family) ⊤ s ⊤
    (by simp) (by simp)
  simp only [Scheme.Hom.preimage_top, InitialHodgeSection.res_self] at heq
  change (comparison C).hom.app ⊤ ((pullbackEqIso he.symm _).hom.app ⊤
    (pullbackGlobalSection (V.base ≫ D.quotient.inclusion) _ s)) =
    transportSection (baseMap D.atlas.quotient.ring (LaurentSeries k) C.scalar)
      (hodge D.atlas.descent.family) (Hodge (LaurentSeries k) (TateCurve k L)) (comparison C) s
  simp only [transportSection, Scheme.Hom.preimage_top, InitialHodgeSection.res_self]
  simp only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection] at heq ⊢
  rw [heq]

end DesignatedExpansionProof
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
/-- Complete signed designated expansion of the same normalized section. -/
theorem isogeny_alpha_designated_expansion :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L),
    ∀ A : OpenAlpha k L m D, DesignatedExpansion k L m D A := by
  intro k _ _ _ L m hL hm _ hdiv D A V ζ hζ hcan
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨C⟩ := DesignatedExpansionProof.tate_comparison k L m hL hm hdiv D A.quotient V ζ hζ hcan
  have ha := DesignatedExpansionProof.comparison_alpha k L m hL hm hdiv D A V ζ hζ C
  let Cs := DesignatedExpansionProof.sourceTest k L D V
  have hv : Cs.scalar (algebraMap k D.atlas.quotient.ring (m : k)⁻¹) =
      (m : LaurentSeries k)⁻¹ := by
    change (Cs.scalar.comp (algebraMap k D.atlas.quotient.ring)) ((m : k)⁻¹) = _
    rw [map_inv₀, map_natCast]
  have h0 := DesignatedExpansionProof.normalized_test_formula
    (S := D.atlas.quotient.ring) D.atlas.descent.family A.quotient.target A.quotient.arrow (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k L)
    (ArithmeticThetaTateCuspsR0181.TateCurve k (L*m)) V.level.law C.law Cs C.test
    C.scalar_eq C.map C.over_eq C.zero_eq C.square
  have h1 := h0 A.alpha
    (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k (L*m) C.differential)
    (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential)
    m hm (algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m)^2))
    (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)
  have h2 := h1 hv
  have h3 := h2 ha
  have hw := C.weight
  -- Align the field-derived and direct Hahn-series ring instances without unfolding curves.
  have h := h3 (by with_reducible_and_instances exact hw)
  change (ArithmeticThetaBoundaryHodgeR0182.testIso k L V).hom.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (V.base ≫ D.quotient.inclusion)
      (ArithmeticThetaOpenHodgeR0180.hodge D.atlas.descent.family) (ambientAlpha k L m D A)) = _
  rw [DesignatedExpansionProof.source_test_transport k L D V (ambientAlpha k L m D A)]
  exact h

end ArithmeticThetaIsogenyHalfLinesR0193

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.cancel_degree
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.transport_map

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.tate_comparison

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.target_combination
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.lifted_combination

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.signed_alpha_of_labels

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.comparison_alpha

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.normalized_test_formula
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.source_test_transport
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.isogeny_alpha_designated_expansion

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.normalized_transport
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansionProof.normalized_test_formula_raw
