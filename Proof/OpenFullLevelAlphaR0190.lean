module

public import RelativeAlphaNaturalityR0190
public import GlobalFamilyTorsionValueR0180

@[expose] public section

/-! Descent of the intrinsic four-torsion Hodge frame to the actual marked family. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

section Marking
variable {S R : Type u} [CommRing S] [CommRing R]
  {E : EllipticFamily S} {W : WeierstrassCurve R} [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

include hG

/-- Pointed Cartesian comparison fixes the group law, with no multiplication
compatibility assumption added to a classifying chart. -/
lemma cartesian_law_eq (ρ : S →+* R) (f : Curve R W ⟶ E.curve)
    (hf : IsPullback f (structureMap R W) E.projection (baseMap S R ρ))
    (ho : origin R W ≫ f = baseMap S R ρ ≫ zero E) :
    toGRJ G = cartesianLaw hf E.law := by
  apply GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
    (BaseChange.geometry R W G)
  apply Subtype.ext
  apply hf.hom_ext
  · change (G.one (𝟙 _)).val ≫ f = _
    rw [hG.1, Category.id_comp, ho, cartesian_one, Category.id_comp]
    exact congrArg Subtype.val (E.law.one_natural (𝟙 _) (baseMap S R ρ)
      (baseMap S R ρ) (by simp))
  · exact (G.one (𝟙 _)).property.trans ((cartesianLaw hf E.law).one (𝟙 _)).property.symm

lemma cartesian_nsmul (ρ : S →+* R) (f : Curve R W ⟶ E.curve)
    (hf : IsPullback f (structureMap R W) E.projection (baseMap S R ρ))
    (ho : origin R W ≫ f = baseMap S R ρ ≫ zero E) (n : ℕ) :
    G.schemeNsmul n ≫ f = f ≫ E.law.schemeNsmul n := by
  have he := cartesian_law_eq G hG ρ f hf ho
  have hn {T : Scheme.{u}} (t : T ⟶ Base R)
      (P : SchemeHomOver t (structureMap R W)) (n : ℕ) :
      down hf (G.nsmul t n P) = E.law.nsmul _ n (down hf P) := by
    induction n with
    | zero =>
      change down hf ((toGRJ G).one t) = E.law.one _
      rw [he]; exact down_up hf _
    | succ n ih =>
      change down hf ((toGRJ G).mul t (G.nsmul t n P) P) = _
      rw [he]
      change down hf (up hf (E.law.mul _ _ _)) = _
      rw [down_up, ih]; rfl
  exact (congrArg Subtype.val (hn (structureMap R W)
    WeierstrassProjModel.RelativeGroupLaw.idPoint n)).trans (section_nsmul _ _ _ _)

def pointedTest (ρ : S →+* R) (f : Curve R W ⟶ E.curve)
    (hf : IsPullback f (structureMap R W) E.projection (baseMap S R ρ))
    (ho : origin R W ≫ f = baseMap S R ρ ≫ zero E) : Test S E R W G :=
  ⟨ρ, f, hf, ho, cartesian_nsmul G hG ρ f hf ho⟩

variable (C : Test S E R W G) {L : ℕ} (M : FamilyLevel S E L)

lemma test_down_one {T : Scheme.{u}} (t : T ⟶ Base R) :
    down C.cartesian (G.one t) = E.law.one (t ≫ baseMap S R C.scalar) := by
  change down C.cartesian ((toGRJ G).one t) = _
  rw [cartesian_law_eq G hG C.scalar C.map C.cartesian C.origin_eq]
  exact down_up _ _

lemma test_down_mul {T : Scheme.{u}} (t : T ⟶ Base R)
    (P Q : SchemeHomOver t (structureMap R W)) :
    down C.cartesian (G.mul t P Q) = E.law.mul _ (down C.cartesian P) (down C.cartesian Q) := by
  change down C.cartesian ((toGRJ G).mul t P Q) = _
  rw [cartesian_law_eq G hG C.scalar C.map C.cartesian C.origin_eq]
  exact down_up _ _

lemma test_down_nsmul {T : Scheme.{u}} (t : T ⟶ Base R)
    (P : SchemeHomOver t (structureMap R W)) (n : ℕ) :
    down C.cartesian (G.nsmul t n P) = E.law.nsmul _ n (down C.cartesian P) := by
  induction n with
  | zero => exact test_down_one G hG C t
  | succ n ih => rw [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ,
      test_down_mul G hG C, ih]; rfl

def liftMarkPoint (P : SchemeHomOver (𝟙 (Base S)) E.projection) :
    SchemeHomOver (𝟙 (Base R)) (structureMap R W) :=
  up C.cartesian ⟨baseMap S R C.scalar ≫ P.val, by simp [P.property]⟩

omit hG in
lemma liftMarkPoint_map (P : SchemeHomOver (𝟙 (Base S)) E.projection) :
    (liftMarkPoint G C P).val ≫ C.map = baseMap S R C.scalar ≫ P.val :=
  C.cartesian.lift_fst _ _ _

lemma liftMarkPoint_killed (P : SchemeHomOver (𝟙 (Base S)) E.projection)
    (hP : P.val ≫ E.law.schemeNsmul L = zero E) :
    G.nsmul (𝟙 _) L (liftMarkPoint G C P) = G.one (𝟙 _) := by
  apply Subtype.ext
  apply C.cartesian.hom_ext
  · rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.assoc, C.nsmul_eq, ← Category.assoc, liftMarkPoint_map,
      Category.assoc, hP, hG.1, Category.id_comp, C.origin_eq]
  · exact (G.nsmul (𝟙 _) L _).property.trans (G.one (𝟙 _)).property.symm

lemma liftMarkPoint_combination (i j : ℕ) :
    (G.mul (𝟙 _) (G.nsmul (𝟙 _) i (liftMarkPoint G C M.x))
      (G.nsmul (𝟙 _) j (liftMarkPoint G C M.y))).val ≫ C.map =
    baseMap S R C.scalar ≫ (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i M.x)
      (E.law.nsmul (𝟙 _) j M.y)).val := by
  have h := congrArg Subtype.val (test_down_mul G hG C (𝟙 _)
    (G.nsmul (𝟙 _) i (liftMarkPoint G C M.x)) (G.nsmul (𝟙 _) j (liftMarkPoint G C M.y)))
  rw [test_down_nsmul G hG C, test_down_nsmul G hG C] at h
  have hx : down C.cartesian (liftMarkPoint G C M.x) =
      GoodReductionJacobian.schemeHomOverComp (baseMap S R C.scalar)
        (show baseMap S R C.scalar ≫ 𝟙 _ = 𝟙 _ ≫ baseMap S R C.scalar by simp) M.x :=
    Subtype.ext (liftMarkPoint_map G C M.x)
  have hy : down C.cartesian (liftMarkPoint G C M.y) =
      GoodReductionJacobian.schemeHomOverComp (baseMap S R C.scalar)
        (show baseMap S R C.scalar ≫ 𝟙 _ = 𝟙 _ ≫ baseMap S R C.scalar by simp) M.y :=
    Subtype.ext (liftMarkPoint_map G C M.y)
  rw [hx, hy, ← E.law.nsmul_natural, ← E.law.nsmul_natural,
    ← E.law.mul_natural] at h
  exact h

def liftMarking : FullLevel R W G L (𝟙 (Base R)) where
  x := liftMarkPoint G C M.x
  y := liftMarkPoint G C M.y
  killed_x := liftMarkPoint_killed G hG C M.x M.killed_x
  killed_y := liftMarkPoint_killed G hG C M.y M.killed_y
  avoids i j hij := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx⟩ ⟨y,hy⟩
    have hdis := Set.disjoint_left.mp (M.avoids i j hij)
    apply hdis (a := C.map z)
    · refine ⟨baseMap S R C.scalar x, ?_⟩
      have h := congrArg (fun f : Base R ⟶ E.curve => f x)
        (liftMarkPoint_combination G hG C M i.val j.val)
      simpa only [Scheme.Hom.comp_apply, hx] using h.symm
    · refine ⟨baseMap S R C.scalar y, ?_⟩
      have h := congrArg (fun f : Base R ⟶ E.curve => f y) C.origin_eq
      simpa only [Scheme.Hom.comp_apply, hy] using h.symm

end Marking

section LocalSections
variable {S : Type u} [CommRing S] {E : EllipticFamily S} {L : ℕ}
  (M : FamilyLevel S E L) (hL : 0 < L) (h4 : 4 ∣ L)
  {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] {W : WeierstrassCurve R} [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G)

def localAlpha : Γ(Hodge R W, ⊤) :=
  (relative_alpha_naturality R W G hG L hL h4 (liftMarking G hG C M)).1.exists.choose

lemma localAlpha_spec :
    RealizesAlpha R W G L (liftMarking G hG C M) (localAlpha M hL h4 G hG C) ∧
    IsFrame (Hodge R W) ⊤ (localAlpha M hL h4 G hG C) :=
  (relative_alpha_naturality R W G hG L hL h4 (liftMarking G hG C M)).1.exists.choose_spec

variable {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
  [IsIntegrallyClosed T] [Algebra ℚ T] {Wt : WeierstrassCurve T} [Wt.IsElliptic]
  (Gt : Law T Wt) (hGt : IsOriginLaw T Wt Gt) (D : Test S E T Wt Gt)
  (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
  (hb : IsBaseChange R W G T Wt Gt ρ b) (hm : b ≫ C.map = D.map)
  (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar)

include hb hm hbase in
lemma liftMarkPoint_natural (P : SchemeHomOver (𝟙 (Base S)) E.projection) :
    (liftMarkPoint Gt D P).val ≫ b = baseMap R T ρ ≫ (liftMarkPoint G C P).val := by
  apply C.cartesian.hom_ext
  · rw [Category.assoc, hm, liftMarkPoint_map, Category.assoc, liftMarkPoint_map,
      ← Category.assoc, ← hbase]
  · rw [Category.assoc, hb.1.w, ← Category.assoc, (liftMarkPoint Gt D P).property,
      Category.id_comp, Category.assoc, (liftMarkPoint G C P).property, Category.comp_id]
    rfl

include hm hbase in
lemma localAlpha_natural :
    pullAlpha R W G T Wt Gt ρ b hb (localAlpha M hL h4 G hG C) =
      localAlpha M hL h4 Gt hGt D := by
  apply (relative_alpha_naturality R W G hG L hL h4 (liftMarking G hG C M)).2
    T Wt Gt hGt (liftMarking Gt hGt D M) ρ b hb
  · exact liftMarkPoint_natural G C Gt D ρ b hb hm hbase M.x
  · exact liftMarkPoint_natural G C Gt D ρ b hb hm hbase M.y
  · exact (localAlpha_spec M hL h4 G hG C).1
  · exact (localAlpha_spec M hL h4 Gt hGt D).1

end LocalSections

section Comparisons
variable {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
  {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
  {G : Law R W} {Gt : Law T Wt}

def familyDifferential (E : EllipticFamily S) (U : E.curve.Opens) (a : Γ(E.curve,U)) :
    Γ(hodge E, zero E ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection (zero E)
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD E.projection U a)

lemma comparison_D (C : Test S E R W G) (U : E.curve.Opens) (a : Γ(E.curve,U))
    (V : (Base R).Opens) (h₁ : V ≤ baseMap S R C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    res (Hodge R W) h₁ ((comparison C).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) (familyDifferential E U a))) =
    res (Hodge R W) h₂ (localDifferential R W (C.map ⁻¹ᵁ U) (C.map.app U a)) := by
  letI : Algebra S R := C.scalar.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso_D E.projection (structureMap R W) C.map C.cartesian
    (zero E) (origin R W) C.origin_eq U a V h₁ h₂

lemma differential_map_congr {X : Scheme.{u}} (f g : Curve T Wt ⟶ X) (he : f = g)
    (U : X.Opens) (a : Γ(X,U)) (V : (Base T).Opens)
    (hf : V ≤ origin T Wt ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : V ≤ origin T Wt ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    res (Hodge T Wt) hf (localDifferential T Wt (f ⁻¹ᵁ U) (f.app U a)) =
      res (Hodge T Wt) hg (localDifferential T Wt (g ⁻¹ᵁ U) (g.app U a)) := by
  subst g
  rfl

lemma comparison_comp [IsDomain R] [IsDomain T] [W.IsElliptic]
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : IsBaseChange R W G T Wt Gt ρ b) (hm : b ≫ C.map = D.map)
    (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar) :
    comparison D = composeComparison (baseMap S R C.scalar) (baseMap R T ρ)
      (baseMap S T D.scalar) hbase (hodge E) (Hodge R W) (Hodge T Wt)
      (comparison C) (hodgeIso R W G T Wt Gt ρ b hb) := by
  have hf : ∀ t : Base S, ∃ (U : E.curve.Opens) (a : Γ(E.curve,U)),
      zero E t ∈ U ∧ IsFrame (hodge E) (zero E ⁻¹ᵁ U) (familyDifferential E U a) := by
    letI := E.smooth
    intro t
    obtain ⟨U,a,ht,hf⟩ := exists_exact_differential_frame E.projection (zero E t)
    exact ⟨U,a,ht,pullback_frame _ _ _ hf⟩
  apply RelativeAlphaNaturality.local_comparison_comp (zero E) (origin R W) (origin T Wt)
    (baseMap S R C.scalar) (baseMap R T ρ) (baseMap S T D.scalar) hbase C.map b
    C.origin_eq hb.2.1 (by rw [hm]; exact D.origin_eq)
    (hodge E) (Hodge R W) (Hodge T Wt) (familyDifferential E)
    (localDifferential R W) (localDifferential T Wt) hf
    (comparison C) (hodgeIso R W G T Wt Gt ρ b hb) (comparison D)
    (comparison_D C) (hodgeIso_D R W G T Wt Gt ρ b hb)
  intro U a V ha hd
  have hd' : V ≤ origin T Wt ⁻¹ᵁ (D.map ⁻¹ᵁ U) := by simpa only [hm] using hd
  exact (comparison_D D U a V ha hd').trans
    (differential_map_congr (b ≫ C.map) D.map hm U a V hd hd').symm

def alphaPull (C : Test S E R W G) (U : (Base S).Opens) (V : (Base R).Opens)
    (h : V ≤ baseMap S R C.scalar ⁻¹ᵁ U) (s : Γ(hodge E,U)) : Γ(Hodge R W,V) :=
  res _ h ((comparison C).hom.app _
    (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))

lemma alphaPull_restrict (C : Test S E R W G) (U U' : (Base S).Opens) (hU : U' ≤ U)
    (V : (Base R).Opens) (h : V ≤ baseMap S R C.scalar ⁻¹ᵁ U') (s : Γ(hodge E,U)) :
    alphaPull C U' V h (res (hodge E) hU s) =
      alphaPull C U V (h.trans (fun _ hx => hU hx)) s := by
  unfold alphaPull
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

lemma alphaPull_refinement [IsDomain R] [IsDomain T] [W.IsElliptic]
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : IsBaseChange R W G T Wt Gt ρ b) (hm : b ≫ C.map = D.map)
    (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar)
    (U : (Base S).Opens) (V : (Base R).Opens) (Z : (Base T).Opens)
    (hC : V ≤ baseMap S R C.scalar ⁻¹ᵁ U)
    (hT : Z ≤ baseMap R T ρ ⁻¹ᵁ V) (hD : Z ≤ baseMap S T D.scalar ⁻¹ᵁ U)
    (s : Γ(hodge E,U)) :
    alphaPull D U Z hD s = res (Hodge T Wt) hT
      ((hodgeIso R W G T Wt Gt ρ b hb).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap R T ρ) (alphaPull C U V hC s))) := by
  unfold alphaPull
  rw [comparison_comp C D ρ b hb hm hbase]
  rw [composeComparison_section _ _ _ _ _ _ _ _ _ U s Z hD (fun z hz => hC (hT hz))]
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

end Comparisons

section Gluing
variable {S : Type u} [CommRing S] {E : EllipticFamily S} {L : ℕ}
  (M : FamilyLevel S E L) (hL : 0 < L) (h4 : 4 ∣ L)

lemma alphaChart_exists (C : Chart S E) :
    ∃ s : Γ(hodge E, chartOpen C), IsFrame (hodge E) (chartOpen C) s ∧
      alphaPull C.comparison (chartOpen C) ⊤ (chart_preimage C) s =
        localAlpha M hL h4 C.law C.originLaw C.comparison := by
  letI := C.openImmersion
  exact frame_lift_open (baseMap S C.ring C.comparison.scalar) (hodge E)
    (Hodge C.ring C.equation) (comparison C.comparison)
    (localAlpha M hL h4 C.law C.originLaw C.comparison)
    (localAlpha_spec M hL h4 C.law C.originLaw C.comparison).2

def alphaChartSection (C : Chart S E) : Γ(hodge E,chartOpen C) :=
  (alphaChart_exists M hL h4 C).choose

lemma alphaChart_frame (C : Chart S E) :
    IsFrame (hodge E) (chartOpen C) (alphaChartSection M hL h4 C) :=
  (alphaChart_exists M hL h4 C).choose_spec.1

lemma alphaChart_pull (C : Chart S E) :
    alphaPull C.comparison (chartOpen C) ⊤ (chart_preimage C) (alphaChartSection M hL h4 C) =
      localAlpha M hL h4 C.law C.originLaw C.comparison :=
  (alphaChart_exists M hL h4 C).choose_spec.2

lemma alphaChart_test {T : Type u} [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Algebra ℚ T]
    (C : Chart S E) (Wt : WeierstrassCurve T) [Wt.IsElliptic]
    (Gt : Law T Wt) (hGt : IsOriginLaw T Wt Gt) (D : Test S E T Wt Gt)
    (ρ : C.ring →+* T) (hρ : ρ.comp C.comparison.scalar = D.scalar)
    (hD : (⊤ : (Base T).Opens) ≤ baseMap S T D.scalar ⁻¹ᵁ chartOpen C) :
    alphaPull D (chartOpen C) ⊤ hD (alphaChartSection M hL h4 C) =
      localAlpha M hL h4 Gt hGt D := by
  obtain ⟨b, hm, hb⟩ := test_refinement C.comparison D ρ hρ
  have hbase : baseMap S T D.scalar =
      baseMap C.ring T ρ ≫ baseMap S C.ring C.comparison.scalar := by
    rw [← hρ]
    exact Spec.map_comp (CommRingCat.ofHom C.comparison.scalar) (CommRingCat.ofHom ρ)
  rw [alphaPull_refinement C.comparison D ρ b hb hm hbase (chartOpen C) ⊤ ⊤
    (chart_preimage C) (by simp) hD, alphaChart_pull, res_refl]
  have hh := localAlpha_natural M hL h4 C.law C.originLaw C.comparison Gt hGt D ρ b hb hm hbase
  simpa only [pullAlpha, RelativeAlphaNaturality.hodge_comparison_eq,
    pullbackGlobalSection, Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top, res_refl] using hh

lemma alpha_res_eq_of_pull_eq {R : Type u} [CommRing R]
    {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G)
    [IsOpenImmersion (baseMap S R C.scalar)]
    (U : (Base S).Opens) (hU : (baseMap S R C.scalar).opensRange ≤ U)
    (h : (⊤ : (Base R).Opens) ≤ baseMap S R C.scalar ⁻¹ᵁ U)
    (s t : Γ(hodge E,U)) (he : alphaPull C U ⊤ h s = alphaPull C U ⊤ h t) :
    res (hodge E) hU s = res (hodge E) hU t := by
  have hp : Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s =
      Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) t := by
    apply (ConcreteCategory.bijective_of_isIso ((comparison C).hom.app _)).1
    exact (res_bijective _ h le_top).1 he
  exact restriction_eq_of_pullback_eq (baseMap S R C.scalar) (hodge E) U hU s t hp

lemma alphaChart_overlap
    (C D : Chart S E) :
    res (hodge E) (inf_le_left : chartOpen C ⊓ chartOpen D ≤ chartOpen C) (alphaChartSection M hL h4 C) =
      res (hodge E) (inf_le_right : chartOpen C ⊓ chartOpen D ≤ chartOpen D) (alphaChartSection M hL h4 D) := by
  apply sections_eq_local
  intro x hx
  letI := C.openImmersion
  letI := D.openImmersion
  obtain ⟨y, hy⟩ := hx.1
  let U := baseMap S C.ring C.comparison.scalar ⁻¹ᵁ chartOpen D
  have hyU : y ∈ U := by change baseMap S C.ring C.comparison.scalar y ∈ chartOpen D; rw [hy]; exact hx.2
  let N := Classical.choice (normal_affine_neighborhood C.ring U y hyU)
  letI := N.openImmersion
  obtain ⟨Gt, hGt, Z, hZ, b, hbmap, hb⟩ := test_base_change C.comparison C.originLaw N.scalar
  let Wt := C.equation.map N.scalar
  have hZbase : baseMap S N.ring Z.scalar =
      baseMap C.ring N.ring N.scalar ≫ baseMap S C.ring C.comparison.scalar := by
    rw [hZ]
    exact Spec.map_comp (CommRingCat.ofHom C.comparison.scalar) (CommRingCat.ofHom N.scalar)
  letI : IsOpenImmersion (baseMap S N.ring Z.scalar) := by rw [hZbase]; infer_instance
  have hC : (⊤ : (Base N.ring).Opens) ≤ baseMap S N.ring Z.scalar ⁻¹ᵁ chartOpen C := by
    intro z _
    change baseMap S N.ring Z.scalar z ∈ chartOpen C
    rw [hZbase]
    exact ⟨baseMap C.ring N.ring N.scalar z, rfl⟩
  have hD : (⊤ : (Base N.ring).Opens) ≤ baseMap S N.ring Z.scalar ⁻¹ᵁ chartOpen D := by
    intro z _
    change baseMap S N.ring Z.scalar z ∈ chartOpen D
    rw [hZbase]
    exact N.inside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := scalar_factor_open D.comparison.scalar Z.scalar (by
    rintro _ ⟨z, rfl⟩
    exact hD (Set.mem_univ z))
  have hgeom := relative_curve_geometry N.ring Wt
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  have hcs := alphaChart_test M hL h4 C Wt Gt hGt Z N.scalar hZ.symm hC
  have hds := alphaChart_test M hL h4 D Wt Gt hGt Z τ hτ hD
  have hU : (baseMap S N.ring Z.scalar).opensRange ≤ chartOpen C ⊓ chartOpen D := by
    rintro _ ⟨z, rfl⟩
    exact ⟨hC (Set.mem_univ z), hD (Set.mem_univ z)⟩
  have hUZ : (⊤ : (Base N.ring).Opens) ≤
      baseMap S N.ring Z.scalar ⁻¹ᵁ (chartOpen C ⊓ chartOpen D) := by
    intro z _
    exact ⟨hC (Set.mem_univ z), hD (Set.mem_univ z)⟩
  refine ⟨(baseMap S N.ring Z.scalar).opensRange, ?_, hU, ?_⟩
  · obtain ⟨z, hz⟩ := N.contains
    refine ⟨z, ?_⟩
    rw [hZbase]
    change baseMap S C.ring C.comparison.scalar (baseMap C.ring N.ring N.scalar z) = x
    rw [hz, hy]
  · apply alpha_res_eq_of_pull_eq Z _ hU hUZ
    rw [alphaPull_restrict, alphaPull_restrict]
    exact hcs.trans hds.symm

lemma glue_alpha_sections (A : Atlas S E) :
    ∃ d : Γ(hodge E, ⊤), IsFrame (hodge E) ⊤ d ∧
      ∀ i, res (hodge E) le_top d = alphaChartSection M hL h4 (A.chart i) := by
  let U := fun i => chartOpen (A.chart i)
  have hc : (⨆ i, U i) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (A.covers x)
  obtain ⟨d, hd, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(hodge E).presheaf, (hodge E).isSheaf⟩ U ⊤ (fun _ => homOfLE le_top)
    hc.ge (fun i => alphaChartSection M hL h4 (A.chart i)) (fun i j => alphaChart_overlap M hL h4 _ _)
  refine ⟨d, ?_, hd⟩
  apply frame_glue_cover _ U hc d
  intro i
  change IsFrame (hodge E) (U i) ((hodge E).presheaf.map (homOfLE le_top).op d)
  rw [hd i]
  exact alphaChart_frame M hL h4 _

lemma glued_alpha_test (A : Atlas S E)
    (d : Γ(hodge E, ⊤))
    (hd : ∀ i, res (hodge E) le_top d = alphaChartSection M hL h4 (A.chart i))
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G) :
    alphaPull C ⊤ ⊤ (by simp) d = localAlpha M hL h4 G hG C := by
  apply sections_eq_local
  intro x _
  obtain ⟨i, hi⟩ := A.covers (baseMap S R C.scalar x)
  let D := A.chart i
  letI := D.openImmersion
  let U := baseMap S R C.scalar ⁻¹ᵁ chartOpen D
  have hxU : x ∈ U := hi
  let N := Classical.choice (normal_affine_neighborhood R U x hxU)
  letI := N.openImmersion
  obtain ⟨Gt, hGt, Z, hZ, b, hbmap, hb⟩ := test_base_change C hG N.scalar
  have hZbase : baseMap S N.ring Z.scalar = baseMap R N.ring N.scalar ≫ baseMap S R C.scalar := by
    rw [hZ]
    exact Spec.map_comp (CommRingCat.ofHom C.scalar) (CommRingCat.ofHom N.scalar)
  have hDZ : (⊤ : (Base N.ring).Opens) ≤ baseMap S N.ring Z.scalar ⁻¹ᵁ chartOpen D := by
    intro z _
    change baseMap S N.ring Z.scalar z ∈ chartOpen D
    rw [hZbase]
    exact N.inside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := scalar_factor_open D.comparison.scalar Z.scalar (by
    rintro _ ⟨z, rfl⟩
    exact hDZ (Set.mem_univ z))
  have hgeom := relative_curve_geometry N.ring (W.map N.scalar)
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  have hchart := alphaChart_test M hL h4 D (W.map N.scalar) Gt hGt Z τ hτ hDZ
  have hglobal : alphaPull Z ⊤ ⊤ (by simp) d = localAlpha M hL h4 Gt hGt Z := by
    rw [← alphaPull_restrict Z ⊤ (chartOpen D) le_top ⊤ hDZ d, hd i]
    exact hchart
  have htransport := alphaPull_refinement C Z N.scalar b hb hbmap hZbase
    ⊤ ⊤ ⊤ (by simp) (by simp) (by simp) d
  have hnat := localAlpha_natural M hL h4 G hG C Gt hGt Z N.scalar b hb hbmap hZbase
  simp only [pullAlpha, RelativeAlphaNaturality.hodge_comparison_eq, pullbackGlobalSection] at hnat
  have hp : Scheme.Modules.pullbackLocalSection (baseMap R N.ring N.scalar) (alphaPull C ⊤ ⊤ (by simp) d) =
      Scheme.Modules.pullbackLocalSection (baseMap R N.ring N.scalar) (localAlpha M hL h4 G hG C) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((hodgeIso R W G N.ring (W.map N.scalar) Gt N.scalar b hb).hom.app
        (baseMap R N.ring N.scalar ⁻¹ᵁ ⊤))).1
    have hfirst := htransport.symm.trans hglobal
    simp only [res_refl] at hfirst
    exact hfirst.trans hnat.symm
  refine ⟨(baseMap R N.ring N.scalar).opensRange, N.contains, le_top, ?_⟩
  exact restriction_eq_of_pullback_eq (baseMap R N.ring N.scalar) (Hodge R W)
    ⊤ le_top _ _ hp

end Gluing

section OpenBase
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCompatibleLevelR0178
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L)

/-- Every point of the actual compatible quotient admits a normal affine
classifying neighborhood of the same descended marked family. -/
structure ClassifyingChart (x : OpenBase k L D) where
  ring : Type
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  [algebra : Algebra k ring]
  equation : WeierstrassCurve ring
  [elliptic : equation.IsElliptic]
  law : Law ring equation
  originLaw : IsOriginLaw ring equation law
  marking : FullLevel ring equation law L (𝟙 (Base ring))
  base : Base ring ⟶ OpenBase k L D
  map : Curve ring equation ⟶ D.atlas.descent.family.curve
  classifies : Classifies k L D.atlas D.two D.cover D.quotient
    ring equation law marking base map
  openImmersion : IsOpenImmersion base
  contains : x ∈ Set.range base
attribute [instance] ClassifyingChart.commRing ClassifyingChart.domain ClassifyingChart.noetherian
  ClassifyingChart.normal ClassifyingChart.rational ClassifyingChart.algebra ClassifyingChart.elliptic

lemma classifying_chart (x : OpenBase k L D) : Nonempty (ClassifyingChart k L D x) := by
  let S := D.atlas.quotient.ring
  let E := D.atlas.descent.family
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k S D.atlas.quotient.smooth E
  obtain ⟨i,hi⟩ := A.covers (D.quotient.inclusion x)
  let C := A.chart i
  letI := C.openImmersion
  letI := D.quotient.openImmersion
  obtain ⟨y,hy⟩ := hi
  let U := baseMap S C.ring C.comparison.scalar ⁻¹ᵁ D.quotient.inclusion.opensRange
  have hyU : y ∈ U := by
    change baseMap S C.ring C.comparison.scalar y ∈ D.quotient.inclusion.opensRange
    rw [hy]
    exact ⟨x,rfl⟩
  let N := Classical.choice (normal_affine_neighborhood C.ring U y hyU)
  letI := N.openImmersion
  obtain ⟨Gt,hGt,Z,hZ,c,hc,hbc⟩ := test_base_change C.comparison C.originLaw N.scalar
  have hZbase : baseMap S N.ring Z.scalar =
      baseMap C.ring N.ring N.scalar ≫ baseMap S C.ring C.comparison.scalar := by
    rw [hZ]
    exact Spec.map_comp (CommRingCat.ofHom C.comparison.scalar) (CommRingCat.ofHom N.scalar)
  letI : IsOpenImmersion (baseMap S N.ring Z.scalar) := by rw [hZbase]; infer_instance
  have hinside : Set.range (baseMap S N.ring Z.scalar) ⊆ Set.range D.quotient.inclusion := by
    rintro _ ⟨z,rfl⟩
    rw [hZbase]
    exact N.inside ⟨z,rfl⟩
  let b := IsOpenImmersion.lift D.quotient.inclusion (baseMap S N.ring Z.scalar) hinside
  have hb : b ≫ D.quotient.inclusion = baseMap S N.ring Z.scalar :=
    IsOpenImmersion.lift_fac _ _ _
  letI : IsOpenImmersion b := by
    apply IsOpenImmersion.of_comp b D.quotient.inclusion
  letI : Algebra k N.ring := (Z.scalar.comp (algebraMap k S)).toAlgebra
  have hclass : Classifies k L D.atlas D.two D.cover D.quotient N.ring
      (C.equation.map N.scalar) Gt (liftMarking Gt hGt Z D.atlas.marking) b Z.map := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← D.quotient.over_eq, ← Category.assoc, hb]
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k S)) (CommRingCat.ofHom Z.scalar)).symm
    · rw [hb]; exact Z.cartesian
    · rw [hb]; exact Z.origin_eq
    · rw [hb]; exact liftMarkPoint_map Gt Z D.atlas.marking.x
    · rw [hb]; exact liftMarkPoint_map Gt Z D.atlas.marking.y
  refine ⟨⟨N.ring,C.equation.map N.scalar,Gt,hGt,liftMarking Gt hGt Z D.atlas.marking,
    b,Z.map,hclass,inferInstance,?_⟩⟩
  obtain ⟨z,hz⟩ := N.contains
  refine ⟨z,?_⟩
  apply D.quotient.inclusion.isOpenEmbedding.injective
  change (b ≫ D.quotient.inclusion) z = D.quotient.inclusion x
  rw [hb,hZbase]
  change baseMap S C.ring C.comparison.scalar (baseMap C.ring N.ring N.scalar z) = _
  rw [hz,hy]

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
  (M : FullLevel R W G L (𝟙 (Base R)))
  (b : Base R ⟶ OpenBase k L D) (f : Curve R W ⟶ D.atlas.descent.family.curve)
  (hf : Classifies k L D.atlas D.two D.cover D.quotient R W G M b f)

def classifyingTest : Test D.atlas.quotient.ring D.atlas.descent.family R W G := by
  let ρ : D.atlas.quotient.ring →+* R := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have hρ : baseMap D.atlas.quotient.ring R ρ = b ≫ D.quotient.inclusion := Spec.map_preimage _
  exact pointedTest G hG ρ f (by rw [hρ]; exact hf.2.1) (by rw [hρ]; exact hf.2.2.1)

lemma classifying_marking : liftMarking G hG (classifyingTest k L D W G hG M b f hf)
    D.atlas.marking = M := by
  have hρ : baseMap D.atlas.quotient.ring R (classifyingTest k L D W G hG M b f hf).scalar =
      b ≫ D.quotient.inclusion := Spec.map_preimage _
  have hx : liftMarkPoint G (classifyingTest k L D W G hG M b f hf) D.atlas.marking.x = M.x := by
    apply Subtype.ext
    apply hf.2.1.hom_ext
    · exact (liftMarkPoint_map G _ _).trans (by rw [hρ]; exact hf.2.2.2.1.symm)
    · exact (liftMarkPoint G _ _).property.trans M.x.property.symm
  have hy : liftMarkPoint G (classifyingTest k L D W G hG M b f hf) D.atlas.marking.y = M.y := by
    apply Subtype.ext
    apply hf.2.1.hom_ext
    · exact (liftMarkPoint_map G _ _).trans (by rw [hρ]; exact hf.2.2.2.2.symm)
    · exact (liftMarkPoint G _ _).property.trans M.y.property.symm
  have hext (A B : FullLevel R W G L (𝟙 (Base R))) (hx : A.x = B.x) (hy : A.y = B.y) : A = B := by
    cases A
    cases B
    cases hx
    cases hy
    rfl
  exact hext _ _ hx hy

lemma open_pull_ambient (a : Γ(hodge D.atlas.descent.family,⊤)) :
    pullOpenAlpha L k D R W G M b f hf
      (pullbackGlobalSection D.quotient.inclusion (hodge D.atlas.descent.family) a) =
    alphaPull (classifyingTest k L D W G hG M b f hf) ⊤ ⊤ (by simp) a := by
  let C := classifyingTest k L D W G hG M b f hf
  have he : baseMap D.atlas.quotient.ring R C.scalar = b ≫ D.quotient.inclusion := Spec.map_preimage _
  have hcomp := pullbackComp_hom_section b D.quotient.inclusion (hodge D.atlas.descent.family) ⊤ a
  have heq := pullbackEqIso_section he.symm (hodge D.atlas.descent.family) ⊤ a ⊤ (by simp) (by simp)
  simp only [Scheme.Hom.preimage_top, res_refl] at hcomp heq
  unfold pullOpenAlpha openComparison
  change (comparison C).hom.app ⊤ ((pullbackEqIso he.symm _).hom.app ⊤
    (((Scheme.Modules.pullbackComp b D.quotient.inclusion).app _).hom.app ⊤
      (pullbackGlobalSection b _ (pullbackGlobalSection D.quotient.inclusion _ a)))) = _
  simp only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection] at hcomp heq ⊢
  rw [hcomp, heq]
  simp only [alphaPull, Scheme.Hom.preimage_top, res_refl, Scheme.Modules.pullbackLocalSection, C]

end OpenBase

section Conclusion
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
  (D : LevelData k L)

include hL h4 in
lemma open_alpha_exists : ∃ a : Γ(openHodge k L D,⊤), IsOpenAlpha L k D a := by
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k D.atlas.quotient.ring
    D.atlas.quotient.smooth D.atlas.descent.family
  obtain ⟨a,ha,hat⟩ := glue_alpha_sections D.atlas.marking hL h4 A
  refine ⟨pullbackGlobalSection D.quotient.inclusion (hodge D.atlas.descent.family) a, ?_, ?_⟩
  · simpa only [openHodge, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
      Scheme.Hom.preimage_top] using (pullback_frame D.quotient.inclusion _ a ha)
  · intro R _ _ _ _ _ _ W _ G hG M b f hf
    rw [open_pull_ambient k L D W G hG M b f hf a]
    let C := classifyingTest k L D W G hG M b f hf
    have hgeom := relative_curve_geometry R W
    letI := hgeom.1
    letI := hgeom.2.1
    letI := hgeom.2.2.2.1
    letI := hgeom.2.2.2.2.1
    rw [glued_alpha_test D.atlas.marking hL h4 A a hat R W G hG C]
    have hh := (localAlpha_spec D.atlas.marking hL h4 G hG C).1
    simpa only [C, classifying_marking] using hh

lemma open_alpha_unique (a a' : Γ(openHodge k L D,⊤))
    (ha : IsOpenAlpha L k D a) (ha' : IsOpenAlpha L k D a') : a = a' := by
  apply sections_eq_local
  intro x _
  obtain ⟨C⟩ := classifying_chart k L D x
  letI := C.openImmersion
  have he := RelativeAlphaNaturality.realizes_unique C.ring C.equation C.law L C.marking
    (ha.2 C.ring C.equation C.law C.originLaw C.marking C.base C.map C.classifies)
    (ha'.2 C.ring C.equation C.law C.originLaw C.marking C.base C.map C.classifies)
  have hp : pullbackGlobalSection C.base (openHodge k L D) a =
      pullbackGlobalSection C.base (openHodge k L D) a' :=
    (ConcreteCategory.bijective_of_isIso
      ((openComparison L k D C.ring C.equation C.law C.marking C.base C.map C.classifies).hom.app ⊤)).1 he
  refine ⟨C.base.opensRange,C.contains,le_top,?_⟩
  apply restriction_eq_of_pullback_eq C.base (openHodge k L D) ⊤ le_top
  simpa only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top] using hp

end Conclusion
end ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha

namespace ArithmeticThetaGlobalFourTorsionR0190
/-- The intrinsic four-torsion formula descends to a unique frame of the actual
open Hodge sheaf, tested along every specified normal affine classifying map. -/
theorem open_full_level_alpha :
∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 0 < L → 4 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∃! a : (ArithmeticThetaBoundaryHodgeR0182.openHodge k L D).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.IsOpenAlpha L k D a := by
  intro k _ _ L hL h4 D
  obtain ⟨a,ha⟩ := OpenFullLevelAlpha.open_alpha_exists k L hL h4 D
  exact ⟨a,ha,fun a' ha' => OpenFullLevelAlpha.open_alpha_unique k L D a' a ha' ha⟩
end ArithmeticThetaGlobalFourTorsionR0190
#print axioms ArithmeticThetaGlobalFourTorsionR0190.open_full_level_alpha
