module

public import MarkedAffineTestComparisonR0215
public import ArbitraryAlphaNaturalityR0214
public import SchemeCotangentCoherenceR0205

@[expose] public section

/-! Construction of the intrinsic signed alpha on marked affine tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemeAlphaSection
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- The unique inclusion-compatible identity-ideal comparison. -/
def idealIso (P : AffineTest E M) :=
  (MarkedAffineTestComparison.ideal_comparison E M P).choose

lemma idealIso_compatible (P : AffineTest E M) :
    AffineIdealCompatible E M P (idealIso E M P) :=
  (MarkedAffineTestComparison.ideal_comparison E M P).choose_spec.1

def hodgeIso (P : AffineTest E M) :
    (Scheme.Modules.pullback P.base).obj (Cotangent E) ≅ Hodge P.ring P.equation := by
  letI := MarkedAffineTestComparison.hodge_isIso E M P (idealIso E M P)
  exact asIso (affineHodgeMap E M P (idealIso E M P))

/-- The accepted signed affine alpha, with no choice of its sign. -/
lemma affine_exists_unique (P : AffineTest E M) :
    ∃! a : Γ(Hodge P.ring P.equation, ⊤),
      ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha
        P.ring P.equation P.law 4 P.level a ∧
      IsFrame (Hodge P.ring P.equation) ⊤ a := by
  letI := P.elliptic
  exact ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.exists_unique_alpha
    P.ring P.equation P.law 4 P.level P.originLaw (by decide) (by decide)

def localAlpha (P : AffineTest E M) : Γ(Hodge P.ring P.equation, ⊤) :=
  (affine_exists_unique E M P).choose

lemma localAlpha_realizes (P : AffineTest E M) :
    ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha
      P.ring P.equation P.law 4 P.level (localAlpha E M P) :=
  (affine_exists_unique E M P).choose_spec.1.1

lemma localAlpha_frame (P : AffineTest E M) :
    IsFrame (Hodge P.ring P.equation) ⊤ (localAlpha E M P) :=
  (affine_exists_unique E M P).choose_spec.1.2

/-- Each open test supplies a frame on its actual image in the base. -/
lemma chart_section_exists (P : AffineTest E M) [IsOpenImmersion P.base] :
    ∃ s : Γ(Cotangent E, P.base.opensRange),
      IsFrame (Cotangent E) P.base.opensRange s ∧
      res (Hodge P.ring P.equation) (by rw [P.base.preimage_opensRange])
        ((hodgeIso E M P).hom.app _ (Scheme.Modules.pullbackLocalSection P.base s)) =
        localAlpha E M P :=
  frame_lift_open P.base (Cotangent E) (Hodge P.ring P.equation)
    (hodgeIso E M P) (localAlpha E M P) (localAlpha_frame E M P)

/-- The all-test condition is equivalent to equality with the fixed affine alpha.
Uniqueness of ideal comparisons removes the apparent choice in this criterion. -/
lemma realizes_iff (a : Γ(Cotangent E, ⊤)) :
    RealizesAlpha E M a ↔ ∀ P : AffineTest E M,
      affineAlpha E M P (idealIso E M P) a = localAlpha E M P := by
  constructor
  · intro ha P
    letI := P.elliptic
    exact ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.realizes_unique
      P.ring P.equation P.law 4 P.level
      ((ha P).2 _ (idealIso_compatible E M P)) (localAlpha_realizes E M P)
  · intro ha P
    refine ⟨⟨idealIso E M P, idealIso_compatible E M P⟩, ?_⟩
    intro i hi
    have he : i = idealIso E M P :=
      (MarkedAffineTestComparison.ideal_comparison E M P).choose_spec.2 i hi
    rw [he, ha P]
    exact localAlpha_realizes E M P

/-- Realization determines a global section, including over an empty base. -/
lemma realizes_unique (k : Type u) [Field k] [CharZero k] (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    {a b : Γ(Cotangent E, ⊤)} (ha : RealizesAlpha E M a) (hb : RealizesAlpha E M b) :
    a = b := by
  let P : S → AffineTest E M := fun s =>
    (MarkedAffineTestComparison.coverage E M k σ s).choose
  have ho : ∀ s, IsOpenImmersion (P s).base := fun s =>
    (MarkedAffineTestComparison.coverage E M k σ s).choose_spec.1
  apply sections_ext_cover (fun s => ArithmeticThetaLocalWeierstrassR0203.Base (P s).ring) (fun s => (P s).base) ho
    (fun s => ⟨s, (MarkedAffineTestComparison.coverage E M k σ s).choose_spec.2⟩)
    (Cotangent E) a b
  intro s
  apply (ConcreteCategory.bijective_of_isIso ((hodgeIso E M (P s)).hom.app ⊤)).1
  exact ((realizes_iff E M a).mp ha (P s)).trans
    ((realizes_iff E M b).mp hb (P s)).symm

/-- The frame property descends from the actual affine comparisons on an open cover. -/
lemma realizes_frame (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (a : Γ(Cotangent E, ⊤)) (ha : RealizesAlpha E M a) :
    IsFrame (Cotangent E) ⊤ a := by
  let P : S → AffineTest E M := fun s =>
    (MarkedAffineTestComparison.coverage E M k σ s).choose
  letI (s : S) : IsOpenImmersion (P s).base :=
    (MarkedAffineTestComparison.coverage E M k σ s).choose_spec.1
  have hc : (⨆ s, (P s).base.opensRange) = ⊤ := by
    apply top_unique
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨s, (MarkedAffineTestComparison.coverage E M k σ s).choose_spec.2⟩
  apply frame_glue_cover (Cotangent E) (fun s => (P s).base.opensRange) hc a
  intro s
  apply frame_of_pullback_open (P s).base (Cotangent E) (P s).base.opensRange le_rfl
  have hf : IsFrame ((Scheme.Modules.pullback (P s).base).obj (Cotangent E)) ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection (P s).base (Cotangent E) a) := by
    have he := frame_iso (hodgeIso E M (P s)).symm _ (localAlpha_frame E M (P s))
    rw [← (realizes_iff E M a).mp ha (P s)] at he
    change IsFrame _ ⊤ ((hodgeIso E M (P s)).inv.app ⊤
      ((hodgeIso E M (P s)).hom.app ⊤
        (ArithmeticThetaPullback.pullbackGlobalSection (P s).base (Cotangent E) a))) at he
    simpa only [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using he
  have hr := frame_restrict ((Scheme.Modules.pullback (P s).base).obj (Cotangent E))
    (show (P s).base ⁻¹ᵁ (P s).base.opensRange ≤ ⊤ from le_top) _ hf
  change IsFrame _ _ (res _ _ (Scheme.Modules.pullbackLocalSection (P s).base a)) at hr
  rw [InitialSectionNaturality.pullback_res] at hr
  exact hr

open NeronModelInfra

private lemma mul_base_congr {T : Scheme.{u}} {a b : T ⟶ S} (h : a = b)
    (x y : SchemeHomOver a E.p) (x' y' : SchemeHomOver b E.p)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (E.law.mul a x y).val = (E.law.mul b x' y').val := by
  subst b
  have hxx : x = x' := Subtype.ext hx
  have hyy : y = y' := Subtype.ext hy
  rw [hxx, hyy]

/-- A factorization of the actual base maps induces a pointed, marked Cartesian
comparison of the two Weierstrass curves. -/
lemma test_refinement (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (hρ : baseMap P.ring Q.ring ρ ≫ P.base = Q.base) :
    ∃ b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
        ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation,
      b ≫ P.comparison = Q.comparison ∧
      ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
        P.ring P.equation P.law Q.ring Q.equation Q.law ρ b ∧
      Q.level.x.val ≫ b = baseMap P.ring Q.ring ρ ≫ P.level.x.val ∧
      Q.level.y.val ≫ b = baseMap P.ring Q.ring ρ ≫ P.level.y.val := by
  let p := ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation
  let q := ArithmeticThetaRelativeKatoR0169.structureMap Q.ring Q.equation
  let f := baseMap P.ring Q.ring ρ
  have hw : Q.comparison ≫ E.p = (q ≫ f) ≫ P.base := by
    rw [Category.assoc, hρ]
    exact Q.cartesian.w
  let b := P.cartesian.lift Q.comparison (q ≫ f) hw
  have hb : b ≫ P.comparison = Q.comparison := P.cartesian.lift_fst _ _ _
  have hp : b ≫ p = q ≫ f := P.cartesian.lift_snd _ _ _
  have hc : IsPullback b q p f :=
    IsPullback.of_right (by rw [hb, hρ]; exact Q.cartesian) hp P.cartesian
  have hz : ArithmeticThetaRelativeKatoR0169.origin Q.ring Q.equation ≫ b =
      f ≫ ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation := by
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hb, Q.zero_eq, Category.assoc, P.zero_eq,
        ← Category.assoc, hρ]
    · have hoP : ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation ≫ p = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect P.ring P.equation).property
      have hoQ : ArithmeticThetaRelativeKatoR0169.origin Q.ring Q.equation ≫ q = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect Q.ring Q.equation).property
      change (_ ≫ b) ≫ p = (f ≫ _) ≫ p
      rw [Category.assoc, hp, ← Category.assoc, hoQ, Category.id_comp,
        Category.assoc, hoP, Category.comp_id]
  have hn : ∀ n, Q.law.schemeNsmul n ≫ b = b ≫ P.law.schemeNsmul n := by
    apply ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp ρ q b hc P.law Q.law
    · intro T t x y
      apply P.cartesian.hom_ext
      · rw [Category.assoc, hb]
        let x' : SchemeHomOver (t ≫ Q.base) E.p :=
          ⟨x.val ≫ Q.comparison, by rw [Category.assoc, Q.cartesian.w, ← Category.assoc, x.property]⟩
        let y' : SchemeHomOver (t ≫ Q.base) E.p :=
          ⟨y.val ≫ Q.comparison, by rw [Category.assoc, Q.cartesian.w, ← Category.assoc, y.property]⟩
        have hQ := Q.mul_eq T t x y x' y' rfl rfl
        let xp : SchemeHomOver (t ≫ f) p :=
          ⟨x.val ≫ b, by rw [Category.assoc, hp, ← Category.assoc, x.property]⟩
        let yp : SchemeHomOver (t ≫ f) p :=
          ⟨y.val ≫ b, by rw [Category.assoc, hp, ← Category.assoc, y.property]⟩
        have he : (t ≫ f) ≫ P.base = t ≫ Q.base := by rw [Category.assoc, hρ]
        let xx : SchemeHomOver ((t ≫ f) ≫ P.base) E.p := ⟨x'.val, x'.property.trans he.symm⟩
        let yy : SchemeHomOver ((t ≫ f) ≫ P.base) E.p := ⟨y'.val, y'.property.trans he.symm⟩
        have hP := P.mul_eq T (t ≫ f) xp yp xx yy
          (by dsimp [xx, x', xp]; rw [Category.assoc, hb])
          (by dsimp [yy, y', yp]; rw [Category.assoc, hb])
        have hh : (E.law.mul _ xx yy).val = (E.law.mul _ x' y').val :=
          mul_base_congr E he xx yy x' y' rfl rfl
        exact hQ.symm.trans (hh.symm.trans hP)
      · exact (Category.assoc _ b p).trans
          ((congrArg (fun z => (Q.law.mul t x y).val ≫ z) hp).trans
            ((Category.assoc _ q f).symm.trans
              ((congrArg (fun z => z ≫ f) (Q.law.mul t x y).property).trans
                (P.law.mul _ _ _).property.symm)))
    · intro T t
      rw [Q.originLaw.1, P.originLaw.1, Category.assoc, hz, Category.assoc]
      rfl
  have hx (x : SchemeHomOver (𝟙 _) q) (y : SchemeHomOver (𝟙 _) p)
      (hQ : x.val ≫ Q.comparison = Q.base ≫ M.x.val)
      (hP : y.val ≫ P.comparison = P.base ≫ M.x.val) : x.val ≫ b = f ≫ y.val := by
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hb, hQ, Category.assoc, hP, ← Category.assoc, hρ]
    · rw [Category.assoc, hp, ← Category.assoc, x.property,
        Category.id_comp, Category.assoc, y.property, Category.comp_id]
  refine ⟨b, hb, ⟨hc, hz, hn⟩, hx Q.level.x P.level.x Q.x_eq P.x_eq, ?_⟩
  apply P.cartesian.hom_ext
  · rw [Category.assoc, hb, Q.y_eq, Category.assoc, P.y_eq, ← Category.assoc, hρ]
  · rw [Category.assoc, hp, ← Category.assoc, Q.level.y.property,
      Category.id_comp, Category.assoc, P.level.y.property, Category.comp_id]

/-- The signed affine sections agree under every actual refinement, including
nonflat ring maps. The curve comparison is supplied by the Cartesian tests. -/
lemma localAlpha_refinement (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (hρ : baseMap P.ring Q.ring ρ ≫ P.base = Q.base) :
    ∃ (b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
        ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
      (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
        P.ring P.equation P.law Q.ring Q.equation Q.law ρ b),
      b ≫ P.comparison = Q.comparison ∧
      Q.level.x.val ≫ b = baseMap P.ring Q.ring ρ ≫ P.level.x.val ∧
      Q.level.y.val ≫ b = baseMap P.ring Q.ring ρ ≫ P.level.y.val ∧
      ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha
        P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb
        (localAlpha E M P) = localAlpha E M Q := by
  obtain ⟨b, hc, hb, hx, hy⟩ := test_refinement E M P Q ρ hρ
  letI := P.elliptic
  letI := Q.elliptic
  exact ⟨b, hb, hc, hx, hy,
    ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.alpha_naturality
      P.ring P.equation P.law 4 P.level P.originLaw (by decide) (by decide)
      Q.ring Q.equation Q.law Q.originLaw Q.level ρ b hb hx hy
      (localAlpha E M P) (localAlpha E M Q)
      (localAlpha_realizes E M P) (localAlpha_realizes E M Q)⟩

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

/-- Combine accepted cotangent coherence and derivative naturality before
specializing the zero sections to the literal Weierstrass origins. -/
lemma comparison_comp {R T : Type u} [CommRing R] [CommRing T]
    (F : Family (ArithmeticThetaLocalWeierstrassR0203.Base R))
    (G : Family (ArithmeticThetaLocalWeierstrassR0203.Base T))
    (ρ : R →+* T) (b : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ S)
    (c : ArithmeticThetaLocalWeierstrassR0203.Base T ⟶ S)
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve) (h : G.curve ⟶ E.curve)
    (hbase : c = Spec.map (CommRingCat.ofHom ρ) ≫ b) (hcurve : h = g ≫ f)
    (hgc : IsPullback g G.p F.p (Spec.map (CommRingCat.ofHom ρ)))
    (hf : F.zero ≫ f = b ≫ E.zero)
    (hg : G.zero ≫ g = Spec.map (CommRingCat.ofHom ρ) ≫ F.zero)
    (hh : G.zero ≫ h = c ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module)
    (j : (Scheme.Modules.pullback g).obj F.zero.ker.module ≅ G.zero.ker.module)
    (k : (Scheme.Modules.pullback h).obj E.zero.ker.module ≅ G.zero.ker.module)
    (hi : IdealCompatible E F f i) (hj : IdealCompatible F G g j)
    (hk : IdealCompatible E G h k) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ρ))).map
        ((cotangentComparison E F b f hf i).hom ≫ affineDifferential F) ≫
      (affineHodgeComparison F G ρ g hgc hg).hom =
    ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom ρ)) b).app (Cotangent E)).hom ≫
      (pullbackEqIso hbase.symm (Cotangent E)).hom ≫
      (cotangentComparison E G c h hh k).hom ≫ affineDifferential G := by
  subst c h
  have hn := (affine_conormal_hodge_naturality R T F G ρ g hgc hg).2.2 j hj
  have hc := scheme_cotangent_coherence.2 S _ _ E F G b
    (Spec.map (CommRingCat.ofHom ρ)) f g hf hg hh
    (cotangentComparison E F b f hf i)
    (cotangentComparison F G (Spec.map (CommRingCat.ofHom ρ)) g hg j)
    (cotangentComparison E G (Spec.map (CommRingCat.ofHom ρ) ≫ b) (g ≫ f) hh k)
    ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩
  simp only [Functor.map_comp, Category.assoc, pullbackEqIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  rw [hn, ← Category.assoc, hc, Category.assoc]

/-- Explicit origins allow equality transport before any dependent ideal or
cotangent expression is formed. -/
lemma comparison_comp_explicit {R T : Type u} [CommRing R] [CommRing T]
    (F : Family (ArithmeticThetaLocalWeierstrassR0203.Base R))
    (G : Family (ArithmeticThetaLocalWeierstrassR0203.Base T))
    (ρ : R →+* T) (b : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ S)
    (c : ArithmeticThetaLocalWeierstrassR0203.Base T ⟶ S)
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve) (h : G.curve ⟶ E.curve)
    (s : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ F.curve)
    (t : ArithmeticThetaLocalWeierstrassR0203.Base T ⟶ G.curve)
    (hs : s = F.zero) (ht : t = G.zero)
    (hbase : c = Spec.map (CommRingCat.ofHom ρ) ≫ b) (hcurve : h = g ≫ f)
    (hgc : IsPullback g G.p F.p (Spec.map (CommRingCat.ofHom ρ)))
    (hf : s ≫ f = b ≫ E.zero)
    (hg : t ≫ g = Spec.map (CommRingCat.ofHom ρ) ≫ s)
    (hh : t ≫ h = c ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ s.ker.module)
    (j : (Scheme.Modules.pullback g).obj s.ker.module ≅ t.ker.module)
    (k : (Scheme.Modules.pullback h).obj E.zero.ker.module ≅ t.ker.module)
    (hi : i.hom ≫ s.ker.moduleι = (Scheme.Modules.pullback f).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ f).hom)
    (hj : j.hom ≫ t.ker.moduleι = (Scheme.Modules.pullback g).map s.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ g).hom)
    (hk : k.hom ≫ t.ker.moduleι = (Scheme.Modules.pullback h).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ h).hom) :
    letI : Algebra R T := ρ.toAlgebra
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ρ))).map
      ((squarePullbackIso b E.zero s f hf.symm E.zero.ker.module).hom ≫
        (Scheme.Modules.pullback s).map i.hom ≫ conormalMap F.p s) ≫
      (squarePullbackIso (Spec.map (CommRingCat.ofHom ρ)) s t g hg.symm F.p.kaehler).hom ≫
        (Scheme.Modules.pullback t).map (differentialMap F.p G.p g hgc.w) =
    ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom ρ)) b).app (Cotangent E)).hom ≫
      (pullbackEqIso hbase.symm (Cotangent E)).hom ≫
      (squarePullbackIso c E.zero t h hh.symm E.zero.ker.module).hom ≫
      (Scheme.Modules.pullback t).map k.hom ≫ conormalMap G.p t := by
  letI : Algebra R T := ρ.toAlgebra
  subst s t
  have hc := comparison_comp E F G ρ b c f g h hbase hcurve hgc hf hg hh i j k hi hj hk
  simpa only [cotangentComparison, affineDifferential, affineHodgeComparison,
    pointedDifferentialIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Cotangent, RingHom.algebraMap_toAlgebra, Category.assoc] using hc

/-- There is a unique inclusion-compatible ideal comparison for a refinement. -/
lemma refinement_ideal (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
      ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      P.ring P.equation P.law Q.ring Q.equation Q.law ρ b) :
    ∃! i : (Scheme.Modules.pullback b).obj
        (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module ≅
        (ArithmeticThetaRelativeKatoR0169.origin Q.ring Q.equation).ker.module,
      i.hom ≫ (ArithmeticThetaRelativeKatoR0169.origin Q.ring Q.equation).ker.moduleι =
        (Scheme.Modules.pullback b).map
          (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.moduleι ≫
          (ArithmeticThetaPullback.pullback_unit_iso _ _ b).hom := by
  have hz : (MarkedAffineTestComparison.family E M Q).zero ≫ b =
      Spec.map (CommRingCat.ofHom ρ) ≫ (MarkedAffineTestComparison.family E M P).zero := by
    rw [MarkedAffineTestComparison.family_zero, MarkedAffineTestComparison.family_zero]
    exact hb.2.1
  have h := cartesian_identity_ideal _ _ (MarkedAffineTestComparison.family E M P)
    (MarkedAffineTestComparison.family E M Q) (Spec.map (CommRingCat.ofHom ρ)) b hb.1 hz
  unfold IdealCompatible at h
  rw [MarkedAffineTestComparison.family_zero E M P,
    MarkedAffineTestComparison.family_zero E M Q] at h
  exact h

/-- The prescribed cotangent-to-Hodge maps commute with every actual refinement. -/
lemma test_hodge_naturality (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
      ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      P.ring P.equation P.law Q.ring Q.equation Q.law ρ b)
    (hbase : Q.base = baseMap P.ring Q.ring ρ ≫ P.base)
    (hcurve : Q.comparison = b ≫ P.comparison) :
    (Scheme.Modules.pullback (baseMap P.ring Q.ring ρ)).map
      (affineHodgeMap E M P (idealIso E M P)) ≫
      ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap
        P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb =
    ((Scheme.Modules.pullbackComp (baseMap P.ring Q.ring ρ) P.base).app (Cotangent E)).hom ≫
      (pullbackEqIso hbase.symm (Cotangent E)).hom ≫
      affineHodgeMap E M Q (idealIso E M Q) := by
  obtain ⟨j, hj, _⟩ := refinement_ideal E M P Q ρ b hb
  have h := comparison_comp_explicit E
    (MarkedAffineTestComparison.family E M P) (MarkedAffineTestComparison.family E M Q)
    ρ P.base Q.base P.comparison b Q.comparison
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)
    (ArithmeticThetaRelativeKatoR0169.origin Q.ring Q.equation)
    (MarkedAffineTestComparison.family_zero E M P).symm
    (MarkedAffineTestComparison.family_zero E M Q).symm
    hbase hcurve hb.1 P.zero_eq hb.2.1 Q.zero_eq
    (idealIso E M P) j (idealIso E M Q)
    (idealIso_compatible E M P) hj (idealIso_compatible E M Q)
  simpa only [affineHodgeMap, ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap,
    MarkedAffineTestComparison.family, baseMap, Category.assoc] using h

private lemma iso_eq_comparison {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) (hr : r = q ≫ p)
    (A : X.Modules) (B : Y.Modules) (C : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj A ≅ B)
    (f : (Scheme.Modules.pullback q).obj B ≅ C)
    (g : (Scheme.Modules.pullback r).obj A ≅ C)
    (h : (Scheme.Modules.pullback q).map e.hom ≫ f.hom =
      ((Scheme.Modules.pullbackComp q p).app A).hom ≫
        (pullbackEqIso hr.symm A).hom ≫ g.hom) :
    g = composeComparison p q r hr A B C e f := by
  subst r
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp q p).app A).hom).mp
  simpa only [composeComparison, pullbackEqIso, eqToIso_refl, Iso.refl_hom,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_assoc] using h.symm

lemma comparison_refinement (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
      ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      P.ring P.equation P.law Q.ring Q.equation Q.law ρ b)
    (hbase : Q.base = baseMap P.ring Q.ring ρ ≫ P.base)
    (hcurve : Q.comparison = b ≫ P.comparison) :
    letI := P.elliptic
    letI := ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.hodgeMap_isIso
      P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb
    hodgeIso E M Q = composeComparison P.base (baseMap P.ring Q.ring ρ) Q.base hbase
      (Cotangent E) (Hodge P.ring P.equation) (Hodge Q.ring Q.equation)
      (hodgeIso E M P)
      (asIso (ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap
        P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb)) := by
  letI := P.elliptic
  letI := ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.hodgeMap_isIso
    P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb
  exact iso_eq_comparison _ _ _ _ _ _ _ _ _ _
    (test_hodge_naturality E M P Q ρ b hb hbase hcurve)

/-- Pull a local cotangent section through the prescribed affine comparison. -/
def sectionPull (P : AffineTest E M) (U : S.Opens)
    (V : (ArithmeticThetaLocalWeierstrassR0203.Base P.ring).Opens)
    (h : V ≤ P.base ⁻¹ᵁ U) (s : Γ(Cotangent E, U)) : Γ(Hodge P.ring P.equation, V) :=
  res _ h ((hodgeIso E M P).hom.app _ (Scheme.Modules.pullbackLocalSection P.base s))

lemma sectionPull_top (P : AffineTest E M) (s : Γ(Cotangent E, ⊤)) :
    sectionPull E M P ⊤ ⊤ (by simp) s = affineAlpha E M P (idealIso E M P) s := by
  simp only [sectionPull, res_refl, hodgeIso, asIso_hom, affineAlpha]
  rfl

lemma sectionPull_restrict (P : AffineTest E M) (U U' : S.Opens) (hU : U' ≤ U)
    (V : (ArithmeticThetaLocalWeierstrassR0203.Base P.ring).Opens)
    (h : V ≤ P.base ⁻¹ᵁ U') (s : Γ(Cotangent E, U)) :
    sectionPull E M P U' V h (res (Cotangent E) hU s) =
      sectionPull E M P U V (h.trans (fun _ hx => hU hx)) s := by
  unfold sectionPull
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

lemma sectionPull_refinement (P Q : AffineTest E M) (ρ : P.ring →+* Q.ring)
    (b : ArithmeticThetaRelativeKatoR0169.Curve Q.ring Q.equation ⟶
      ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      P.ring P.equation P.law Q.ring Q.equation Q.law ρ b)
    (hbase : Q.base = baseMap P.ring Q.ring ρ ≫ P.base)
    (hcurve : Q.comparison = b ≫ P.comparison)
    (U : S.Opens) (V : (ArithmeticThetaLocalWeierstrassR0203.Base P.ring).Opens)
    (Z : (ArithmeticThetaLocalWeierstrassR0203.Base Q.ring).Opens)
    (hP : V ≤ P.base ⁻¹ᵁ U) (hT : Z ≤ baseMap P.ring Q.ring ρ ⁻¹ᵁ V)
    (hQ : Z ≤ Q.base ⁻¹ᵁ U) (s : Γ(Cotangent E, U)) :
    sectionPull E M Q U Z hQ s =
      res (Hodge Q.ring Q.equation) hT
        ((ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap
          P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb).app _
          (Scheme.Modules.pullbackLocalSection (baseMap P.ring Q.ring ρ)
            (sectionPull E M P U V hP s))) := by
  letI := P.elliptic
  letI := ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.hodgeMap_isIso
    P.ring P.equation P.law Q.ring Q.equation Q.law ρ b hb
  unfold sectionPull
  rw [comparison_refinement E M P Q ρ b hb hbase hcurve]
  rw [composeComparison_section _ _ _ _ _ _ _ _ _ U s Z hQ (fun z hz => hP (hT hz))]
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]
  simp only [asIso_hom]

/-- Arbitrary affine neighborhoods, without normality, reducedness or finiteness. -/
lemma refinement_inside (P : AffineTest E M)
    (U : (ArithmeticThetaLocalWeierstrassR0203.Base P.ring).Opens)
    (x : ArithmeticThetaLocalWeierstrassR0203.Base P.ring) (hx : x ∈ U) :
    ∃ (Q : AffineTest E M) (ρ : P.ring →+* Q.ring),
      IsOpenImmersion (baseMap P.ring Q.ring ρ) ∧
      x ∈ Set.range (baseMap P.ring Q.ring ρ) ∧
      Set.range (baseMap P.ring Q.ring ρ) ⊆ U ∧
      Q.base = baseMap P.ring Q.ring ρ ≫ P.base := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  letI : IsAffine V := hV
  let T := Γ(V, ⊤)
  let f : ArithmeticThetaLocalWeierstrassR0203.Base T ⟶
      ArithmeticThetaLocalWeierstrassR0203.Base P.ring := (Scheme.isoSpec V).inv ≫ V.ι
  let ρ : P.ring →+* T := (Spec.preimage f).hom
  have hρ : baseMap P.ring T ρ = f := Spec.map_preimage f
  letI : Algebra ℚ T := (ρ.comp (algebraMap ℚ P.ring)).toAlgebra
  letI := P.elliptic
  let W := P.equation.map ρ
  obtain ⟨H, b, hH, hb⟩ :=
    ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.coefficient_base_change
      P.ring P.equation P.law P.originLaw T ρ
  let A : ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law 4
      ((𝟙 (ArithmeticThetaLocalWeierstrassR0203.Base T)) ≫ baseMap P.ring T ρ) :=
    ArithmeticThetaFullLevelCoverR0175.BaseChange.restrict P.level (baseMap P.ring T ρ) (by simp)
  let N := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up
    hb P.originLaw hH A
  have hNx : N.x.val ≫ b = baseMap P.ring T ρ ≫ P.level.x.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_x
      hb P.originLaw hH A
  have hNy : N.y.val ≫ b = baseMap P.ring T ρ ≫ P.level.y.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_y
      hb P.originLaw hH A
  let Q : AffineTest E M :=
    { ring := T, equation := W, elliptic := inferInstance, law := H, originLaw := hH
      base := baseMap P.ring T ρ ≫ P.base
      comparison := b ≫ P.comparison
      cartesian := hb.1.paste_horiz P.cartesian
      zero_eq := by
        rw [← Category.assoc, hb.2.1, Category.assoc, P.zero_eq, Category.assoc]
        rfl
      mul_eq := by
        intro Z t x y x' y' hx' hy'
        let xp := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.point hb t x
        let yp := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.point hb t y
        let xx : SchemeHomOver ((t ≫ baseMap P.ring T ρ) ≫ P.base) E.p :=
          ⟨x'.val, x'.property.trans (Category.assoc _ _ _).symm⟩
        let yy : SchemeHomOver ((t ≫ baseMap P.ring T ρ) ≫ P.base) E.p :=
          ⟨y'.val, y'.property.trans (Category.assoc _ _ _).symm⟩
        have he := mul_base_congr E (Category.assoc t (baseMap P.ring T ρ) P.base).symm
          x' y' xx yy rfl rfl
        have hP := P.mul_eq Z (t ≫ baseMap P.ring T ρ) xp yp xx yy
          (hx'.trans (Category.assoc _ _ _).symm)
          (hy'.trans (Category.assoc _ _ _).symm)
        have hm := congrArg Subtype.val
          (ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.point_mul
            hb P.originLaw hH t x y)
        exact he.trans (hP.trans ((congrArg (fun z => z ≫ P.comparison) hm).symm.trans
          (Category.assoc _ _ _)))
      level := N
      x_eq := by rw [← Category.assoc, hNx, Category.assoc, P.x_eq, Category.assoc]
      y_eq := by rw [← Category.assoc, hNy, Category.assoc, P.y_eq, Category.assoc] }
  refine ⟨Q, ρ, ?_, ?_, ?_, rfl⟩
  · change IsOpenImmersion (baseMap P.ring T ρ)
    rw [hρ]
    dsimp [f]
    infer_instance
  · change x ∈ Set.range (baseMap P.ring T ρ)
    rw [hρ]
    refine ⟨(Scheme.isoSpec V).hom ⟨x, hxV⟩, ?_⟩
    change ((Scheme.isoSpec V).hom ≫ (Scheme.isoSpec V).inv ≫ V.ι) _ = x
    simp
  · change Set.range (baseMap P.ring T ρ) ⊆ U
    rw [hρ]
    rintro _ ⟨z, rfl⟩
    exact hVU ((Scheme.isoSpec V).inv z).property

lemma scalar_factor (P Q : AffineTest E M) [IsOpenImmersion P.base]
    (h : Set.range Q.base ⊆ Set.range P.base) :
    ∃ ρ : P.ring →+* Q.ring, baseMap P.ring Q.ring ρ ≫ P.base = Q.base := by
  let f := IsOpenImmersion.lift P.base Q.base h
  let ρ : P.ring →+* Q.ring := (Spec.preimage f).hom
  have hf : baseMap P.ring Q.ring ρ = f := Spec.map_preimage f
  exact ⟨ρ, hf ▸ IsOpenImmersion.lift_fac P.base Q.base h⟩

def chartSection (P : AffineTest E M) [IsOpenImmersion P.base] :
    Γ(Cotangent E, P.base.opensRange) := (chart_section_exists E M P).choose

lemma chartSection_frame (P : AffineTest E M) [IsOpenImmersion P.base] :
    IsFrame (Cotangent E) P.base.opensRange (chartSection E M P) :=
  (chart_section_exists E M P).choose_spec.1

lemma chartSection_pull (P : AffineTest E M) [IsOpenImmersion P.base] :
    sectionPull E M P P.base.opensRange ⊤ (by rw [P.base.preimage_opensRange])
      (chartSection E M P) = localAlpha E M P :=
  (chart_section_exists E M P).choose_spec.2

lemma chartSection_test (P Q : AffineTest E M) [IsOpenImmersion P.base]
    (ρ : P.ring →+* Q.ring) (hρ : baseMap P.ring Q.ring ρ ≫ P.base = Q.base)
    (hQ : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base Q.ring).Opens) ≤
      Q.base ⁻¹ᵁ P.base.opensRange) :
    sectionPull E M Q P.base.opensRange ⊤ hQ (chartSection E M P) = localAlpha E M Q := by
  obtain ⟨b, hb, hc, hx, hy, hn⟩ := localAlpha_refinement E M P Q ρ hρ
  rw [sectionPull_refinement E M P Q ρ b hb hρ.symm hc.symm
    P.base.opensRange ⊤ ⊤ (by rw [P.base.preimage_opensRange]) (by simp) hQ]
  rw [chartSection_pull, res_refl]
  exact hn

lemma sectionPull_injective (P : AffineTest E M) [IsOpenImmersion P.base]
    (U : S.Opens) (hU : P.base.opensRange ≤ U)
    (h : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base P.ring).Opens) ≤ P.base ⁻¹ᵁ U)
    (s t : Γ(Cotangent E, U))
    (he : sectionPull E M P U ⊤ h s = sectionPull E M P U ⊤ h t) :
    res (Cotangent E) hU s = res (Cotangent E) hU t := by
  have hp : Scheme.Modules.pullbackLocalSection P.base s =
      Scheme.Modules.pullbackLocalSection P.base t := by
    apply (ConcreteCategory.bijective_of_isIso ((hodgeIso E M P).hom.app _)).1
    exact (res_bijective _ h le_top).1 he
  exact restriction_eq_of_pullback_eq P.base (Cotangent E) U hU s t hp

lemma chartSection_overlap (P Q : AffineTest E M)
    [IsOpenImmersion P.base] [IsOpenImmersion Q.base] :
    res (Cotangent E) (inf_le_left : P.base.opensRange ⊓ Q.base.opensRange ≤ P.base.opensRange)
        (chartSection E M P) =
      res (Cotangent E) (inf_le_right : P.base.opensRange ⊓ Q.base.opensRange ≤ Q.base.opensRange)
        (chartSection E M Q) := by
  apply sections_eq_local
  intro x hx
  obtain ⟨y, hy⟩ := hx.1
  let U := P.base ⁻¹ᵁ Q.base.opensRange
  have hyU : y ∈ U := by
    change P.base y ∈ Q.base.opensRange
    rw [hy]
    exact hx.2
  obtain ⟨D, ρ, ho, hcontains, hinside, hbase⟩ := refinement_inside E M P U y hyU
  letI := ho
  letI : IsOpenImmersion D.base := by rw [hbase]; infer_instance
  have hP : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base D.ring).Opens) ≤
      D.base ⁻¹ᵁ P.base.opensRange := by
    intro z _
    change D.base z ∈ P.base.opensRange
    rw [hbase]
    exact ⟨baseMap P.ring D.ring ρ z, rfl⟩
  have hQ : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base D.ring).Opens) ≤
      D.base ⁻¹ᵁ Q.base.opensRange := by
    intro z _
    change D.base z ∈ Q.base.opensRange
    rw [hbase]
    exact hinside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := scalar_factor E M Q D (by
    rintro _ ⟨z, rfl⟩
    exact hQ (Set.mem_univ z))
  have hps := chartSection_test E M P D ρ hbase.symm hP
  have hqs := chartSection_test E M Q D τ hτ hQ
  have hU : D.base.opensRange ≤ P.base.opensRange ⊓ Q.base.opensRange := by
    rintro _ ⟨z, rfl⟩
    exact ⟨hP (Set.mem_univ z), hQ (Set.mem_univ z)⟩
  have hD : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base D.ring).Opens) ≤
      D.base ⁻¹ᵁ (P.base.opensRange ⊓ Q.base.opensRange) := by
    intro z _
    exact ⟨hP (Set.mem_univ z), hQ (Set.mem_univ z)⟩
  refine ⟨D.base.opensRange, ?_, hU, ?_⟩
  · obtain ⟨z, hz⟩ := hcontains
    refine ⟨z, ?_⟩
    rw [hbase]
    change P.base (baseMap P.ring D.ring ρ z) = x
    rw [hz, hy]
  · apply sectionPull_injective E M D _ hU hD
    rw [sectionPull_restrict, sectionPull_restrict]
    exact hps.trans hqs.symm

/-- The glued section has the specified normalization on every affine test.
Neighborhoods are chosen on that test, so its map to the base need not be flat. -/
lemma glued_section_test (P : S → AffineTest E M)
    (ho : ∀ s, IsOpenImmersion (P s).base)
    (hc : ∀ x : S, ∃ i, x ∈ Set.range (P i).base)
    (a : Γ(Cotangent E, ⊤))
    (ha : ∀ i, res (Cotangent E) le_top a = @chartSection _ E M (P i) (ho i))
    (Q : AffineTest E M) :
    affineAlpha E M Q (idealIso E M Q) a = localAlpha E M Q := by
  letI (s : S) := ho s
  apply sections_eq_local
  intro x _
  obtain ⟨i, hi⟩ := hc (Q.base x)
  let U := Q.base ⁻¹ᵁ (P i).base.opensRange
  have hxU : x ∈ U := hi
  obtain ⟨D, ρ, hρopen, hcontains, hinside, hbase⟩ := refinement_inside E M Q U x hxU
  letI := hρopen
  have hD : (⊤ : (ArithmeticThetaLocalWeierstrassR0203.Base D.ring).Opens) ≤
      D.base ⁻¹ᵁ (P i).base.opensRange := by
    intro z _
    change D.base z ∈ (P i).base.opensRange
    rw [hbase]
    exact hinside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := scalar_factor E M (P i) D (by
    rintro _ ⟨z, rfl⟩
    exact hD (Set.mem_univ z))
  have hchart := chartSection_test E M (P i) D τ hτ hD
  have hglobal : sectionPull E M D ⊤ ⊤ (by simp) a = localAlpha E M D := by
    rw [← sectionPull_restrict E M D ⊤ (P i).base.opensRange le_top ⊤ hD a, ha i]
    exact hchart
  obtain ⟨b, hb, hcurve, hx, hy, hnat⟩ := localAlpha_refinement E M Q D ρ hbase.symm
  have htransport := sectionPull_refinement E M Q D ρ b hb hbase hcurve.symm
    ⊤ ⊤ ⊤ (by simp) (by simp) (by simp) a
  letI := Q.elliptic
  letI := ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.hodgeMap_isIso
    Q.ring Q.equation Q.law D.ring D.equation D.law ρ b hb
  have hp : Scheme.Modules.pullbackLocalSection (baseMap Q.ring D.ring ρ)
        (affineAlpha E M Q (idealIso E M Q) a) =
      Scheme.Modules.pullbackLocalSection (baseMap Q.ring D.ring ρ) (localAlpha E M Q) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap
        Q.ring Q.equation Q.law D.ring D.equation D.law ρ b hb).app ⊤)).1
    have hfirst := htransport.symm.trans hglobal
    simp only [sectionPull_top, res_refl] at hfirst
    exact hfirst.trans hnat.symm
  refine ⟨(baseMap Q.ring D.ring ρ).opensRange, hcontains, le_top, ?_⟩
  exact restriction_eq_of_pullback_eq (baseMap Q.ring D.ring ρ)
    (Hodge Q.ring Q.equation) ⊤ le_top _ _ hp

lemma exists_realizes (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) :
    ∃ a : Γ(Cotangent E, ⊤), RealizesAlpha E M a := by
  let P : S → AffineTest E M := fun s =>
    (MarkedAffineTestComparison.coverage E M k σ s).choose
  have ho : ∀ s, IsOpenImmersion (P s).base := fun s =>
    (MarkedAffineTestComparison.coverage E M k σ s).choose_spec.1
  letI (s : S) := ho s
  have hc : ∀ x : S, ∃ i, x ∈ Set.range (P i).base := fun x =>
    ⟨x, (MarkedAffineTestComparison.coverage E M k σ x).choose_spec.2⟩
  have hcover : (⨆ s, (P s).base.opensRange) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (hc x)
  obtain ⟨a, ha, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(Cotangent E).presheaf, (Cotangent E).isSheaf⟩ (fun s => (P s).base.opensRange)
    ⊤ (fun _ => homOfLE le_top) hcover.ge
    (fun s => chartSection E M (P s)) (fun i j => chartSection_overlap E M (P i) (P j))
  refine ⟨a, (realizes_iff E M a).mpr ?_⟩
  exact glued_section_test E M P ho hc a ha

end SchemeAlphaSection

/-- The unique intrinsic signed alpha on an arbitrary marked genus-one family,
with its prescribed affine normalization and its frame property on every open. -/
theorem scheme_alpha_section :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a) ∧ (∀ a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaSchemeHodgeR0205.Cotangent E) ⊤ a) := by
  intro k _ _ S σ E M
  obtain ⟨a, ha⟩ := SchemeAlphaSection.exists_realizes E M k σ
  exact ⟨⟨a, ha, fun b hb => SchemeAlphaSection.realizes_unique E M k σ hb ha⟩,
    fun b hb => SchemeAlphaSection.realizes_frame E M k σ b hb⟩

end ArithmeticThetaSchemeFourCharacterR0215

#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.realizes_unique
#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.realizes_frame
#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.localAlpha_refinement

#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.test_hodge_naturality

#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.sectionPull_refinement

#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.refinement_inside
#print axioms ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.chartSection_test

#print axioms ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_section
