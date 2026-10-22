module

public import SchemeDiscriminantDefinitionsR0244
public import ArbitraryDiscriminantNaturalityR0243
public import ArbitraryWeierstrassDiscriminantR0243
public import SchemeCotangentCoherenceR0205

@[expose] public section

/-! Descent of the normalized discriminant to the actual identity cotangent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaSchemeDiscriminantR0244
namespace SchemeDiscriminantExistence
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171 hiding Base
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic

theorem cotangent_invertible {S : Scheme.{u}} (E : Family S) :
    Scheme.Modules.IsInvertible (Cotangent E) :=
  (CartesianIdentityIdeal.zero_ideal_invertible E).isInvertible_module.pullback E.zero

theorem cotangent_frame {S : Scheme.{u}} (E : Family S) (x : S) :
    ∃ (U : S.Opens) (s : Γ(Cotangent E, U)),
      x ∈ U ∧ IsFrame (Cotangent E) U s := by
  obtain ⟨U, s, hx, hs⟩ := (cotangent_invertible E).exists_isFrameOn x
  exact ⟨U, s, hx, fun V hV => hs hV hV⟩

theorem weierstrass_zero (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    (weierstrassFamily R W G hG).zero = origin R W := by
  change (G.one (𝟙 (Base R))).val = origin R W
  simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))

def comparisonComp {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a) : Comparison E H (a ≫ b) where
  map := D.map ≫ C.map
  cartesian := D.cartesian.paste_horiz C.cartesian
  pointed := by rw [← Category.assoc, D.pointed, Category.assoc, C.pointed,
    Category.assoc]

theorem cotangentIso_compatible {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :
    CotangentCompatible E F b C.map C.pointed (cotangentIso C) :=
  ⟨_, (cartesian_identity_ideal S T E F b C.map C.cartesian C.pointed).exists.choose_spec,
    rfl⟩

theorem cotangentIso_comp {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a) :
    (Scheme.Modules.pullback a).map (cotangentIso C).hom ≫ (cotangentIso D).hom =
      ((Scheme.Modules.pullbackComp a b).app (Cotangent E)).hom ≫
        (cotangentIso (comparisonComp C D)).hom :=
  scheme_cotangent_coherence.2 S T U E F H b a C.map D.map C.pointed D.pointed
    (comparisonComp C D).pointed _ _ _ (cotangentIso_compatible C)
    (cotangentIso_compatible D) (cotangentIso_compatible (comparisonComp C D))

theorem cotangentIso_comp_eq {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a) :
    cotangentIso (comparisonComp C D) =
      composeComparison b a (a ≫ b) rfl (Cotangent E) (Cotangent F) (Cotangent H)
        (cotangentIso C) (cotangentIso D) := by
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp a b).app (Cotangent E)).hom).mp
  simpa only [composeComparison, pullbackEqIso, Iso.trans_hom, Iso.refl_hom,
    eqToIso_refl, Category.id_comp, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc] using
    (cotangentIso_comp C D).symm

open ArithmeticThetaTensorPower

/-- Tensoring the canonical cotangent comparison preserves its composition law. -/
theorem powerIso_comp_eq {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a) :
    powerIso (comparisonComp C D) =
      composeComparison b a (a ≫ b) rfl (Power E) (Power F) (Power H)
        (powerIso C) (powerIso D) := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  obtain ⟨V, s, hx, hs⟩ := cotangent_frame E ((a ≫ b) x)
  refine ⟨(a ≫ b) ⁻¹ᵁ V,
    Scheme.Modules.pullbackLocalSection (a ≫ b) (tensorPowerSection S (Cotangent E) 24 V s),
    hx, pullback_frame _ _ _ (by apply tensorPower_frame; exact hs), ?_⟩
  have hc := composeComparison_section b a (a ≫ b) rfl
    (Cotangent E) (Cotangent F) (Cotangent H) (cotangentIso C) (cotangentIso D)
    V s ((a ≫ b) ⁻¹ᵁ V) le_rfl le_rfl
  rw [← cotangentIso_comp_eq C D, res_refl, res_refl] at hc
  have hp := composeComparison_section b a (a ≫ b) rfl
    (Power E) (Power F) (Power H) (powerIso C) (powerIso D)
    V (tensorPowerSection S (Cotangent E) 24 V s) ((a ≫ b) ⁻¹ᵁ V) le_rfl le_rfl
  rw [res_refl, res_refl] at hp
  rw [hp]
  change (tensorComparison _ _ _ _ 24).hom.app _
    (Scheme.Modules.pullbackLocalSection _ (tensorPowerSection _ _ _ _ _)) = _
  rw [tensorComparison_section, hc]
  change _ = (tensorComparison _ _ _ _ 24).hom.app _
    (Scheme.Modules.pullbackLocalSection _ ((tensorComparison _ _ _ _ 24).hom.app _
      (Scheme.Modules.pullbackLocalSection _ (tensorPowerSection _ _ _ _ _))))
  rw [tensorComparison_section, tensorComparison_section]
  rfl

/-- Pullback on arbitrary opens, with the same fixed comparison as `pull`. -/
def localPull {S T : Scheme.{u}} {E : Family S} {F : Family T} {b : T ⟶ S}
    (C : Comparison E F b) (U : S.Opens) (V : T.Opens) (h : V ≤ b ⁻¹ᵁ U)
    (s : Γ(Power E, U)) : Γ(Power F, V) :=
  res _ h ((powerIso C).hom.app _ (Scheme.Modules.pullbackLocalSection b s))

theorem localPull_top {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) (d : Sections E) :
    localPull C ⊤ ⊤ (by simp) d = pull C d := rfl

theorem localPull_restrict {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) (U U' : S.Opens) (hU : U' ≤ U)
    (V : T.Opens) (h : V ≤ b ⁻¹ᵁ U') (s : Γ(Power E, U)) :
    localPull C U' V h (res (Power E) hU s) =
      localPull C U V (h.trans (fun _ hx => hU hx)) s := by
  unfold localPull
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

theorem localPull_comp {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a)
    (V : S.Opens) (W : T.Opens) (Z : U.Opens)
    (hC : W ≤ b ⁻¹ᵁ V) (hD : Z ≤ a ⁻¹ᵁ W) (s : Γ(Power E, V)) :
    localPull (comparisonComp C D) V Z (fun _ hz => hC (hD hz)) s =
      localPull D W Z hD (localPull C V W hC s) := by
  unfold localPull
  rw [powerIso_comp_eq, composeComparison_section b a (a ≫ b) rfl
    (Power E) (Power F) (Power H) (powerIso C) (powerIso D) V s Z
    (fun _ hz => hC (hD hz)) (fun _ hz => hC (hD hz))]
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

/-- The Cartesian universal property constructs the refinement map, including
its pointed equation, without choosing an isomorphism of abstract lines. -/
theorem comparison_refinement {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {c : U ⟶ S}
    (C : Comparison E F b) (D : Comparison E H c)
    (a : U ⟶ T) (ha : a ≫ b = c) :
    ∃ B : Comparison F H a, B.map ≫ C.map = D.map := by
  have hcomm : D.map ≫ E.p = (H.p ≫ a) ≫ b := by
    rw [Category.assoc, ha]; exact D.cartesian.w
  let f := C.cartesian.lift D.map (H.p ≫ a) hcomm
  have hf : f ≫ C.map = D.map := C.cartesian.lift_fst _ _ _
  have hp : f ≫ F.p = H.p ≫ a := C.cartesian.lift_snd _ _ _
  refine ⟨⟨f, ?_, ?_⟩, hf⟩
  · exact IsPullback.of_right (by rw [hf, ha]; exact D.cartesian) hp C.cartesian
  · apply C.cartesian.hom_ext
    · rw [Category.assoc, hf, D.pointed, Category.assoc, C.pointed,
        ← Category.assoc, ha]
    · rw [Category.assoc, hp, ← Category.assoc, CartesianIdentityIdeal.zero_section,
        Category.id_comp, Category.assoc, CartesianIdentityIdeal.zero_section,
        Category.comp_id]

/-- Changing a written presentation of the identity retains the same differential map. -/
theorem pointedDifferentialIso_points
    {R V : Type u} [CommRing R] [CommRing V] [Algebra R V]
    {X Y : Scheme.{u}} (p : X ⟶ Base R) (q : Y ⟶ Base V)
    [SmoothOfRelativeDimension 1 p] (f : Y ⟶ X)
    (hc : IsPullback f q p (Spec.map (CommRingCat.ofHom (algebraMap R V))))
    (s s' : Base R ⟶ X) (t t' : Base V ⟶ Y) (hs : s = s') (ht : t = t')
    (hz : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s)
    (hz' : t' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s') :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R V)))).map
        (pullbackEqIso hs p.kaehler).hom ≫ (pointedDifferentialIso p q f hc s' t' hz').hom =
      (pointedDifferentialIso p q f hc s t hz).hom ≫ (pullbackEqIso ht q.kaehler).hom := by
  subst s'; subst t'
  simp [pullbackEqIso]

/-- A commuting square of line comparisons induces the same square on each
actual sheafified tensor power. The proof is independent of curve presentations. -/
theorem tensorComparison_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M M' : X.Modules} {N N' : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (a : M ≅ M') (b : N ≅ N')
    (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (e' : (Scheme.Modules.pullback f).obj M' ≅ N')
    (h : (Scheme.Modules.pullback f).map a.hom ≫ e'.hom = e.hom ≫ b.hom)
    (n : ℕ) :
    (Scheme.Modules.pullback f).map (powerCongr X a n).hom ≫
        (tensorComparison f M' N' e' n).hom =
      (tensorComparison f M N e n).hom ≫ (powerCongr Y b n).hom := by
  apply hom_ext_frames
  intro x
  obtain ⟨U, s, hx, hs⟩ := hM.exists_isFrameOn (f x)
  have hs' : IsFrame M U s := fun V hV => hs hV hV
  refine ⟨f ⁻¹ᵁ U, Scheme.Modules.pullbackLocalSection f
    (tensorPowerSection X M n U s), hx,
    pullback_frame _ _ _ (tensorPower_frame M s hs' n), ?_⟩
  have hn := congrArg (fun g => g.app (f ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection f s)) h
  change e'.hom.app _ (((Scheme.Modules.pullback f).map a.hom).app _
    (Scheme.Modules.pullbackLocalSection f s)) =
      b.hom.app _ (e.hom.app _ (Scheme.Modules.pullbackLocalSection f s)) at hn
  rw [← Scheme.Modules.pullbackLocalSection_app] at hn
  change (tensorComparison f M' N' e' n).hom.app _
      (((Scheme.Modules.pullback f).map (powerCongr X a n).hom).app _
        (Scheme.Modules.pullbackLocalSection f (tensorPowerSection X M n U s))) =
    (powerCongr Y b n).hom.app _ ((tensorComparison f M N e n).hom.app _
      (Scheme.Modules.pullbackLocalSection f (tensorPowerSection X M n U s)))
  rw [← Scheme.Modules.pullbackLocalSection_app, powerCongr_section,
    tensorComparison_section, tensorComparison_section, powerCongr_section]
  exact congrArg (tensorPowerSection Y N' n (f ⁻¹ᵁ U)) hn

section WeierstrassComparison
variable {R V : Type u} [CommRing R] [CommRing V]
    {W : WeierstrassCurve R} [W.IsElliptic] {Z : WeierstrassCurve V} [Z.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law V Z) (hH : IsOriginLaw V Z H) (ι : R →+* V)
    (C : Comparison (weierstrassFamily R W G hG) (weierstrassFamily V Z H hH)
      (Spec.map (CommRingCat.ofHom ι)))

def hodgeComparison : ArithmeticThetaArbitraryDiscriminantR0243.Comparison R V W Z ι where
  map := C.map
  cartesian := C.cartesian
  pointed := by
    rw [← weierstrass_zero R W G hG, ← weierstrass_zero V Z H hH]
    exact C.pointed

theorem weierstrassHodgeIso_natural :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map
        (weierstrassHodgeIso R W G hG).hom ≫
      (ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge
        (hodgeComparison G hG H hH ι C)).hom =
    (cotangentIso C).hom ≫ (weierstrassHodgeIso V Z H hH).hom := by
  let E := weierstrassFamily R W G hG
  let F := weierstrassFamily V Z H hH
  letI : Algebra R V := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 E.p := E.dimension
  have hn := (affine_conormal_hodge_naturality R V E F ι C.map C.cartesian C.pointed).2.2
    _ (cartesian_identity_ideal (Base R) (Base V) E F _ C.map C.cartesian C.pointed).exists.choose_spec
  have ht := pointedDifferentialIso_points E.p F.p C.map C.cartesian
    E.zero (origin R W) F.zero (origin V Z)
    (weierstrass_zero R W G hG) (weierstrass_zero V Z H hH)
    C.pointed (hodgeComparison G hG H hH ι C).pointed
  change (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map
      (affineDifferential E ≫ (pullbackEqIso (weierstrass_zero R W G hG) E.p.kaehler).hom) ≫
      (pointedDifferentialIso E.p F.p C.map C.cartesian (origin R W) (origin V Z)
        (hodgeComparison G hG H hH ι C).pointed).hom =
    (cotangentIso C).hom ≫ affineDifferential F ≫
      (pullbackEqIso (weierstrass_zero V Z H hH) F.p.kaehler).hom
  rw [Functor.map_comp, Category.assoc]
  refine (congrArg (fun f =>
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map
      (affineDifferential E) ≫ f) ht).trans ?_
  simpa only [Category.assoc, affineHodgeComparison, cotangentIso] using congrArg (fun f => f ≫
    (pullbackEqIso (weierstrass_zero V Z H hH) F.p.kaehler).hom) hn

set_option maxRecDepth 4096 in
theorem weierstrassPowerIso_natural :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map
        (powerCongr (Base R) (weierstrassHodgeIso R W G hG) 24).hom ≫
      (ArithmeticThetaArbitraryDiscriminantR0243.comparisonPower
        (hodgeComparison G hG H hH ι C)).hom =
    (powerIso C).hom ≫ (powerCongr (Base V) (weierstrassHodgeIso V Z H hH) 24).hom := by
  exact tensorComparison_natural (Spec.map (CommRingCat.ofHom ι))
    (cotangent_invertible (weierstrassFamily R W G hG))
    (weierstrassHodgeIso R W G hG) (weierstrassHodgeIso V Z H hH)
    (cotangentIso C)
    (ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge
      (hodgeComparison G hG H hH ι C))
    (weierstrassHodgeIso_natural G hG H hH ι C) 24

/-- The fixed conormal identification intertwines full global-section pullbacks. -/
theorem weierstrassValue_pull (d : Sections (weierstrassFamily R W G hG)) :
    weierstrassValue V Z H hH (pull C d) =
      ArithmeticThetaArbitraryDiscriminantR0243.pull (hodgeComparison G hG H hH ι C)
        (weierstrassValue R W G hG d) := by
  let b := Spec.map (CommRingCat.ofHom ι)
  have hn := congrArg (fun f => f.app (b ⁻¹ᵁ ⊤)
    (Scheme.Modules.pullbackLocalSection b d)) (weierstrassPowerIso_natural G hG H hH ι C)
  change (ArithmeticThetaArbitraryDiscriminantR0243.comparisonPower
      (hodgeComparison G hG H hH ι C)).hom.app _
      (((Scheme.Modules.pullback b).map
        (powerCongr (Base R) (weierstrassHodgeIso R W G hG) 24).hom).app _
        (Scheme.Modules.pullbackLocalSection b d)) =
    (powerCongr (Base V) (weierstrassHodgeIso V Z H hH) 24).hom.app _
      ((powerIso C).hom.app _ (Scheme.Modules.pullbackLocalSection b d)) at hn
  rw [← Scheme.Modules.pullbackLocalSection_app] at hn
  unfold weierstrassValue pull ArithmeticThetaArbitraryDiscriminantR0243.pull
  rw [← hom_res]
  exact congrArg (res (HodgePower V Z 24) (show ⊤ ≤ b ⁻¹ᵁ ⊤ by simp)) hn.symm

end WeierstrassComparison

theorem comparison_ext {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C D : Comparison E F b) (h : C.map = D.map) : C = D := by
  cases C; cases D; cases h; rfl

theorem localPull_refinement {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {c : U ⟶ S}
    (C : Comparison E F b) (D : Comparison E H c)
    {a : U ⟶ T} (B : Comparison F H a) (hm : B.map ≫ C.map = D.map)
    (ha : a ≫ b = c) (V : S.Opens) (W : T.Opens) (Z : U.Opens)
    (hC : W ≤ b ⁻¹ᵁ V) (hB : Z ≤ a ⁻¹ᵁ W) (hD : Z ≤ c ⁻¹ᵁ V)
    (s : Γ(Power E, V)) :
    localPull D V Z hD s = localPull B W Z hB (localPull C V W hC s) := by
  subst c
  have he : comparisonComp C B = D := comparison_ext _ _ hm
  rw [← he]
  exact localPull_comp C B V W Z hC hB s

section NormalizedCotangent
variable (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)

theorem normalized_cotangent_exists :
    ∃ d : Sections (weierstrassFamily R W G hG),
      ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W (weierstrassValue R W G hG d) := by
  obtain ⟨d, hd, _⟩ :=
    ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_weierstrass_discriminant R W
  obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso
    ((powerCongr (Base R) (weierstrassHodgeIso R W G hG) 24).hom.app ⊤)).surjective d
  refine ⟨s, ?_⟩
  unfold weierstrassValue
  rw [hs]
  exact hd.1

theorem normalized_cotangent_unique (d e : Sections (weierstrassFamily R W G hG))
    (hd : ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W (weierstrassValue R W G hG d))
    (he : ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W (weierstrassValue R W G hG e)) :
    d = e := by
  obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model R W
  apply (ConcreteCategory.bijective_of_isIso
    ((powerCongr (Base R) (weierstrassHodgeIso R W G hG) 24).hom.app ⊤)).injective
  exact (hd M).trans (he M).symm

theorem normalized_cotangent_pull
    (V : Type u) [CommRing V] [Algebra ℚ V]
    (Z : WeierstrassCurve V) [Z.IsElliptic] (H : Law V Z) (hH : IsOriginLaw V Z H)
    (ι : R →+* V) (C : Comparison (weierstrassFamily R W G hG)
      (weierstrassFamily V Z H hH) (Spec.map (CommRingCat.ofHom ι)))
    (d : Sections (weierstrassFamily R W G hG))
    (hd : ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W (weierstrassValue R W G hG d)) :
    ArithmeticThetaArbitraryDiscriminantR0243.IsD2 Z
      (weierstrassValue V Z H hH (pull C d)) := by
  obtain ⟨e, he, _⟩ :=
    ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_weierstrass_discriminant V Z
  let ι' : R →ₐ[ℚ] V := { ι with commutes' := ι.map_rat_algebraMap }
  have hn := ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_discriminant_naturality
    R W V Z ι' (hodgeComparison G hG H hH ι C)
    (weierstrassValue R W G hG d) e hd he.1
  rw [weierstrassValue_pull G hG H hH ι C, hn]
  exact he.1

end NormalizedCotangent

theorem restriction_eq_of_localPull_eq
    {S T : Scheme.{u}} {E : Family S} {F : Family T} {b : T ⟶ S}
    (C : Comparison E F b) [IsOpenImmersion b]
    (U : S.Opens) (hU : b.opensRange ≤ U) (h : (⊤ : T.Opens) ≤ b ⁻¹ᵁ U)
    (s t : Γ(Power E, U)) (he : localPull C U ⊤ h s = localPull C U ⊤ h t) :
    res (Power E) hU s = res (Power E) hU t := by
  apply restriction_eq_of_pullback_eq b (Power E) U hU
  apply (ConcreteCategory.bijective_of_isIso ((powerIso C).hom.app _)).injective
  exact (res_bijective (Power F) h le_top).injective he

/-- An arbitrary affine neighborhood, with no hypotheses on its coefficient ring. -/
structure AffineNeighborhood (X : Scheme.{u}) (U : X.Opens) (x : X) where
  ring : Type u
  [commRing : CommRing ring]
  base : Base ring ⟶ X
  openImmersion : IsOpenImmersion base
  contains : x ∈ Set.range base
  inside : Set.range base ⊆ U

attribute [local instance] AffineNeighborhood.commRing

theorem affine_neighborhood (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U) :
    Nonempty (AffineNeighborhood X U x) := by
  obtain ⟨R, b, hb, r, hr⟩ := U.toScheme.exists_Spec_apply_eq ⟨x, hx⟩
  letI := hb
  refine ⟨⟨R, b ≫ U.ι, inferInstance, ⟨r, ?_⟩, ?_⟩⟩
  · exact congrArg Subtype.val hr
  · rintro _ ⟨z, rfl⟩
    exact (b z).property

theorem weierstrass_comparison_base_change
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    {T : Type u} [CommRing T] (ρ : R →+* T) :
    ∃ (H : Law T (W.map ρ)) (hH : IsOriginLaw T (W.map ρ) H)
      , Nonempty (Comparison (weierstrassFamily R W G hG)
        (weierstrassFamily T (W.map ρ) H hH) (Spec.map (CommRingCat.ofHom ρ))) := by
  obtain ⟨H, hH, f, hf, hz, _⟩ := weierstrass_base_change W G hG ρ
  refine ⟨H, hH, ⟨⟨f, hf, ?_⟩⟩⟩
  rw [weierstrass_zero, weierstrass_zero]
  exact hz

section Charts
variable {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    {σ : S ⟶ Base k} {E : Family S} (P : LocalPresentation k S σ E)

def chartFamily : Family (Base P.ring) := by
  letI := P.commRing
  letI := P.elliptic
  exact weierstrassFamily P.ring P.equation P.law P.originLaw

def chartComparison : Comparison E (chartFamily P) P.base := by
  letI := P.commRing
  letI := P.elliptic
  refine ⟨P.comparison, P.cartesian, ?_⟩
  rw [show (chartFamily P).zero = origin P.ring P.equation from
    weierstrass_zero P.ring P.equation P.law P.originLaw]
  exact P.zero_eq

def chartImage : S.Opens := by
  letI := P.openImmersion
  exact P.base.opensRange

theorem chart_preimage : (⊤ : (Base P.ring).Opens) ≤ P.base ⁻¹ᵁ chartImage P := by
  letI := P.openImmersion
  rw [chartImage, Scheme.Hom.preimage_opensRange]

def chartHodgeIso : Cotangent (chartFamily P) ≅ Hodge P.ring P.equation := by
  letI := P.commRing
  letI := P.elliptic
  exact weierstrassHodgeIso P.ring P.equation P.law P.originLaw

def chartPowerIso : (Scheme.Modules.pullback P.base).obj (Power E) ≅
    HodgePower P.ring P.equation 24 :=
  powerIso (chartComparison P) ≪≫ powerCongr (Base P.ring) (chartHodgeIso P) 24

/-- The arbitrary-ring theorem supplies a normalized frame on each actual chart. -/
theorem chart_frame_exists :
    ∃ s : Γ(Power E, chartImage P), IsFrame (Power E) (chartImage P) s ∧
      (letI : CommRing P.ring := P.commRing
       letI : Algebra k P.ring := P.algebra
       letI : Algebra ℚ P.ring :=
         ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
       ArithmeticThetaArbitraryDiscriminantR0243.IsD2 P.equation
         (res _ (chart_preimage P) ((chartPowerIso P).hom.app _
           (Scheme.Modules.pullbackLocalSection P.base s)))) := by
  letI := P.commRing
  letI := P.algebra
  letI := P.elliptic
  letI := P.openImmersion
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨d, hd, _⟩ :=
    ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_weierstrass_discriminant
      P.ring P.equation
  obtain ⟨s, hs, he⟩ := frame_lift_open P.base (Power E)
    (HodgePower P.ring P.equation 24) (chartPowerIso P) d hd.2
  exact ⟨s, hs, he.symm ▸ hd.1⟩

def chartSection : Γ(Power E, chartImage P) := (chart_frame_exists P).choose

theorem chartSection_frame : IsFrame (Power E) (chartImage P) (chartSection P) :=
  (chart_frame_exists P).choose_spec.1

set_option maxRecDepth 4096 in
theorem chartSection_normalized :
    letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
    ArithmeticThetaArbitraryDiscriminantR0243.IsD2 P.equation
      (weierstrassValue P.ring P.equation P.law P.originLaw
        (localPull (chartComparison P) (chartImage P) ⊤ (chart_preimage P) (chartSection P))) := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  unfold weierstrassValue localPull
  erw [← hom_res]
  exact (chart_frame_exists P).choose_spec.2

/-- Every test factoring through the chart receives a normalized section. -/
theorem chartSection_test (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    {b : Base R ⟶ S} (C : Comparison E (weierstrassFamily R W G hG) b)
    (ι : P.ring →+* R) (hι : Spec.map (CommRingCat.ofHom ι) ≫ P.base = b)
    (h : (⊤ : (Base R).Opens) ≤ b ⁻¹ᵁ chartImage P) :
    ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W
      (weierstrassValue R W G hG (localPull C (chartImage P) ⊤ h (chartSection P))) := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨B, hB⟩ := comparison_refinement (chartComparison P) C
    (Spec.map (CommRingCat.ofHom ι)) hι
  have he := localPull_refinement (chartComparison P) C B hB hι
    (chartImage P) ⊤ ⊤ (chart_preimage P) (by simp) h (chartSection P)
  rw [he, localPull_top]
  exact normalized_cotangent_pull P.ring P.equation P.law P.originLaw
    R W G hG ι B _ (chartSection_normalized P)

theorem factor_chart {R : Type u} [CommRing R] (b : Base R ⟶ S)
    (h : Set.range b ⊆ chartImage P) :
    ∃ ι : P.ring →+* R, Spec.map (CommRingCat.ofHom ι) ≫ P.base = b := by
  letI := P.openImmersion
  let a := IsOpenImmersion.lift P.base b h
  refine ⟨(Spec.preimage a).hom, ?_⟩
  change Spec.map (Spec.preimage a) ≫ P.base = b
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The accepted local presentation theorem covers every point of the base. -/
theorem chart_cover : ∀ x : S, ∃ P : LocalPresentation k S σ E, x ∈ chartImage P :=
  scheme_local_weierstrass k S σ E

/-- Equality on overlaps is checked on arbitrary affine neighborhoods of a chart. -/
theorem chartSection_overlap (Q : LocalPresentation k S σ E) :
    res (Power E) (inf_le_left : chartImage P ⊓ chartImage Q ≤ chartImage P) (chartSection P) =
      res (Power E) (inf_le_right : chartImage P ⊓ chartImage Q ≤ chartImage Q) (chartSection Q) := by
  apply sections_eq_local
  intro x hx
  letI := P.openImmersion
  letI := Q.openImmersion
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨y, hy⟩ := hx.1
  have hyU : y ∈ P.base ⁻¹ᵁ chartImage Q := by
    change P.base y ∈ chartImage Q
    rw [hy]; exact hx.2
  let N := Classical.choice (affine_neighborhood (Base P.ring)
    (P.base ⁻¹ᵁ chartImage Q) y hyU)
  letI := N.openImmersion
  let ρ : P.ring →+* N.ring := (Spec.preimage N.base).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = N.base := Spec.map_preimage N.base
  letI : Algebra ℚ N.ring := (ρ.comp (algebraMap ℚ P.ring)).toAlgebra
  obtain ⟨H, hH, ⟨B⟩⟩ := weierstrass_comparison_base_change P.equation P.law P.originLaw ρ
  let Z := comparisonComp (chartComparison P) B
  let b := Spec.map (CommRingCat.ofHom ρ) ≫ P.base
  letI : IsOpenImmersion b := by dsimp [b]; rw [hρ]; infer_instance
  have hP : (⊤ : (Base N.ring).Opens) ≤ b ⁻¹ᵁ chartImage P := by
    intro z _
    exact ⟨Spec.map (CommRingCat.ofHom ρ) z, rfl⟩
  have hQ : (⊤ : (Base N.ring).Opens) ≤ b ⁻¹ᵁ chartImage Q := by
    intro z _
    change P.base (Spec.map (CommRingCat.ofHom ρ) z) ∈ chartImage Q
    rw [hρ]
    exact N.inside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := factor_chart Q b (by rintro _ ⟨z, rfl⟩; exact hQ (Set.mem_univ z))
  have hp := chartSection_test P N.ring (P.equation.map ρ) H hH Z ρ rfl hP
  have hq := chartSection_test Q N.ring (P.equation.map ρ) H hH Z τ hτ hQ
  have he := normalized_cotangent_unique N.ring (P.equation.map ρ) H hH _ _ hp hq
  have hU : b.opensRange ≤ chartImage P ⊓ chartImage Q := by
    rintro _ ⟨z, rfl⟩
    exact ⟨hP (Set.mem_univ z), hQ (Set.mem_univ z)⟩
  have hUZ : (⊤ : (Base N.ring).Opens) ≤ b ⁻¹ᵁ (chartImage P ⊓ chartImage Q) := by
    intro z _
    exact ⟨hP (Set.mem_univ z), hQ (Set.mem_univ z)⟩
  refine ⟨b.opensRange, ?_, hU, ?_⟩
  · obtain ⟨z, hz⟩ := N.contains
    refine ⟨z, ?_⟩
    change P.base (Spec.map (CommRingCat.ofHom ρ) z) = x
    rw [hρ, hz, hy]
  · apply restriction_eq_of_localPull_eq Z _ hU hUZ
    rw [localPull_restrict, localPull_restrict]
    exact he

theorem glue_chart_sections :
    ∃ d : Sections E, ∀ P : LocalPresentation k S σ E,
      res (Power E) le_top d = chartSection P := by
  let V := fun P : LocalPresentation k S σ E => chartImage P
  have hc : (⨆ P, V P) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (chart_cover (k := k) (σ := σ) (E := E) x)
  obtain ⟨d, hd, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(Power E).presheaf, (Power E).isSheaf⟩ V ⊤ (fun _ => homOfLE le_top)
    hc.ge (fun P => chartSection P) (fun P Q => chartSection_overlap P Q)
  exact ⟨d, hd⟩

set_option maxRecDepth 4096 in
/-- The normalization of the glued section is checked locally on an arbitrary
test scheme. In particular the affine rings need not be reduced or normal. -/
theorem glued_section_test (d : Sections E)
    (hd : ∀ P : LocalPresentation k S σ E, res (Power E) le_top d = chartSection P)
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    {b : Base R ⟶ S} (C : Comparison E (weierstrassFamily R W G hG) b) :
    ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W
      (weierstrassValue R W G hG (pull C d)) := by
  obtain ⟨e, he⟩ := normalized_cotangent_exists R W G hG
  have heq : pull C d = e := by
    apply sections_eq_local
    intro x _
    obtain ⟨Q, hQ⟩ := chart_cover (k := k) (σ := σ) (E := E) (b x)
    let N := Classical.choice (affine_neighborhood (Base R) (b ⁻¹ᵁ chartImage Q) x hQ)
    letI := N.openImmersion
    let ρ : R →+* N.ring := (Spec.preimage N.base).hom
    have hρ : Spec.map (CommRingCat.ofHom ρ) = N.base := Spec.map_preimage N.base
    letI : Algebra ℚ N.ring := (ρ.comp (algebraMap ℚ R)).toAlgebra
    obtain ⟨H, hH, ⟨B⟩⟩ := weierstrass_comparison_base_change W G hG ρ
    let Z := comparisonComp C B
    let a := Spec.map (CommRingCat.ofHom ρ)
    letI : IsOpenImmersion a := by dsimp [a]; rw [hρ]; infer_instance
    have hZ : (⊤ : (Base N.ring).Opens) ≤ (a ≫ b) ⁻¹ᵁ chartImage Q := by
      intro z _
      change b (Spec.map (CommRingCat.ofHom ρ) z) ∈ chartImage Q
      rw [hρ]
      exact N.inside ⟨z, rfl⟩
    obtain ⟨τ, hτ⟩ := factor_chart Q (a ≫ b)
      (by rintro _ ⟨z, rfl⟩; exact hZ (Set.mem_univ z))
    have hn := chartSection_test Q N.ring (W.map ρ) H hH Z τ hτ hZ
    have hz : ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (W.map ρ)
        (weierstrassValue N.ring (W.map ρ) H hH (pull Z d)) := by
      change ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (W.map ρ)
        (weierstrassValue N.ring (W.map ρ) H hH (localPull Z ⊤ ⊤ (by simp) d))
      rw [← localPull_restrict Z ⊤ (chartImage Q) le_top ⊤ hZ d, hd Q]
      exact hn
    have he' := normalized_cotangent_pull R W G hG N.ring (W.map ρ) H hH ρ B e he
    have hze := normalized_cotangent_unique N.ring (W.map ρ) H hH _ _ hz he'
    have hcomp : pull Z d = pull B (pull C d) :=
      localPull_comp C B ⊤ ⊤ ⊤ (by simp) (by simp) d
    have hp : localPull B ⊤ ⊤ (by simp) (pull C d) = localPull B ⊤ ⊤ (by simp) e :=
      hcomp.symm.trans hze
    refine ⟨a.opensRange, ?_, le_top, ?_⟩
    · change x ∈ Set.range a
      simpa only [a, hρ] using N.contains
    · exact restriction_eq_of_localPull_eq B ⊤ le_top (by simp) _ _ hp
  rw [heq]
  exact he

end Charts

end SchemeDiscriminantExistence

open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203

/-- The canonical discriminant-square section on every characteristic-zero scheme family. -/
theorem scheme_discriminant_existence :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S), ∃ d : Sections E, IsD2 k σ E d := by
  intro k _ _ S σ E
  obtain ⟨d, hd⟩ := SchemeDiscriminantExistence.glue_chart_sections (k := k) (σ := σ) (E := E)
  refine ⟨d, ?_⟩
  intro R _ _ W _ G hG b _ C
  letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  exact SchemeDiscriminantExistence.glued_section_test d hd R W G hG C

#print axioms scheme_discriminant_existence
end ArithmeticThetaSchemeDiscriminantR0244
