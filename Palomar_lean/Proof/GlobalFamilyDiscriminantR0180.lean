module

public import EllipticFamilyWeierstrassAtlasR0180
public import RelativeInitialSectionNaturalityR0171

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaOpenHodgeR0180
namespace GlobalFamilyDiscriminantR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower

section Weierstrass
variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)

include hG

/-- Construct the normalized function for the specified group law. -/
lemma normalized_exists (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    ∃ g : (Curve R W).functionField, Normalized R W G c g := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  obtain ⟨f, hf, _⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6
  let g := C.field.symm f
  have hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g) := by
    simpa only [g, RingEquiv.apply_symm_apply] using hf
  exact ⟨g, (RelativeExistence.relative_of_generic R W G hG C c hc hc6 g hg).1,
    fun D => RelativeExistence.comparison_independent R W G C D c hc hc6 g hg⟩

lemma normalized_unique (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g g' : (Curve R W).functionField)
    (hg : Normalized R W G c g) (hg' : Normalized R W G c g') : g = g' := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  apply C.field.injective
  exact (ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6).unique
      (hg.2 C) (hg'.2 C)

/-- A canonical local D2 frame, independent of the chosen normalized function. -/
lemma local_discriminant_exists :
    ∃! d : Γ(HodgePower R W 24, ⊤),
      IsFrame (HodgePower R W 24) ⊤ d ∧
      ∀ g : (Curve R W).functionField, Normalized R W G 5 g →
        RepresentsInitial R W G 5 g d := by
  obtain ⟨g, hg⟩ := normalized_exists R W G hG 5 (by norm_num) (by norm_num)
  obtain ⟨d, hd, hu⟩ := relative_initial_hodge_section R W G hG
    5 (by norm_num) (by norm_num) g hg
  refine ⟨d, ⟨hd.2, ?_⟩, ?_⟩
  · intro g' hg'
    rw [← normalized_unique R W G hG 5 (by norm_num) (by norm_num) g g' hg hg']
    exact hd.1
  · intro d' hd'
    exact hu d' ⟨hd'.2 g hg, hd'.1⟩

/-- The locally constructed section. -/
def localD : Γ(HodgePower R W 24, ⊤) :=
  (local_discriminant_exists R W G hG).exists.choose

lemma localD_frame : IsFrame (HodgePower R W 24) ⊤ (localD R W G hG) :=
  (local_discriminant_exists R W G hG).exists.choose_spec.1

lemma localD_represents (g : (Curve R W).functionField) (hg : Normalized R W G 5 g) :
    RepresentsInitial R W G 5 g (localD R W G hG) :=
  (local_discriminant_exists R W G hG).exists.choose_spec.2 g hg

variable (T : Type u) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Algebra ℚ T]
    (Wt : WeierstrassCurve T) [Wt.IsElliptic]
    [IsIntegral (Curve T Wt)] [IsLocallyNoetherian (Curve T Wt)]
    [IsIntegral (GenericCurve T Wt)] [IsLocallyNoetherian (GenericCurve T Wt)]
    (Gt : Law T Wt) (hGt : IsOriginLaw T Wt Gt)

/-- Naturality of the constructed local frames, including specializations. -/
lemma localD_naturality (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : IsBaseChange R W G T Wt Gt ρ b) :
    InitialBaseChange R W T Wt ρ 24 (hodgePowerIso R W G T Wt Gt ρ b hb 24)
      (localD R W G hG) (localD T Wt Gt hGt) := by
  obtain ⟨g, hg⟩ := normalized_exists R W G hG 5 (by norm_num) (by norm_num)
  obtain ⟨gt, hgt⟩ := normalized_exists T Wt Gt hGt 5 (by norm_num) (by norm_num)
  exact relative_initial_section_naturality R W G hG T Wt Gt hGt ρ b hb
    5 (by norm_num) (by norm_num) g hg gt hgt
    (localD R W G hG) (localD_represents R W G hG g hg)
    (localD T Wt Gt hGt) (localD_represents T Wt Gt hGt gt hgt)
    (hodgePowerIso R W G T Wt Gt ρ b hb 24)
    (hodgePowerIso_spec R W G T Wt Gt ρ b hb 24)

end Weierstrass

lemma frame_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {U : X.Opens} (s : Γ(M, U)) (hs : IsFrame M U s) :
    IsFrame N U (e.hom.app U s) := by
  intro V hV
  have he : Function.Bijective (e.hom.app V) :=
    ConcreteCategory.bijective_of_isIso (e.hom.app V)
  have h := he.comp (hs V hV)
  simpa only [Function.comp_def, hom_res, Scheme.Modules.Hom.app_smul] using h

lemma pullSection_frame {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤))
    (hs : IsFrame (power E n) ⊤ s) :
    IsFrame (HodgePower R W n) ⊤ (pullSection C n s) := by
  exact frame_restrict _ (by simp) _
    (frame_iso (powerComparison C n) _ (pullback_frame _ _ s hs))

/-- A refinement between tests is constructed from the actual Cartesian square. -/
lemma test_refinement {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt}
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (hρ : ρ.comp C.scalar = D.scalar) :
    ∃ b : Curve T Wt ⟶ Curve R W,
      b ≫ C.map = D.map ∧ IsBaseChange R W G T Wt Gt ρ b := by
  have hbase : baseMap R T ρ ≫ baseMap S R C.scalar = baseMap S T D.scalar := by
    unfold baseMap
    rw [← Spec.map_comp]
    exact congrArg (fun f : S →+* T => Spec.map (CommRingCat.ofHom f)) hρ
  have hcomm : D.map ≫ E.projection =
      (structureMap T Wt ≫ baseMap R T ρ) ≫ baseMap S R C.scalar := by
    rw [Category.assoc, hbase]
    exact D.cartesian.w
  let b := C.cartesian.lift D.map (structureMap T Wt ≫ baseMap R T ρ) hcomm
  have hb : b ≫ C.map = D.map := C.cartesian.lift_fst _ _ _
  have hp : b ≫ structureMap R W = structureMap T Wt ≫ baseMap R T ρ :=
    C.cartesian.lift_snd _ _ _
  change ∃ b : Curve T Wt ⟶ Curve R W, b ≫ C.map = D.map ∧
    IsPullback b (structureMap T Wt) (structureMap R W) (baseMap R T ρ) ∧
      origin T Wt ≫ b = baseMap R T ρ ≫ origin R W ∧
        ∀ n, Gt.schemeNsmul n ≫ b = b ≫ G.schemeNsmul n
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  have hot : origin T Wt ≫ structureMap T Wt = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect T Wt).property
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · exact IsPullback.of_right (by rw [hb, hbase]; exact D.cartesian) hp C.cartesian
  · apply C.cartesian.hom_ext
    · rw [Category.assoc, hb, D.origin_eq, Category.assoc, C.origin_eq,
        ← Category.assoc, hbase]
    · rw [Category.assoc, hp, ← Category.assoc, hot,
        Category.id_comp, Category.assoc, ho, Category.comp_id]
  · intro n
    apply C.cartesian.hom_ext
    · rw [Category.assoc, hb, D.nsmul_eq, Category.assoc, C.nsmul_eq,
        ← Category.assoc, hb]
    · rw [Category.assoc, hp, ← Category.assoc, Gt.schemeNsmul_over,
        Category.assoc, G.schemeNsmul_over, hp]

def familyLocalPower {S : Type u} [CommRing S] (E : EllipticFamily S)
    (n : ℕ) (U : E.curve.Opens) (a : Γ(E.curve, U)) :
    Γ(power E n, zero E ⁻¹ᵁ U) :=
  tensorPowerSection (Base S) (hodge E) n (zero E ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection (zero E)
      (ArithmeticThetaCompactifiedDifferentialR0145.relativeD E.projection U a))

/-- The canonical comparison sends actual local differentials and their powers
to the corresponding differentials on the test, on every smaller open. -/
lemma powerComparison_localPower {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (U : E.curve.Opens) (a : Γ(E.curve, U))
    (V : (Base R).Opens)
    (h₁ : V ≤ baseMap S R C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    res (HodgePower R W n) h₁
      ((powerComparison C n).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar)
          (familyLocalPower E n U a))) =
    res (HodgePower R W n) h₂ (localPower R W n (C.map ⁻¹ᵁ U) (C.map.app U a)) := by
  letI : Algebra S R := C.scalar.toAlgebra
  letI := E.smooth
  change res _ h₁ ((tensorComparison _ _ _ _ n).hom.app _
    (Scheme.Modules.pullbackLocalSection _ (tensorPowerSection _ _ n _ _))) = _
  rw [tensorComparison_section]
  change (tensorPower (Base R) (Hodge R W) n).presheaf.map (homOfLE h₁).op
    (tensorPowerSection _ _ n _ _) =
      (tensorPower (Base R) (Hodge R W) n).presheaf.map (homOfLE h₂).op
        (tensorPowerSection _ _ n _ _)
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection (Base R) (Hodge R W) n V)
    (pointedDifferentialIso_D E.projection (structureMap R W) C.map C.cartesian
      (zero E) (origin R W) C.origin_eq U a V h₁ h₂)

lemma res_bijective {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (h' : U ≤ V) : Function.Bijective (res M h) := by
  let e : V ≅ U := eqToIso (le_antisymm h h')
  have he : homOfLE h = e.hom := Subsingleton.elim _ _
  unfold res
  rw [he]
  exact ConcreteCategory.bijective_of_isIso _

/-- Descent of the frame property through an open immersion onto its image. -/
lemma frame_of_pullback_open {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U))
    (hs : IsFrame ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection f s)) : IsFrame M U s := by
  intro V hV
  have hsec := Scheme.Modules.bijective_unit_app_of_le_opensRange f M V (hV.trans hU)
  haveI := f.isIso_app V (hV.trans hU)
  have hscalar := ConcreteCategory.bijective_of_isIso (f.app V)
  have h := (hs (f ⁻¹ᵁ V) (fun _ hx => hV hx)).comp hscalar
  have heq : (fun a : Γ(X, V) => f.app V a •
      res ((Scheme.Modules.pullback f).obj M) (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => hV hx)
        (Scheme.Modules.pullbackLocalSection f s)) =
      (fun a : Γ(X, V) => Scheme.Modules.pullbackLocalSection f (a • res M hV s)) := by
    funext a
    rw [InitialSectionNaturality.pullback_res, Scheme.Modules.pullbackLocalSection_smul]
  change Function.Bijective (fun a : Γ(X, V) => f.app V a • _) at h
  rw [heq] at h
  exact (Function.Bijective.of_comp_iff' hsec (fun a : Γ(X, V) => a • res M hV s)).mp h

/-- Every intrinsic frame on a chart lifts to a frame on its open image. -/
lemma frame_lift_open {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (N : Y.Modules) (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (d : Γ(N, ⊤)) (hd : IsFrame N ⊤ d) :
    ∃ s : Γ(M, f.opensRange), IsFrame M f.opensRange s ∧
      res N (by rw [f.preimage_opensRange])
        (e.hom.app _ (Scheme.Modules.pullbackLocalSection f s)) = d := by
  let h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ f.opensRange := by rw [f.preimage_opensRange]
  have hb := (res_bijective N h le_top).comp
    ((ConcreteCategory.bijective_of_isIso (e.hom.app (f ⁻¹ᵁ f.opensRange))).comp
      (Scheme.Modules.bijective_unit_app_of_le_opensRange f M f.opensRange le_rfl))
  obtain ⟨s, hs⟩ := hb.surjective d
  refine ⟨s, ?_, hs⟩
  apply frame_of_pullback_open f M f.opensRange le_rfl
  have hds : IsFrame N (f ⁻¹ᵁ f.opensRange)
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection f s)) := by
    have hres := frame_restrict N (V := f ⁻¹ᵁ f.opensRange) le_top d hd
    change res N h (e.hom.app _ (Scheme.Modules.pullbackLocalSection f s)) = d at hs
    rw [← hs, res_res, res_refl] at hres
    exact hres
  have he := frame_iso e.symm _ hds
  simpa only [Iso.symm_hom, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply] using he

def chartOpen {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E) :
    (Base S).Opens := by
  letI := C.openImmersion
  exact (baseMap S C.ring C.comparison.scalar).opensRange

lemma chart_preimage {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E) :
    (⊤ : (Base C.ring).Opens) ≤ baseMap S C.ring C.comparison.scalar ⁻¹ᵁ chartOpen C := by
  letI := C.openImmersion
  rw [chartOpen, Scheme.Hom.preimage_opensRange]

def chartPull {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E)
    (s : Γ(power E 24, chartOpen C)) : Γ(HodgePower C.ring C.equation 24, ⊤) :=
  res _ (chart_preimage C) ((powerComparison C.comparison 24).hom.app _
    (Scheme.Modules.pullbackLocalSection (baseMap S C.ring C.comparison.scalar) s))

/-- The intrinsic local D2 is a genuine frame on the chart image in the original
base, rather than merely a section of an independently chosen line. -/
lemma chart_frame_exists {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E) :
    ∃ s : Γ(power E 24, chartOpen C), IsFrame (power E 24) (chartOpen C) s ∧
      ∀ [IsIntegral (Curve C.ring C.equation)] [IsLocallyNoetherian (Curve C.ring C.equation)]
        [IsIntegral (GenericCurve C.ring C.equation)]
        [IsLocallyNoetherian (GenericCurve C.ring C.equation)]
        (g : (Curve C.ring C.equation).functionField),
        Normalized C.ring C.equation C.law 5 g →
          RepresentsInitial C.ring C.equation C.law 5 g (chartPull C s) := by
  letI := C.openImmersion
  have hgeom := relative_curve_geometry C.ring C.equation
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  obtain ⟨s, hs, he⟩ := frame_lift_open (baseMap S C.ring C.comparison.scalar)
    (power E 24) (HodgePower C.ring C.equation 24) (powerComparison C.comparison 24)
    (localD C.ring C.equation C.law C.originLaw)
    (localD_frame C.ring C.equation C.law C.originLaw)
  refine ⟨s, hs, ?_⟩
  intro _ _ _ _ g hg
  change chartPull C s = localD C.ring C.equation C.law C.originLaw at he
  rw [he]
  exact localD_represents C.ring C.equation C.law C.originLaw g hg

/-- Composition of specified pullback isomorphisms, retaining the exact maps. -/
def composeComparison {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X)
    (hr : r = q ≫ p) (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) :
    (Scheme.Modules.pullback r).obj M ≅ P :=
  pullbackEqIso hr M ≪≫ ((Scheme.Modules.pullbackComp q p).app M).symm ≪≫
    (Scheme.Modules.pullback q).mapIso e ≪≫ f

lemma composeComparison_section {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) (hr : r = q ≫ p)
    (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (U : X.Opens) (s : Γ(M, U)) (V : Z.Opens)
    (h₁ : V ≤ r ⁻¹ᵁ U) (h₂ : V ≤ q ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    res P h₁ ((composeComparison p q r hr M N P e f).hom.app _
      (Scheme.Modules.pullbackLocalSection r s)) =
    res P h₂ (f.hom.app _ (Scheme.Modules.pullbackLocalSection q
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s)))) := by
  subst r
  change res P h₁ (f.hom.app _ (((Scheme.Modules.pullback q).map e.hom).app _
    (((Scheme.Modules.pullbackComp q p).app M).inv.app _
      (Scheme.Modules.pullbackLocalSection (q ≫ p) s)))) = _
  rw [pullbackComp_inv_section]
  exact congrArg (fun z => res P h₂ (f.hom.app _ z))
    (Scheme.Modules.pullbackLocalSection_app q e.hom (Scheme.Modules.pullbackLocalSection p s)).symm

lemma localPower_map_congr {T : Type u} [CommRing T] (Wt : WeierstrassCurve T)
    {X : Scheme.{u}} (f g : Curve T Wt ⟶ X) (h : f = g)
    (n : ℕ) (U : X.Opens) (a : Γ(X, U)) (V : (Base T).Opens)
    (hf : V ≤ origin T Wt ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : V ≤ origin T Wt ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    res (HodgePower T Wt n) hf (localPower T Wt n (f ⁻¹ᵁ U) (f.app U a)) =
    res (HodgePower T Wt n) hg (localPower T Wt n (g ⁻¹ᵁ U) (g.app U a)) := by
  subst g
  rfl

set_option maxHeartbeats 1600000 in
lemma comparison_refinement {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt} [IsDomain R] [IsDomain T] [W.IsElliptic]
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : IsBaseChange R W G T Wt Gt ρ b)
    (hm : b ≫ C.map = D.map)
    (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar)
    (n : ℕ) :
    powerComparison D n =
      composeComparison (baseMap S R C.scalar) (baseMap R T ρ) (baseMap S T D.scalar)
        hbase (power E n) (HodgePower R W n) (HodgePower T Wt n)
        (powerComparison C n) (hodgePowerIso R W G T Wt Gt ρ b hb n) := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  letI := E.smooth
  obtain ⟨U, a, hx, hframe⟩ := exists_exact_differential_frame E.projection
    (zero E (baseMap S T D.scalar x))
  let V := baseMap S T D.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U)
  have hV : V ≤ baseMap R T ρ ⁻¹ᵁ (baseMap S R C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U)) := by
    intro y hy
    change (baseMap R T ρ ≫ baseMap S R C.scalar) y ∈ zero E ⁻¹ᵁ U
    rw [← hbase]
    exact hy
  have hC : baseMap S R C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U) ≤
      origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ U) := by
    intro y hy
    change (origin R W ≫ C.map) y ∈ U
    rw [C.origin_eq]
    exact hy
  have hD : V ≤ origin T Wt ⁻¹ᵁ (D.map ⁻¹ᵁ U) := by
    intro y hy
    change (origin T Wt ≫ D.map) y ∈ U
    rw [D.origin_eq]
    exact hy
  have hB : V ≤ origin T Wt ⁻¹ᵁ (b ⁻¹ᵁ (C.map ⁻¹ᵁ U)) := by
    intro y hy
    change (origin T Wt ≫ b ≫ C.map) y ∈ U
    rw [hm]
    exact hD hy
  refine ⟨V, Scheme.Modules.pullbackLocalSection (baseMap S T D.scalar)
    (familyLocalPower E n U a), hx, ?_, ?_⟩
  · apply pullback_frame
    apply tensorPower_frame
    exact pullback_frame (zero E) E.projection.kaehler _ hframe
  · have hleft := powerComparison_localPower D n U a V le_rfl hD
    have hcomp := composeComparison_section (baseMap S R C.scalar) (baseMap R T ρ)
      (baseMap S T D.scalar) hbase (power E n) (HodgePower R W n) (HodgePower T Wt n)
      (powerComparison C n) (hodgePowerIso R W G T Wt Gt ρ b hb n)
      (zero E ⁻¹ᵁ U) (familyLocalPower E n U a) V le_rfl hV
    have hinner := powerComparison_localPower C n U a
      (baseMap S R C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U)) le_rfl hC
    rw [res_refl] at hinner
    rw [hinner, ← InitialSectionNaturality.pullback_res, ← hom_res, res_res] at hcomp
    rw [hodgePowerIso_spec R W G T Wt Gt ρ b hb n (C.map ⁻¹ᵁ U) (C.map.app U a) V
      (fun y hy => hC (hV hy)) hB] at hcomp
    have hvalue : res (HodgePower T Wt n) hB
        (localPower T Wt n (b ⁻¹ᵁ (C.map ⁻¹ᵁ U)) (b.app _ (C.map.app U a))) =
        res (HodgePower T Wt n) hD (localPower T Wt n (D.map ⁻¹ᵁ U) (D.map.app U a)) := by
      exact localPower_map_congr Wt (b ≫ C.map) D.map hm n U a V hB hD
    rw [hvalue] at hcomp
    simpa only [res_refl] using hleft.trans hcomp.symm

/-- An actual open cover detects equality of module sections. -/
lemma sections_ext_cover {X : Scheme.{u}} {ι : Type*}
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (ho : ∀ i, IsOpenImmersion (f i))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (M : X.Modules) (s t : Γ(M, ⊤))
    (h : ∀ i, Scheme.Modules.pullbackLocalSection (f i) s =
      Scheme.Modules.pullbackLocalSection (f i) t) : s = t := by
  letI : ∀ i, IsOpenImmersion (f i) := ho
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i => (f i).opensRange) ⊤ (fun _ => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr (hc x))
  intro i
  apply (Scheme.Modules.bijective_unit_app_of_le_opensRange
    (f i) M (f i).opensRange le_rfl).1
  change Scheme.Modules.pullbackLocalSection (f i) (res M le_top s) =
    Scheme.Modules.pullbackLocalSection (f i) (res M le_top t)
  rw [← InitialSectionNaturality.pullback_res, ← InitialSectionNaturality.pullback_res, h i]

/-- Uniqueness is detected on the constructed charts, including an empty atlas
over an empty base. No connectedness hypothesis is used. -/
lemma isD2_unique_of_atlas {S : Type u} [CommRing S] (E : EllipticFamily S)
    (A : Atlas S E) (s t : Γ(power E 24, ⊤))
    (hs : IsD2 E s) (ht : IsD2 E t) : s = t := by
  apply sections_ext_cover (fun i => Base (A.chart i).ring)
    (fun i => baseMap S (A.chart i).ring (A.chart i).comparison.scalar)
    (fun i => (A.chart i).openImmersion) A.covers (power E 24) s t
  intro i
  let C := A.chart i
  have hgeom := relative_curve_geometry C.ring C.equation
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  obtain ⟨g, hg⟩ := normalized_exists C.ring C.equation C.law C.originLaw
    5 (by norm_num) (by norm_num)
  have huniq := relative_initial_hodge_section C.ring C.equation C.law C.originLaw
    5 (by norm_num) (by norm_num) g hg
  have heq : pullSection C.comparison 24 s = pullSection C.comparison 24 t :=
    huniq.unique ⟨hs.2 C.ring C.equation C.law C.originLaw C.comparison g hg,
      pullSection_frame C.comparison 24 s hs.1⟩
      ⟨ht.2 C.ring C.equation C.law C.originLaw C.comparison g hg,
        pullSection_frame C.comparison 24 t ht.1⟩
  change Scheme.Modules.pullbackLocalSection (baseMap S C.ring C.comparison.scalar) s =
    Scheme.Modules.pullbackLocalSection (baseMap S C.ring C.comparison.scalar) t
  apply (ConcreteCategory.bijective_of_isIso ((powerComparison C.comparison 24).hom.app
    (baseMap S C.ring C.comparison.scalar ⁻¹ᵁ ⊤))).1
  simpa only [pullSection, res_refl] using heq

end GlobalFamilyDiscriminantR0180
open CategoryTheory AlgebraicGeometry ArithmeticThetaLegendreAtlasR0176

/-- The uniqueness half of global family discriminant descent. -/
theorem GlobalFamilyDiscriminantR0180.global_family_discriminant_unique
    (k : Type u) [Field k] [CharZero k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (E : EllipticFamily S) (s t : Γ(power E 24, ⊤))
    (hs : IsD2 E s) (ht : IsD2 E t) : s = t := by
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k S hS E
  exact GlobalFamilyDiscriminantR0180.isD2_unique_of_atlas E A s t hs ht

#print axioms GlobalFamilyDiscriminantR0180.global_family_discriminant_unique
#print axioms GlobalFamilyDiscriminantR0180.localD_naturality
end ArithmeticThetaOpenHodgeR0180

namespace ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
open ArithmeticThetaGeneralEllipticKatoR0168.BaseChange

lemma weierstrass_base_change {R T : Type u} [CommRing R] [CommRing T]
    (W : WeierstrassCurve R) (G : Law R W) (hG : IsOriginLaw R W G) (ρ : R →+* T) :
    ∃ (Gt : Law T (W.map ρ)), IsOriginLaw T (W.map ρ) Gt ∧
      ∃ b : Curve T (W.map ρ) ⟶ Curve R W, IsBaseChange R W G T (W.map ρ) Gt ρ b := by
  letI : Algebra R T := ρ.toAlgebra
  let Wt := W.map ρ
  let ft := structureMap T Wt
  obtain ⟨α, hα⟩ := WeierstrassProjModel.projModel_isPullback_baseChange_ring W.toProjective T
  obtain ⟨b, hb, he⟩ := pointed_cartesian ρ ft α hα G (WeierstrassProjModel.kwZeroSect T Wt)
  have he' : origin T Wt ≫ b = baseMap R T ρ ≫ origin R W := he.trans (hG.1 _)
  obtain ⟨H, hm, ho⟩ := WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ρ (structureMap R W) ft b hb G
  have hH : IsOriginLaw T Wt H := by
    constructor
    · intro Z t
      apply hb.hom_ext
      · simp only [ho, hG.1, Category.assoc, he']; rfl
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z) (WeierstrassProjModel.kwZeroSect T Wt).property).trans
            (Category.comp_id t)).symm)
    · intro Z t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  exact ⟨H, hH, b, hb, he', nsmul_comp ρ ft b hb G H hm ho⟩

lemma test_base_change {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (hG : IsOriginLaw R W G) (ρ : R →+* T) :
    ∃ (Gt : Law T (W.map ρ)) (_hGt : IsOriginLaw T (W.map ρ) Gt)
      (D : Test S E T (W.map ρ) Gt),
      D.scalar = ρ.comp C.scalar ∧
      ∃ b : Curve T (W.map ρ) ⟶ Curve R W,
        b ≫ C.map = D.map ∧ IsBaseChange R W G T (W.map ρ) Gt ρ b := by
  obtain ⟨Gt, hGt, b, hb, ho, hn⟩ := weierstrass_base_change W G hG ρ
  have hbase : baseMap S T (ρ.comp C.scalar) = baseMap R T ρ ≫ baseMap S R C.scalar :=
    Spec.map_comp (CommRingCat.ofHom C.scalar) (CommRingCat.ofHom ρ)
  refine ⟨Gt, hGt, ⟨ρ.comp C.scalar, b ≫ C.map, ?_, ?_, ?_⟩, rfl, b, rfl, hb, ho, hn⟩
  · rw [hbase]
    exact hb.paste_horiz C.cartesian
  · rw [← Category.assoc, ho, Category.assoc, C.origin_eq, ← Category.assoc, hbase]
    rfl
  · intro n
    rw [← Category.assoc, hn, Category.assoc, C.nsmul_eq, Category.assoc]

structure NormalAffineNeighborhood (R : Type u) [CommRing R]
    (U : (Base R).Opens) (x : Base R) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  scalar : R →+* ring
  openImmersion : IsOpenImmersion (baseMap R ring scalar)
  contains : x ∈ Set.range (baseMap R ring scalar)
  inside : Set.range (baseMap R ring scalar) ⊆ U
attribute [instance] NormalAffineNeighborhood.commRing NormalAffineNeighborhood.domain
  NormalAffineNeighborhood.noetherian NormalAffineNeighborhood.normal NormalAffineNeighborhood.rational

lemma normal_affine_neighborhood (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (U : (Base R).Opens) (x : Base R) (hx : x ∈ U) :
    Nonempty (NormalAffineNeighborhood R U x) := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : IsAffine V := hV
  letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian V.ι
  let T := Γ(V, ⊤)
  letI : IsNoetherianRing T := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  letI : IsIntegrallyClosed Γ(Base R, ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI : IsIntegrallyClosed T :=
    IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
      (fun z : V => (Smooth.isDomain_and_isIntegrallyClosed_stalk V.ι z).2)
      ⊤ (isAffineOpen_top V)
  let q : Base T ⟶ Base R := (Scheme.isoSpec V).inv ≫ V.ι
  let ρ : R →+* T := (Spec.preimage q).hom
  have hρ : baseMap R T ρ = q := Spec.map_preimage q
  letI : Algebra ℚ T := (ρ.comp (algebraMap ℚ R)).toAlgebra
  refine ⟨⟨T, ρ, ?_, ?_, ?_⟩⟩
  · rw [hρ]; dsimp [q]; infer_instance
  · rw [hρ]
    refine ⟨(Scheme.isoSpec V).hom ⟨x, hxV⟩, ?_⟩
    change ((Scheme.isoSpec V).hom ≫ (Scheme.isoSpec V).inv ≫ V.ι) _ = x
    simp
  · rw [hρ]
    rintro _ ⟨z, rfl⟩
    exact hVU ((Scheme.isoSpec V).inv z).property

lemma scalar_factor_open {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    (ρ : S →+* R) (τ : S →+* T) [IsOpenImmersion (baseMap S R ρ)]
    (h : Set.range (baseMap S T τ) ⊆ Set.range (baseMap S R ρ)) :
    ∃ σ : R →+* T, σ.comp ρ = τ := by
  let f := IsOpenImmersion.lift (baseMap S R ρ) (baseMap S T τ) h
  let σ : R →+* T := (Spec.preimage f).hom
  have hf : baseMap R T σ = f := Spec.map_preimage f
  refine ⟨σ, ?_⟩
  have he : CommRingCat.ofHom (σ.comp ρ) = CommRingCat.ofHom τ := by
    apply Spec.map_injective
    refine (Spec.map_comp (CommRingCat.ofHom ρ) (CommRingCat.ofHom σ)).trans ?_
    change baseMap R T σ ≫ baseMap S R ρ = baseMap S T τ
    rw [hf]
    exact IsOpenImmersion.lift_fac _ _ _
  exact congrArg CommRingCat.Hom.hom he

def testPull {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (U : (Base S).Opens) (V : (Base R).Opens)
    (h : V ≤ baseMap S R C.scalar ⁻¹ᵁ U) (s : Γ(power E n, U)) :
    Γ(HodgePower R W n, V) :=
  res _ h ((powerComparison C n).hom.app _
    (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))

lemma testPull_top {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤)) :
    testPull C n ⊤ ⊤ (by simp) s = pullSection C n s := rfl

lemma testPull_restrict {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (U U' : (Base S).Opens) (hU : U' ≤ U)
    (V : (Base R).Opens) (h : V ≤ baseMap S R C.scalar ⁻¹ᵁ U')
    (s : Γ(power E n, U)) :
    testPull C n U' V h (res (power E n) hU s) =
      testPull C n U V (h.trans (fun _ hx => hU hx)) s := by
  unfold testPull
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

lemma testPull_refinement {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt} [IsDomain R] [IsDomain T] [W.IsElliptic]
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : IsBaseChange R W G T Wt Gt ρ b) (hm : b ≫ C.map = D.map)
    (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar)
    (n : ℕ) (U : (Base S).Opens) (V : (Base R).Opens) (Z : (Base T).Opens)
    (hC : V ≤ baseMap S R C.scalar ⁻¹ᵁ U)
    (hT : Z ≤ baseMap R T ρ ⁻¹ᵁ V)
    (hD : Z ≤ baseMap S T D.scalar ⁻¹ᵁ U) (s : Γ(power E n, U)) :
    testPull D n U Z hD s =
      res (HodgePower T Wt n) hT ((hodgePowerIso R W G T Wt Gt ρ b hb n).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap R T ρ) (testPull C n U V hC s))) := by
  unfold testPull
  rw [comparison_refinement C D ρ b hb hm hbase n]
  rw [composeComparison_section _ _ _ _ _ _ _ _ _ U s Z hD
    (fun z hz => hC (hT hz))]
  rw [← InitialSectionNaturality.pullback_res, ← hom_res, res_res]

def chartSection {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E) :
    Γ(power E 24, chartOpen C) := (chart_frame_exists C).choose

lemma chartSection_frame {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E) :
    IsFrame (power E 24) (chartOpen C) (chartSection C) :=
  (chart_frame_exists C).choose_spec.1

lemma chartSection_pull {S : Type u} [CommRing S] {E : EllipticFamily S} (C : Chart S E)
    [IsIntegral (Curve C.ring C.equation)] [IsLocallyNoetherian (Curve C.ring C.equation)]
    [IsIntegral (GenericCurve C.ring C.equation)]
    [IsLocallyNoetherian (GenericCurve C.ring C.equation)] :
    chartPull C (chartSection C) = localD C.ring C.equation C.law C.originLaw := by
  apply (local_discriminant_exists C.ring C.equation C.law C.originLaw).unique
  · refine ⟨?_, (chart_frame_exists C).choose_spec.2⟩
    exact frame_restrict _ (chart_preimage C) _
      (frame_iso (powerComparison C.comparison 24) _
        (pullback_frame _ _ _ (chartSection_frame C)))
  · exact (local_discriminant_exists C.ring C.equation C.law C.originLaw).exists.choose_spec

/-- Every test factoring through a chart receives its constructed intrinsic
section. The refinement map is obtained from the Cartesian universal property. -/
lemma chartSection_test {S T : Type u} [CommRing S]
    [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T] [Algebra ℚ T]
    {E : EllipticFamily S} (C : Chart S E) (Wt : WeierstrassCurve T) [Wt.IsElliptic]
    [IsIntegral (Curve T Wt)] [IsLocallyNoetherian (Curve T Wt)]
    [IsIntegral (GenericCurve T Wt)] [IsLocallyNoetherian (GenericCurve T Wt)]
    (Gt : Law T Wt) (hGt : IsOriginLaw T Wt Gt) (D : Test S E T Wt Gt)
    (ρ : C.ring →+* T) (hρ : ρ.comp C.comparison.scalar = D.scalar)
    (hD : (⊤ : (Base T).Opens) ≤ baseMap S T D.scalar ⁻¹ᵁ chartOpen C) :
    testPull D 24 (chartOpen C) ⊤ hD (chartSection C) = localD T Wt Gt hGt := by
  have hgeom := relative_curve_geometry C.ring C.equation
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  obtain ⟨b, hm, hb⟩ := test_refinement C.comparison D ρ hρ
  have hbase : baseMap S T D.scalar =
      baseMap C.ring T ρ ≫ baseMap S C.ring C.comparison.scalar := by
    rw [← hρ]
    exact Spec.map_comp (CommRingCat.ofHom C.comparison.scalar) (CommRingCat.ofHom ρ)
  rw [testPull_refinement C.comparison D ρ b hb hm hbase 24 (chartOpen C) ⊤ ⊤
    (chart_preimage C) (by simp) hD]
  change res (HodgePower T Wt 24) le_rfl ((hodgePowerIso _ _ _ _ _ _ ρ b hb 24).hom.app _
    (Scheme.Modules.pullbackLocalSection (baseMap C.ring T ρ) (chartPull C (chartSection C)))) = _
  rw [chartSection_pull, res_refl]
  exact (localD_naturality C.ring C.equation C.law C.originLaw T Wt Gt hGt ρ b hb).trans
    (res_refl _ _)

lemma sections_eq_local {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (s t : Γ(M, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (_ : x ∈ V) (hV : V ≤ U),
      res M hV s = res M hV t) : s = t := by
  classical
  choose V hx hV he using (fun x : U => h x.val x.property)
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ V U
    (fun x => homOfLE (hV x))
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  exact he

lemma section_res_eq_of_testPull_eq {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) [IsOpenImmersion (baseMap S R C.scalar)]
    (n : ℕ) (U : (Base S).Opens) (hU : (baseMap S R C.scalar).opensRange ≤ U)
    (h : (⊤ : (Base R).Opens) ≤ baseMap S R C.scalar ⁻¹ᵁ U)
    (s t : Γ(power E n, U)) (he : testPull C n U ⊤ h s = testPull C n U ⊤ h t) :
    res (power E n) hU s = res (power E n) hU t := by
  have hp : Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s =
      Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) t := by
    apply (ConcreteCategory.bijective_of_isIso ((powerComparison C n).hom.app _)).1
    exact (res_bijective _ h le_top).1 he
  apply (Scheme.Modules.bijective_unit_app_of_le_opensRange (baseMap S R C.scalar)
    (power E n) (baseMap S R C.scalar).opensRange le_rfl).1
  change Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) (res (power E n) hU s) =
    Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) (res (power E n) hU t)
  rw [← InitialSectionNaturality.pullback_res, ← InitialSectionNaturality.pullback_res, hp]

/-- Equality of the constructed frames on every overlap of chart images. -/
lemma chartSection_overlap {S : Type u} [CommRing S] {E : EllipticFamily S}
    (C D : Chart S E) :
    res (power E 24) (inf_le_left : chartOpen C ⊓ chartOpen D ≤ chartOpen C) (chartSection C) =
      res (power E 24) (inf_le_right : chartOpen C ⊓ chartOpen D ≤ chartOpen D) (chartSection D) := by
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
  have hcs := chartSection_test C Wt Gt hGt Z N.scalar hZ.symm hC
  have hds := chartSection_test D Wt Gt hGt Z τ hτ hD
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
  · apply section_res_eq_of_testPull_eq Z 24 _ hU hUZ
    rw [testPull_restrict, testPull_restrict]
    exact hcs.trans hds.symm

lemma frame_glue_cover {X : Scheme.{u}} (F : X.Modules) {ι : Type*}
    (V : ι → X.Opens) (hcover : (⨆ i, V i) = ⊤) (s : Γ(F, ⊤))
    (h : ∀ i, IsFrame F (V i) (res F le_top s)) : IsFrame F ⊤ s := by
  have hs : ∀ i, Scheme.Modules.IsFrameOn s (V i) := by
    intro i T hT hTi
    have hh := h i T hTi
    change Function.Bijective (fun a : Γ(X, T) => a • res F hT s)
    simpa only [InitialHodgeSection.res_res] using hh
  have ht := Scheme.Modules.IsFrameOn.of_iSup V hs
  rw [hcover] at ht
  exact fun T hT => ht hT hT

lemma glue_chart_sections {S : Type u} [CommRing S] (E : EllipticFamily S) (A : Atlas S E) :
    ∃ d : Γ(power E 24, ⊤), IsFrame (power E 24) ⊤ d ∧
      ∀ i, res (power E 24) le_top d = chartSection (A.chart i) := by
  let U := fun i => chartOpen (A.chart i)
  have hc : (⨆ i, U i) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (A.covers x)
  obtain ⟨d, hd, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(power E 24).presheaf, (power E 24).isSheaf⟩ U ⊤ (fun _ => homOfLE le_top)
    hc.ge (fun i => chartSection (A.chart i)) (fun i j => chartSection_overlap _ _)
  refine ⟨d, ?_, hd⟩
  apply frame_glue_cover _ U hc d
  intro i
  change IsFrame (power E 24) (U i) ((power E 24).presheaf.map (homOfLE le_top).op d)
  rw [hd i]
  exact chartSection_frame _

lemma restriction_eq_of_pullback_eq {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (hU : f.opensRange ≤ U) (s t : Γ(M, U))
    (h : Scheme.Modules.pullbackLocalSection f s = Scheme.Modules.pullbackLocalSection f t) :
    res M hU s = res M hU t := by
  apply (Scheme.Modules.bijective_unit_app_of_le_opensRange f M f.opensRange le_rfl).1
  change Scheme.Modules.pullbackLocalSection f (res M hU s) =
    Scheme.Modules.pullbackLocalSection f (res M hU t)
  rw [← InitialSectionNaturality.pullback_res, ← InitialSectionNaturality.pullback_res, h]

set_option maxRecDepth 4096 in
/-- The glued section has the intrinsic value on every normal-affine test;
the local neighborhoods are taken on that test, so no dominance is required. -/
lemma glued_section_test {S : Type u} [CommRing S] (E : EllipticFamily S) (A : Atlas S E)
    (d : Γ(power E 24, ⊤))
    (hd : ∀ i, res (power E 24) le_top d = chartSection (A.chart i))
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G) :
    pullSection C 24 d = localD R W G hG := by
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
  have hchart := chartSection_test D (W.map N.scalar) Gt hGt Z τ hτ hDZ
  have hglobal : testPull Z 24 ⊤ ⊤ (by simp) d = localD N.ring (W.map N.scalar) Gt hGt := by
    rw [← testPull_restrict Z 24 ⊤ (chartOpen D) le_top ⊤ hDZ d, hd i]
    exact hchart
  have htransport := testPull_refinement C Z N.scalar b hb hbmap hZbase
    24 ⊤ ⊤ ⊤ (by simp) (by simp) (by simp) d
  have hnat := localD_naturality R W G hG N.ring (W.map N.scalar) Gt hGt N.scalar b hb
  simp only [InitialBaseChange, res_refl] at hnat
  have hp : Scheme.Modules.pullbackLocalSection (baseMap R N.ring N.scalar) (pullSection C 24 d) =
      Scheme.Modules.pullbackLocalSection (baseMap R N.ring N.scalar) (localD R W G hG) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((hodgePowerIso R W G N.ring (W.map N.scalar) Gt N.scalar b hb 24).hom.app
        (baseMap R N.ring N.scalar ⁻¹ᵁ ⊤))).1
    have hfirst := htransport.symm.trans hglobal
    simp only [testPull_top, res_refl] at hfirst
    exact hfirst.trans hnat.symm
  refine ⟨(baseMap R N.ring N.scalar).opensRange, N.contains, le_top, ?_⟩
  exact restriction_eq_of_pullback_eq (baseMap R N.ring N.scalar) (HodgePower R W 24)
    ⊤ le_top _ _ hp

lemma global_discriminant_exists_of_atlas {S : Type u} [CommRing S]
    (E : EllipticFamily S) (A : Atlas S E) : ∃ d : Γ(power E 24, ⊤), IsD2 E d := by
  obtain ⟨d, hdframe, hd⟩ := glue_chart_sections E A
  refine ⟨d, hdframe, ?_⟩
  intro R _ _ _ _ _ W _ _ _ _ _ G hG C g hg
  rw [glued_section_test E A d hd R W G hG C]
  exact localD_represents R W G hG g hg

end ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

namespace ArithmeticThetaOpenHodgeR0180
open CategoryTheory AlgebraicGeometry ArithmeticThetaLegendreAtlasR0176

/-- The unique global intrinsic discriminant frame, characterized on every
pointed Cartesian normal-affine Weierstrass test. -/
theorem global_family_discriminant
    (k : Type u) [Field k] [CharZero k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (E : EllipticFamily S) : ∃! d : Γ(power E 24, ⊤), IsD2 E d := by
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k S hS E
  obtain ⟨d, hd⟩ := GlobalFamilyDiscriminantR0180.global_discriminant_exists_of_atlas E A
  exact ⟨d, hd, fun d' hd' => GlobalFamilyDiscriminantR0180.isD2_unique_of_atlas E A d' d hd' hd⟩

#print axioms global_family_discriminant
end ArithmeticThetaOpenHodgeR0180
