import SchemeIdentityChartCoverR0253
import ArbitraryUnitInitialCoefficientR0253

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaKatoInitialR0253
namespace SchemeFiveKatoInitialCharacterization
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeKatoUnitR0250
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaRelativeDiscriminantR0171 (res)
open ArithmeticThetaArbitraryKatoUnitR0249 (restrict)
open ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- The exact Cartier divisor gives the entire-chart coefficient of five times
the same unit; regularity justifies the cancellation even over nonreduced bases. -/
lemma chart_equation (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S)
    (v : UnitSection E 5) (hv : IsKatoUnit E k σ 5 v)
    (U : E.curve.affineOpens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U.1))
    (hx : IdentityChart E 5 U x) :
    ∃ ε : (Γ(E.curve, U.1))ˣ,
      5 * restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
        restrict U.1 (U.1 ⊓ complement E 5) inf_le_left
          ((ε : _) * (equation E U.1 x)^24) := by
  let a := equation E U.1 x
  have hI : (torsionIdeal E 5).ideal U = Ideal.span {a} := hx.2.2.trans hx.2.1
  obtain ⟨ε, hε⟩ := (scheme_kato_cartier_divisor k S σ E 5
    (by norm_num) (by norm_num) v hv).2.2 U a a hx.1 hx.1 hx.2.1 hI
  have hreg := ArbitraryUnitInitialCoefficient.regular_on_complement
    (torsionIdeal E 5) U a hx.1 hI
  have he : restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement E 5) inf_le_left ((ε : _) * a^24) := by
    apply hreg.right
    rw [show 5^2 = 24+1 from rfl, pow_succ, ← mul_assoc, restrict_mul] at hε
    exact hε
  let φ : ℚ →+* Γ(E.curve, U.1) :=
    (E.curve.presheaf.map (homOfLE le_top).op).hom.comp
      ((E.p ≫ σ).appTop.hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp (algebraMap ℚ k)))
  let five : (Γ(E.curve, U.1))ˣ :=
    Units.map φ.toMonoidHom (Units.mk0 (5 : ℚ) (by norm_num))
  have hfive : (five : Γ(E.curve, U.1)) = 5 := by
    change φ (5 : ℚ) = 5
    exact map_ofNat φ 5
  refine ⟨five * ε, ?_⟩
  rw [he, Units.val_mul, hfive, mul_assoc]
  simp only [restrict, map_mul, map_ofNat, a]

/-- Entire-chart initial coefficients are unique by schematic density of the
regular divisor complement and cancellation of the regular twenty-fourth power. -/
lemma coefficient_unique {S : Scheme.{u}} (E : Family S)
    (v : UnitSection E 5) (U : E.curve.affineOpens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U.1))
    (hx : IdentityChart E 5 U x) (ε η : Γ(E.curve, U.1))
    (hε : 5 * restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement E 5) inf_le_left (ε * (equation E U.1 x)^24))
    (hη : 5 * restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement E 5) inf_le_left (η * (equation E U.1 x)^24)) :
    ε = η := by
  apply (hx.1.pow 24).right
  exact complement_restrict_injective (torsionIdeal E 5) U (equation E U.1 x)
    hx.1 (hx.2.2.trans hx.2.1) (hε.symm.trans hη)

/-- The local initial equations determine an arbitrary global conormal tensor.
No canonical-discriminant hypothesis is used for either section. -/
lemma initial_unique (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S)
    (v : UnitSection E 5) (d e : Sections E)
    (hd : SchemeInitial E v d) (he : SchemeInitial E v e) : d = e := by
  apply sections_eq_local
  intro s _
  obtain ⟨U, x, hs, _, hx⟩ := scheme_identity_chart_cover k S σ E 5 (by norm_num) s ⊤
    (by trivial)
  obtain ⟨ε, hε, hdε⟩ := hd U x hx
  obtain ⟨η, hη, heη⟩ := he U x hx
  have h := coefficient_unique E v U x hx (ε : _) (η : _) hε hη
  refine ⟨E.zero ⁻¹ᵁ U.1, hs, le_top, ?_⟩
  rw [hdε, heη, h]

open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171 hiding Base
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence

lemma conormalPower_restrict {S : Scheme.{u}} (E : Family S)
    {U V : E.curve.Opens} (h : V ≤ U)
    (x : Γ(E.zero.ker.module, U)) :
    res (Power E) (show E.zero ⁻¹ᵁ V ≤ E.zero ⁻¹ᵁ U from fun _ hx => h hx)
      (conormalPower E U x) =
    conormalPower E V (res E.zero.ker.module h x) := by
  unfold conormalPower res
  rw [tensorPowerSection_restrict]
  congr 1
  exact InitialSectionNaturality.pullback_res E.zero E.zero.ker.module h x

def idealIso {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :=
  (cartesian_identity_ideal S T E F b C.map C.cartesian C.pointed).exists.choose

lemma idealIso_compatible {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :
    IdealCompatible E F C.map (idealIso C) :=
  (cartesian_identity_ideal S T E F b C.map C.cartesian C.pointed).exists.choose_spec

/-- The canonical comparison transports the actual pulled-back ideal section. -/
lemma comparison_conormalPower {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b)
    (U : E.curve.Opens) (x : Γ(E.zero.ker.module, U)) (V : T.Opens)
    (h₁ : V ≤ b ⁻¹ᵁ (E.zero ⁻¹ᵁ U))
    (h₂ : V ≤ F.zero ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    localPull C (E.zero ⁻¹ᵁ U) V h₁ (conormalPower E U x) =
      res (Power F) h₂ (conormalPower F (C.map ⁻¹ᵁ U)
        ((idealIso C).hom.app _ (Scheme.Modules.pullbackLocalSection C.map x))) := by
  unfold localPull powerIso conormalPower
  rw [tensorComparison_section]
  unfold res
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection T (Cotangent F) 24 V)
    (AffineConormalHodgeNaturality.cotangent_section E F b C.map C.pointed (idealIso C) U x V h₁ h₂)

open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

/-- Under the actual conormal derivative the ideal-section class becomes the
relative differential of its image in the structure sheaf. -/
lemma weierstrass_conormalPower (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (U : (Curve R W).Opens)
    (x : Γ((weierstrassFamily R W G hG).zero.ker.module, U))
    (V : (ArithmeticThetaLocalWeierstrassR0203.Base R).Opens)
    (h₁ : V ≤ (weierstrassFamily R W G hG).zero ⁻¹ᵁ U)
    (h₂ : V ≤ origin R W ⁻¹ᵁ U) :
    res (HodgePower R W 24) h₁
      ((powerCongr _ (weierstrassHodgeIso R W G hG) 24).hom.app _
        (conormalPower (weierstrassFamily R W G hG) U x)) =
    res (HodgePower R W 24) h₂
      (localPower R W 24 U (equation (weierstrassFamily R W G hG) U x)) := by
  unfold conormalPower
  rw [powerCongr_section]
  change _ = res _ h₂ (tensorPowerSection _ _ 24 _ _)
  unfold res
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  apply congrArg (tensorPowerSection _ _ 24 V)
  change res _ h₁ ((pullbackEqIso (weierstrass_zero R W G hG) _).hom.app _
    ((conormalMap (structureMap R W) (weierstrassFamily R W G hG).zero).app _
      (Scheme.Modules.pullbackLocalSection _ x))) = _
  rw [conormalMap_pullback]
  exact pullbackEqIso_section (weierstrass_zero R W G hG) _ U _ V h₁ h₂

lemma test_conormalPower {S : Scheme.{u}} (E : Family S)
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (b : Base R ⟶ S)
    (C : Comparison E (weierstrassFamily R W G hG) b)
    (U : E.curve.Opens) (V : (Curve R W).Opens) (h : V ≤ C.map ⁻¹ᵁ U)
    (hp : origin R W ⁻¹ᵁ V ≤ b ⁻¹ᵁ (E.zero ⁻¹ᵁ U))
    (x : Γ(E.zero.ker.module, U)) :
    (powerCongr _ (weierstrassHodgeIso R W G hG) 24).hom.app _
      (localPull C (E.zero ⁻¹ᵁ U) (origin R W ⁻¹ᵁ V) hp (conormalPower E U x)) =
      localPower R W 24 V (C.map.appLE U V h (equation E U x)) := by
  have hz : origin R W ⁻¹ᵁ V ≤
      (weierstrassFamily R W G hG).zero ⁻¹ᵁ (C.map ⁻¹ᵁ U) := by
    rw [weierstrass_zero]
    exact fun _ hx => h hx
  rw [comparison_conormalPower C U x _ hp hz, ← hom_res,
    weierstrass_conormalPower R W G hG _ _ _ hz (fun _ hx => h hx)]
  have he := AffineConormalHodgeNaturality.ideal_section E
    (weierstrassFamily R W G hG) C.map (idealIso C) (idealIso_compatible C) U x
  change res _ _ (localPower R W 24 _
    ((weierstrassFamily R W G hG).zero.ker.moduleι.app _ _)) = _
  rw [he, InitialHodgeSection.power_res R W 24 h]
  rfl

lemma test_value {S : Scheme.{u}} (E : Family S)
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (b : Base R ⟶ S)
    (C : Comparison E (weierstrassFamily R W G hG) b)
    (U : E.curve.Opens) (V : (Curve R W).Opens) (h : V ≤ C.map ⁻¹ᵁ U)
    (hp : origin R W ⁻¹ᵁ V ≤ b ⁻¹ᵁ (E.zero ⁻¹ᵁ U))
    (x : Γ(E.zero.ker.module, U)) (r : Γ(E.curve, U)) :
    (powerCongr _ (weierstrassHodgeIso R W G hG) 24).hom.app _
      (localPull C (E.zero ⁻¹ᵁ U) (origin R W ⁻¹ᵁ V) hp
        (E.zero.app U r • conormalPower E U x)) =
    (origin R W).app V (C.map.appLE U V h r) •
      localPower R W 24 V (C.map.appLE U V h (equation E U x)) := by
  have hz : origin R W ≫ C.map = b ≫ E.zero := by
    rw [← weierstrass_zero R W G hG]
    exact C.pointed
  unfold localPull
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul, Scheme.Modules.Hom.app_smul]
  change b.appLE _ _ hp (E.zero.app U r) •
    ((powerCongr _ (weierstrassHodgeIso R W G hG) 24).hom.app _
      (localPull C _ _ hp (conormalPower E U x))) = _
  rw [test_conormalPower E R W G hG b C U V h hp x,
    InitialSectionNaturality.scalar_square b E.zero (origin R W) C.map hz U V h hp r]
  rfl

lemma equation_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U D : X.Opens) (V C : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (hC : C ≤ f ⁻¹ᵁ D)
    (v : Γ(X, D)) (w : Γ(Y, C)) (hw : w = f.appLE D C hC v)
    (a r : Γ(X, U))
    (he : 5 * restrict D (U ⊓ D) inf_le_right v =
      restrict U (U ⊓ D) inf_le_left (r * a^24)) :
    5 * restrict C (V ⊓ C) inf_le_right w =
      restrict V (V ⊓ C) inf_le_left
        (f.appLE U V h r * (f.appLE U V h a)^24) := by
  have ht : V ⊓ C ≤ f ⁻¹ᵁ (U ⊓ D) := fun _ hx => ⟨h hx.1, hC hx.2⟩
  have H := congrArg (f.appLE (U ⊓ D) (V ⊓ C) ht) he
  rw [hw]
  simpa only [restrict, map_mul, map_pow, map_ofNat, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] using H

lemma test_global_restrict {S : Scheme.{u}} (E : Family S)
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (b : Base R ⟶ S)
    (C : Comparison E (weierstrassFamily R W G hG) b)
    (U : S.Opens) (V : (Base R).Opens) (h : V ≤ b ⁻¹ᵁ U) (d : Sections E) :
    (powerCongr _ (weierstrassHodgeIso R W G hG) 24).hom.app V
      (localPull C U V h (res (Power E) le_top d)) =
    res (HodgePower R W 24) le_top (weierstrassValue R W G hG (pull C d)) := by
  rw [localPull_restrict]
  unfold localPull weierstrassValue pull
  rw [← hom_res, ← hom_res, InitialHodgeSection.res_res]

lemma restrict_eq_of_pullback_eq {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U V : X.Opens) (h : V ≤ U) (hV : V ≤ f.opensRange)
    (s t : Γ(M, U))
    (he : Scheme.Modules.pullbackLocalSection f s = Scheme.Modules.pullbackLocalSection f t) :
    res M h s = res M h t := by
  apply (Scheme.Modules.bijective_unit_app_of_le_opensRange f M V hV).1
  change Scheme.Modules.pullbackLocalSection f (res M h s) =
    Scheme.Modules.pullbackLocalSection f (res M h t)
  rw [← InitialSectionNaturality.pullback_res, ← InitialSectionNaturality.pullback_res, he]

attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic LocalPresentation.openImmersion

lemma test_chart {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S) (P : LocalPresentation k S σ E)
    (U : E.curve.affineOpens) (x : Γ(E.zero.ker.module, U.1))
    (hx : IdentityChart E 5 U x)
    (V : (Curve P.ring P.equation).affineOpens) (h : V.1 ≤ P.comparison ⁻¹ᵁ U.1) :
    AffineIdentityChart P.ring P.equation P.law 5 V
      (P.comparison.appLE U.1 V.1 h (equation E U.1 x)) := by
  letI : IsOpenImmersion P.comparison := SchemeMultiplicationDegree.chart_open σ E P
  have hcomp := scheme_torsion_cartesian k S σ E (Base P.ring)
    (Spec.map (CommRingCat.ofHom (algebraMap k P.ring))) (chartFamily P)
    P.base P.base_eq (chartComparison P) 5
  have hI : (identityIdeal E).comap P.comparison =
      ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal P.ring P.equation := by
    simpa only [chartComparison, chartFamily, identityIdeal, weierstrass_zero,
      ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal] using hcomp.2.1
  have hJ : (torsionIdeal E 5).comap P.comparison =
      ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal P.ring P.equation P.law 5 := by
    simpa only [chartComparison, chartFamily, torsionIdeal, identityIdeal, weierstrass_zero,
      SchemeKatoUnitExistence.weierstrass_multiplication,
      ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal,
      ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal] using hcomp.2.2.1
  refine ⟨regular_appLE P.comparison U V h _ hx.1, ?_, ?_⟩
  · rw [← hI, Scheme.IdealSheafData.ideal_comap_of_le _ _ U V h,
      hx.2.1, Ideal.map_span, Set.image_singleton]
  · rw [← hI, ← hJ, Scheme.IdealSheafData.ideal_comap_of_le _ _ U V h,
      Scheme.IdealSheafData.ideal_comap_of_le _ _ U V h, hx.2.2]

lemma test_coefficient_tensor {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S) (P : LocalPresentation k S σ E)
    (v : UnitSection E 5) (hv : IsKatoUnit E k σ 5 v)
    (d : Sections E) (hd : IsD2 k σ E d)
    (U : E.curve.affineOpens) (x : Γ(E.zero.ker.module, U.1))
    (hx : IdentityChart E 5 U x) (ε : (Γ(E.curve, U.1))ˣ)
    (hε : 5 * restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement E 5) inf_le_left ((ε : _) * (equation E U.1 x)^24))
    (V : (Curve P.ring P.equation).affineOpens) (h : V.1 ≤ P.comparison ⁻¹ᵁ U.1)
    (hp : origin P.ring P.equation ⁻¹ᵁ V.1 ≤ P.base ⁻¹ᵁ (E.zero ⁻¹ᵁ U.1)) :
    localPull (chartComparison P) (E.zero ⁻¹ᵁ U.1) (origin P.ring P.equation ⁻¹ᵁ V.1)
      hp (res (Power E) le_top d) =
    localPull (chartComparison P) (E.zero ⁻¹ᵁ U.1) (origin P.ring P.equation ⁻¹ᵁ V.1)
      hp (E.zero.app U.1 (ε : _) • conormalPower E U.1 x) := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨w, hw, eD, hvw⟩ := hv P.ring P.equation P.law P.originLaw
    P.base P.base_eq (chartComparison P)
  have hdP := hd P.ring P.equation P.law P.originLaw P.base P.base_eq (chartComparison P)
  let εV : (Γ(Curve P.ring P.equation, V.1))ˣ :=
    Units.map (P.comparison.appLE U.1 V.1 h).hom.toMonoidHom ε
  have hεV := equation_pullback P.comparison U.1 (complement E 5) V.1
    (ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law 5)
    h eD (v : _) (w : _) hvw (equation E U.1 x) (ε : _) hε
  have ht := ArbitraryUnitInitialCoefficient.coefficient_tensor P.ring P.equation P.law
    w hw (weierstrassValue P.ring P.equation P.law P.originLaw (pull (chartComparison P) d))
    hdP V _ (test_chart σ E P U x hx V h) εV hεV
  apply (ConcreteCategory.bijective_of_isIso
    ((powerCongr _ (weierstrassHodgeIso P.ring P.equation P.law P.originLaw) 24).hom.app
      (origin P.ring P.equation ⁻¹ᵁ V.1))).1
  rw [test_global_restrict, test_value]
  exact ht

/-- The arbitrary-ring formula detects the coefficient on every scheme chart.
All detection takes place on open subschemes and actual sheaf sections. -/
lemma coefficient_tensor (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S)
    (v : UnitSection E 5) (hv : IsKatoUnit E k σ 5 v)
    (d : Sections E) (hd : IsD2 k σ E d)
    (U : E.curve.affineOpens) (x : Γ(E.zero.ker.module, U.1))
    (hx : IdentityChart E 5 U x) (ε : (Γ(E.curve, U.1))ˣ)
    (hε : 5 * restrict (complement E 5) (U.1 ⊓ complement E 5) inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement E 5) inf_le_left ((ε : _) * (equation E U.1 x)^24)) :
    res (Power E) le_top d = E.zero.app U.1 (ε : _) • conormalPower E U.1 x := by
  apply sections_eq_local
  intro s hs
  obtain ⟨P, hsP⟩ := scheme_local_weierstrass k S σ E s
  have hpb : Scheme.Modules.pullbackLocalSection P.base (res (Power E) le_top d) =
      Scheme.Modules.pullbackLocalSection P.base
        (E.zero.app U.1 (ε : _) • conormalPower E U.1 x) := by
    apply (ConcreteCategory.bijective_of_isIso ((powerIso (chartComparison P)).hom.app _)).1
    apply sections_eq_local
    intro z hz
    have hzU : origin P.ring P.equation z ∈ P.comparison ⁻¹ᵁ U.1 := by
      change (origin P.ring P.equation ≫ P.comparison) z ∈ U.1
      rw [P.zero_eq]
      exact hz
    obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset hzU
    have hp : origin P.ring P.equation ⁻¹ᵁ V ≤ P.base ⁻¹ᵁ (E.zero ⁻¹ᵁ U.1) := by
      intro y hy
      change (P.base ≫ E.zero) y ∈ U.1
      rw [← P.zero_eq]
      exact hVU hy
    refine ⟨origin P.ring P.equation ⁻¹ᵁ V, hzV, hp, ?_⟩
    exact test_coefficient_tensor σ E P v hv d hd U x hx ε hε ⟨V, hV⟩ hVU hp
  refine ⟨(E.zero ⁻¹ᵁ U.1) ⊓ P.base.opensRange, ⟨hs, hsP⟩, inf_le_left, ?_⟩
  exact restrict_eq_of_pullback_eq P.base (Power E) (E.zero ⁻¹ᵁ U.1) _
    inf_le_left inf_le_right _ _ hpb

lemma canonical_initial (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S) (v : UnitSection E 5)
    (hv : IsKatoUnit E k σ 5 v) (d : Sections E) (hd : IsD2 k σ E d) :
    SchemeInitial E v d := by
  intro U x hx
  obtain ⟨ε, hε⟩ := chart_equation k σ E v hv U x hx
  exact ⟨ε, hε, coefficient_tensor k σ E v hv d hd U x hx ε hε⟩

#print axioms chart_equation
#print axioms coefficient_unique
#print axioms initial_unique
#print axioms test_value
#print axioms canonical_initial
end SchemeFiveKatoInitialCharacterization

open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203

/-- The same canonical five-Kato unit characterizes the actual discriminant
tensor on every characteristic-zero elliptic scheme family. -/
theorem scheme_five_kato_initial_characterization :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E 5,
      ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ 5 v →
      ∀ d : ArithmeticThetaSchemeDiscriminantR0244.Sections E,
      ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d ↔
        ArithmeticThetaKatoInitialR0253.SchemeInitial E v d := by
  intro k _ _ S σ E v hv d
  constructor
  · exact SchemeFiveKatoInitialCharacterization.canonical_initial k σ E v hv d
  · intro hd
    obtain ⟨e, he⟩ := ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_existence k S σ E
    have hde := SchemeFiveKatoInitialCharacterization.initial_unique k σ E v d e hd
      (SchemeFiveKatoInitialCharacterization.canonical_initial k σ E v hv e he)
    exact hde.symm ▸ he

#print axioms scheme_five_kato_initial_characterization
end ArithmeticThetaKatoInitialR0253
