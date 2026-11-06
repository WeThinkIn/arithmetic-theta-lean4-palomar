module

public import KatoInitialDefinitionsR0253
public import ArbitraryKatoCartierDivisorR0249

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaKatoInitialR0253
namespace ArbitraryUnitInitialCoefficient
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaArbitraryKatoUnitR0249
open ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor

/-- Restricting a regular equation to its divisor complement preserves regularity.
The argument uses the actual basic open and also applies to the zero ring. -/
lemma regular_on_complement {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : IsRegular a)
    (hI : I.ideal U = Ideal.span {a}) :
    IsRegular (restrict U.1 (U.1 ⊓ I.support.compl) inf_le_left a) := by
  have hD : IsAffineOpen (U.1 ⊓ I.support.compl) := by
    rw [complement_inter_basicOpen I U a hI]
    exact U.2.basicOpen a
  exact regular_restrict U ⟨_, hD⟩ inf_le_left a ha

/-- The complete canonical unit has an order-24 equation on the whole given
identity chart. This is the first equality in the frozen target. -/
lemma chart_equation (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (v : UnitSection R W G 5)
    (hv : IsKatoUnit R W G 5 v)
    (U : (Curve R W).affineOpens) (a : Γ(Curve R W, U.1))
    (ha : AffineIdentityChart R W G 5 U a) :
    ∃ ε : (Γ(Curve R W, U.1))ˣ,
      5 * restrict (complement R W G 5) (U.1 ⊓ complement R W G 5)
          inf_le_right (v : _) =
        restrict U.1 (U.1 ⊓ complement R W G 5) inf_le_left ((ε : _) * a^24) := by
  have hI : (torsionIdeal R W G 5).ideal U = Ideal.span {a} :=
    ha.2.2.trans ha.2.1
  obtain ⟨ε, hε⟩ := (arbitrary_kato_cartier_divisor R W G hG 5
    (by norm_num) (by norm_num) v hv).2.2 U a a ha.1 ha.1 ha.2.1 hI
  have hreg := regular_on_complement (torsionIdeal R W G 5) U a ha.1 hI
  have he : restrict (complement R W G 5) (U.1 ⊓ complement R W G 5)
      inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement R W G 5) inf_le_left ((ε : _) * a^24) := by
    apply hreg.right
    rw [show 5^2 = 24+1 from rfl, pow_succ, ← mul_assoc, restrict_mul] at hε
    exact hε
  let φ : ℚ →+* Γ(Curve R W, U.1) :=
    ((Curve R W).presheaf.map (homOfLE le_top).op).hom.comp
      ((structureMap R W).appTop.hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℚ R)))
  let five : (Γ(Curve R W, U.1))ˣ :=
    Units.map φ.toMonoidHom (Units.mk0 (5 : ℚ) (by norm_num))
  have hfive : (five : Γ(Curve R W, U.1)) = 5 := by
    change φ (5 : ℚ) = 5
    exact map_ofNat φ 5
  refine ⟨five * ε, ?_⟩
  rw [he, Units.val_mul, hfive, mul_assoc]
  simp only [restrict, map_mul, map_ofNat]

/-- A generator of the actual identity ideal vanishes under the origin map,
without an integrality hypothesis. -/
lemma generator_vanishes (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).affineOpens) (a : Γ(Curve R W, U.1))
    (ha : (identityIdeal R W).ideal U = Ideal.span {a}) :
    (origin R W).app U.1 a = 0 := by
  change ((origin R W).app U.1).hom a = 0
  apply RingHom.mem_ker.mp
  rw [← Scheme.Hom.ker_apply]
  change a ∈ (identityIdeal R W).ideal U
  rw [ha]
  exact Ideal.subset_span (Set.mem_singleton a)

/-- Equality of the entire section products gives equality of their initial
Hodge tensors for any two equations of the same identity ideal. -/
lemma value_eq (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).affineOpens) (a b e f : Γ(Curve R W, U.1))
    (n : ℕ) (ha : IsRegular a)
    (hIa : (identityIdeal R W).ideal U = Ideal.span {a})
    (hIb : (identityIdeal R W).ideal U = Ideal.span {b})
    (h : e * a^n = f * b^n) :
    (origin R W).app U.1 e • localPower R W n U.1 a =
      (origin R W).app U.1 f • localPower R W n U.1 b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp
    (show b ∈ Ideal.span {a} by rw [← hIa, hIb]; exact Ideal.subset_span rfl)
  have hb : b = r*a := by rw [hr, mul_comm]
  have he : e = f*r^n := (ha.pow n).right (by
    rw [hb, mul_pow, ← mul_assoc] at h
    exact h)
  rw [hb, InitialHodgeSection.power_mul R W n U.1 r a
    (generator_vanishes R W U a hIa), smul_smul, he, map_mul, map_pow]

open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The canonical comparison preserves the tensor power of the actual local
relative differential over an arbitrary target ring. -/
lemma comparison_localPower {A R : Type u} [CommRing A] [CommRing R]
    {Wa : WeierstrassCurve A} [Wa.IsElliptic] {W : WeierstrassCurve R}
    {ι : A →+* R} (C : Comparison A R Wa W ι)
    (U : (Curve A Wa).Opens) (a : Γ(Curve A Wa, U))
    (V : (Base R).Opens)
    (h₁ : V ≤ Spec.map (CommRingCat.ofHom ι) ⁻¹ᵁ (origin A Wa ⁻¹ᵁ U))
    (h₂ : V ≤ origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    res (HodgePower R W 24) h₁
      ((comparisonPower C).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι))
          (localPower A Wa 24 U a))) =
    res (HodgePower R W 24) h₂
      (localPower R W 24 (C.map ⁻¹ᵁ U) (C.map.app U a)) := by
  letI : Algebra A R := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap A Wa) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Wa.toProjective
  change res _ h₁ ((tensorComparison _ _ _ _ 24).hom.app _
    (Scheme.Modules.pullbackLocalSection _ (tensorPowerSection _ _ 24 _ _))) = _
  rw [tensorComparison_section]
  change (tensorPower (Base R) (Hodge R W) 24).presheaf.map (homOfLE h₁).op
    (tensorPowerSection _ _ 24 _ _) =
      (tensorPower (Base R) (Hodge R W) 24).presheaf.map (homOfLE h₂).op
        (tensorPowerSection _ _ 24 _ _)
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection (Base R) (Hodge R W) 24 V)
    (pointedDifferentialIso_D (structureMap A Wa) (structureMap R W) C.map C.cartesian
      (origin A Wa) (origin R W) C.pointed U a V h₁ h₂)

/-- Naturality includes the coefficient evaluated through the same pointed
square, and restriction to an arbitrary smaller target open. -/
lemma comparison_value {A R : Type u} [CommRing A] [CommRing R]
    {Wa : WeierstrassCurve A} [Wa.IsElliptic] {W : WeierstrassCurve R}
    {ι : A →+* R} (C : Comparison A R Wa W ι)
    (U : (Curve A Wa).Opens) (V : (Curve R W).Opens)
    (h : V ≤ C.map ⁻¹ᵁ U)
    (hp : origin R W ⁻¹ᵁ V ≤ Spec.map (CommRingCat.ofHom ι) ⁻¹ᵁ (origin A Wa ⁻¹ᵁ U))
    (r a : Γ(Curve A Wa, U)) :
    res (HodgePower R W 24) hp
      ((comparisonPower C).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι))
          ((origin A Wa).app U r • localPower A Wa 24 U a))) =
      (origin R W).app V (C.map.appLE U V h r) •
        localPower R W 24 V (C.map.appLE U V h a) := by
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul]
  rw [comparison_localPower C U a (origin R W ⁻¹ᵁ V) hp (fun _ hx => h hx)]
  rw [InitialHodgeSection.power_res R W 24 h]
  congr 1
  exact InitialSectionNaturality.scalar_square (Spec.map (CommRingCat.ofHom ι))
    (origin A Wa) (origin R W) C.map C.pointed U V h hp r

open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- A normal-model initial coefficient specializes as both an entire section
identity on the complement and the canonical Hodge tensor on the base. -/
lemma model_initial (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (v : UnitSection R W G 5) (hv : IsKatoUnit R W G 5 v)
    (d : Sections (HodgePower R W 24)) (hd : IsD2 W d)
    (M : NormalModel R W)
    (T : (Curve M.ring M.equation).affineOpens) [Nonempty T.1]
    (b : Γ(Curve M.ring M.equation, T.1))
    (hb : ArithmeticThetaRelativeDiscriminantR0171.IdentityChart
      M.ring M.equation M.law 5 T b)
    (V : (Curve R W).Opens) (eT : V ≤ M.comparison.map ⁻¹ᵁ T.1) :
    ∃ η : (Γ(Curve M.ring M.equation, T.1))ˣ,
      5 * restrict (complement R W G 5) (V ⊓ complement R W G 5)
          inf_le_right (v : _) =
        M.comparison.map.appLE T.1 (V ⊓ complement R W G 5)
          (inf_le_left.trans eT) ((η : _) * b^24) ∧
      res (HodgePower R W 24) le_top d =
        (origin R W).app V (M.comparison.map.appLE T.1 V eT (η : _)) •
          localPower R W 24 V (M.comparison.map.appLE T.1 V eT b) := by
  obtain ⟨hC, g, hg, s, _, hs, eC, hvM⟩ := hv M
  letI := hC
  obtain ⟨η, hη, hdη⟩ := localD_represents M.ring M.equation M.law M.originLaw
    g hg T b hb
  refine ⟨η, ?_, ?_⟩
  · have H := product_pullback M.comparison.map T.1
      (complement M.ring M.equation M.law 5) (V ⊓ complement R W G 5)
      (inf_le_left.trans eT) (inf_le_right.trans eC) s
      (5 : Γ(Curve M.ring M.equation, T.1)) ((η : _) * b^24)
      (by rw [hs, map_ofNat, mul_comm]; exact hη)
    rw [map_ofNat, mul_comm] at H
    rw [hvM]
    simpa only [restrict, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] using H
  · have hp : origin R W ⁻¹ᵁ V ≤
        Spec.map (CommRingCat.ofHom M.scalar.toRingHom) ⁻¹ᵁ
          (origin M.ring M.equation ⁻¹ᵁ T.1) := by
      intro x hx
      change (Spec.map (CommRingCat.ofHom M.scalar.toRingHom) ≫
        origin M.ring M.equation) x ∈ T.1
      rw [← M.comparison.pointed]
      exact eT hx
    calc
      res (HodgePower R W 24) le_top d =
          res (HodgePower R W 24) hp
            ((comparisonPower M.comparison).hom.app _
              (Scheme.Modules.pullbackLocalSection
                (Spec.map (CommRingCat.ofHom M.scalar.toRingHom))
                (res (HodgePower M.ring M.equation 24) le_top
                  (localD M.ring M.equation M.law M.originLaw)))) := by
        rw [hd M]
        unfold value pull
        rw [InitialHodgeSection.res_res, ← InitialSectionNaturality.pullback_res,
          ← hom_res, InitialHodgeSection.res_res]
      _ = _ := by
        change res (HodgePower M.ring M.equation 24) le_top
          (localD M.ring M.equation M.law M.originLaw) =
          (origin M.ring M.equation).app T.1 (η : _) •
            localPower M.ring M.equation 24 T.1 b at hdη
        rw [hdη]
        exact comparison_value M.comparison T.1 V eT hp (η : _) b

lemma restrict_natCast {X : Scheme.{u}} (U V : X.Opens) (e : V ≤ U) (n : ℕ) :
    restrict U V e (n : Γ(X, U)) = (n : Γ(X, V)) := map_natCast _ n

lemma restrict_five {X : Scheme.{u}} (U V : X.Opens) (e : V ≤ U) :
    restrict U V e (5 : Γ(X, U)) = (5 : Γ(X, V)) := map_ofNat _ 5

/-- Restriction of evaluated tensors uses only the actual sheaf maps. -/
lemma value_res (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (n : ℕ) {U V : (Curve R W).Opens} (h : V ≤ U)
    (e a : Γ(Curve R W, U)) :
    res (HodgePower R W n) (show origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ U from fun _ hx => h hx)
      ((origin R W).app U e • localPower R W n U a) =
    (origin R W).app V (restrict U V h e) •
      localPower R W n V (restrict U V h a) := by
  rw [InitialHodgeSection.res_smul, InitialHodgeSection.power_res R W n h]
  congr 1
  exact ConcreteCategory.congr_hom ((origin R W).naturality (homOfLE h).op).symm e

/-- Restriction of an arbitrary identity chart retains its scheme-theoretic
ideal equalities and the regular generator. -/
lemma chart_restrict (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (U V : (Curve R W).affineOpens) (e : V.1 ≤ U.1)
    (a : Γ(Curve R W, U.1)) (ha : AffineIdentityChart R W G 5 U a) :
    AffineIdentityChart R W G 5 V (restrict U.1 V.1 e a) := by
  refine ⟨regular_restrict U V e a ha.1, ?_, ?_⟩
  · rw [← (identityIdeal R W).map_ideal e, ha.2.1,
      Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← (torsionIdeal R W G 5).map_ideal e,
      ← (identityIdeal R W).map_ideal e, ha.2.2]

/-- Any whole-chart coefficient of the given unit computes the prescribed
normal-model discriminant tensor. -/
lemma coefficient_tensor (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (v : UnitSection R W G 5) (hv : IsKatoUnit R W G 5 v)
    (d : Sections (HodgePower R W 24)) (hd : IsD2 W d)
    (U : (Curve R W).affineOpens) (a : Γ(Curve R W, U.1))
    (ha : AffineIdentityChart R W G 5 U a) (ε : (Γ(Curve R W, U.1))ˣ)
    (hε : 5 * restrict (complement R W G 5) (U.1 ⊓ complement R W G 5)
      inf_le_right (v : _) =
      restrict U.1 (U.1 ⊓ complement R W G 5) inf_le_left ((ε : _) * a^24)) :
    res (HodgePower R W 24) le_top d =
      (origin R W).app U.1 (ε : _) • localPower R W 24 U.1 a := by
  obtain ⟨M⟩ := normal_discriminant_model R W
  apply sections_eq_local
  intro x hx
  obtain ⟨T, b, hxT, hb⟩ := relative_identity_torsion_neighborhood
    M.ring M.equation M.law M.originLaw 5 (by norm_num)
    (Spec.map (CommRingCat.ofHom M.scalar.toRingHom) x)
  have hxT' : origin R W x ∈ M.comparison.map ⁻¹ᵁ T.1 := by
    change (origin R W ≫ M.comparison.map) x ∈ T.1
    rw [M.comparison.pointed]
    exact hxT
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show origin R W x ∈ U.1 ⊓ M.comparison.map ⁻¹ᵁ T.1 from ⟨hx, hxT'⟩)
  let V' : (Curve R W).affineOpens := ⟨V, hV⟩
  have e : V ≤ U.1 := hVU.trans inf_le_left
  have eT : V ≤ M.comparison.map ⁻¹ᵁ T.1 := hVU.trans inf_le_right
  letI : Nonempty T.1 := ⟨⟨_, hxT⟩⟩
  obtain ⟨η, hη, hdη⟩ := model_initial R W G v hv d hd M T b hb V eT
  let ar := restrict U.1 V e a
  let er := restrict U.1 V e (ε : _)
  let br := M.comparison.map.appLE T.1 V eT b
  let fr := M.comparison.map.appLE T.1 V eT (η : _)
  have haV := chart_restrict R W G U V' e a ha
  have hbI : (identityIdeal M.ring M.equation).ideal T = Ideal.span {b} := hb.2.1
  have hIb : (identityIdeal R W).ideal V' = Ideal.span {br} := by
    rw [← NormalModelUnitSpecialization.identity_comap M.comparison,
      Scheme.IdealSheafData.ideal_comap_of_le _ _ T V' eT, hbI,
      Ideal.map_span, Set.image_singleton]
  have hεV : 5 * restrict (complement R W G 5) (V ⊓ complement R W G 5)
      inf_le_right (v : _) =
      restrict V (V ⊓ complement R W G 5) inf_le_left (er * ar^24) := by
    have H := congrArg
      (restrict (U.1 ⊓ complement R W G 5) (V ⊓ complement R W G 5)
        (inf_le_inf e le_rfl)) hε
    simpa only [er, ar, restrict_mul, restrict_pow, restrict_five, restrict_trans] using H
  have hηV : 5 * restrict (complement R W G 5) (V ⊓ complement R W G 5)
      inf_le_right (v : _) =
      restrict V (V ⊓ complement R W G 5) inf_le_left (fr * br^24) := by
    simpa only [fr, br, restrict, map_mul, map_pow, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map] using hη
  have heq : er * ar^24 = fr * br^24 :=
    complement_restrict_injective (torsionIdeal R W G 5) V' ar haV.1
      (haV.2.2.trans haV.2.1) (hεV.symm.trans hηV)
  have hval := value_eq R W V' ar br er fr 24 haV.1 haV.2.1 hIb heq
  refine ⟨origin R W ⁻¹ᵁ V, hxV, (fun _ hy => e hy), ?_⟩
  rw [InitialHodgeSection.res_res, value_res R W 24 e]
  exact hdη.trans hval.symm

end ArbitraryUnitInitialCoefficient

open ArithmeticThetaRelativeKatoR0169

/-- The same canonical five-Kato unit has the exact prescribed discriminant
initial coefficient over every rational algebra, on every identity chart. -/
theorem arbitrary_unit_initial_coefficient :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : ArithmeticThetaRelativeKatoR0169.Law R W),
      ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G →
      ∀ (v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection R W G 5)
        (d : ArithmeticThetaArbitraryDiscriminantR0243.Sections
          (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W 24)),
      ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit R W G 5 v →
      ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W d → AffineInitial R W G v d := by
  intro R _ _ W _ G hG v d hv hd U a ha
  obtain ⟨ε, hε⟩ := ArbitraryUnitInitialCoefficient.chart_equation R W G hG v hv U a ha
  exact ⟨ε, hε, ArbitraryUnitInitialCoefficient.coefficient_tensor R W G v hv d hd U a ha ε hε⟩

#print axioms arbitrary_unit_initial_coefficient
end ArithmeticThetaKatoInitialR0253
