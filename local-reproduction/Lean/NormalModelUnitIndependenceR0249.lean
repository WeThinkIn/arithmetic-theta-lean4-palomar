import ArbitraryKatoUnitDefinitionsR0249

/-! Section-level comparison tools for normal-model Kato units. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryKatoUnitR0249
namespace NormalModelUnitIndependence
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaArbitraryDiscriminantR0243.NormalDiscriminantIndependence

section NormalSource
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic]
  [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
  [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
  (G : Law R W) (hG : IsOriginLaw R W G)
  (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)

include hG hc hc6 in
/-- Uniqueness uses the full normalized function on the generic fiber. -/
theorem normalized_unique (g g' : (Curve R W).functionField)
    (hg : Normalized R W G c g) (hg' : Normalized R W G c g') : g = g' := by
  letI : CharZero R := algebraRat.charZero R
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  obtain ⟨f, _, hf⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6
  apply C.field.injective
  exact (hf _ (hg.2 C)).trans (hf _ (hg'.2 C)).symm

include hG hc hc6 in
/-- Existence for the specified law, rather than an existentially selected law. -/
theorem normalized_exists : ∃ g : (Curve R W).functionField, Normalized R W G c g := by
  letI : CharZero R := algebraRat.charZero R
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

theorem complement_avoids (x : Curve R W) (hx : x ∈ complement R W G c) :
    G.schemeNsmul c x ∉ Set.range (origin R W) := by
  intro ht
  exact hx ((RelativeKatoFiberSpecialization.torsion_support R W G c x).mpr ht)

include hG hc in
theorem complement_nonempty : Nonempty (complement R W G c) := by
  refine ⟨⟨genericPoint (Curve R W), ?_⟩⟩
  exact RelativeKatoFiberSpecialization.generic_not_support _
    ((relative_torsion_cartier R W G hG).2 c (by omega))

end NormalSource

/-- Different witnesses of `FromModel` for the same actual model agree even
over nonreduced target rings. Only the normal source uses a function field. -/
theorem from_model_unique
    (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (G : Law R W) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (M : NormalModel R W) (v v' : UnitSection R W G c)
    (hv : FromModel R W G M c v) (hv' : FromModel R W G M c v') : v = v' := by
  obtain ⟨hU, g, hg, a, _, ha, e, hv⟩ := hv
  obtain ⟨hU', g', hg', a', _, ha', e', hv'⟩ := hv'
  letI := hU
  have hgEq := normalized_unique M.ring M.equation M.law M.originLaw c hc hc6 g g' hg hg'
  have haEq : a = a' := (Curve M.ring M.equation).germToFunctionField_injective _
    (ha.trans (hgEq.trans ha'.symm))
  apply Units.ext
  rw [hv, hv', haEq]

section NormalComparison
variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
  [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
  {W : WeierstrassCurve R} [W.IsElliptic]
  [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
  [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
  {V : WeierstrassCurve S} [V.IsElliptic]
  [IsIntegral (Curve S V)] [IsLocallyNoetherian (Curve S V)]
  [IsIntegral (GenericCurve S V)] [IsLocallyNoetherian (GenericCurve S V)]
  {ι : R →+* S} (C : Comparison R S W V ι)
  (G : Law R W) (hG : IsOriginLaw R W G)
  (H : Law S V) (hH : IsOriginLaw S V H)

include hG hH in
theorem normal_complement_le (c : ℕ) :
    complement S V H c ≤ C.map ⁻¹ᵁ complement R W G c := by
  have hb : IsBaseChange R W G S V H ι C.map :=
    ⟨C.cartesian, C.pointed, comparison_nsmul C G hG H hH⟩
  intro x hx ht
  apply hx
  apply (RelativeKatoFiberSpecialization.torsion_support S V H c x).mpr
  apply (RelativeKatoFiberSpecialization.torsion_preimage R W G S V H ι C.map hb c x).mp
  exact (RelativeKatoFiberSpecialization.torsion_support R W G c (C.map x)).mp ht

include hG hH in
/-- Normal-base naturality upgraded from equality of generic restrictions
to equality of the actual complete sections. -/
theorem normal_section_pullback (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (g' : (Curve S V).functionField) (hg' : Normalized S V H c g')
    (U : (Curve R W).Opens) (T : (Curve S V).Opens)
    [Nonempty U] [Nonempty T] (e : T ≤ C.map ⁻¹ᵁ U)
    (a : Γ(Curve R W, U)) (a' : Γ(Curve S V, T))
    (hU : ∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W))
    (ha : (Curve R W).germToFunctionField U a = g)
    (ha' : (Curve S V).germToFunctionField T a' = g') :
    C.map.appLE U T e a = a' := by
  apply (Curve S V).germToFunctionField_injective T
  have hb : IsBaseChange R W G S V H ι C.map :=
    ⟨C.cartesian, C.pointed, comparison_nsmul C G hG H hH⟩
  exact ((relative_kato_arbitrary_base_change R W G hG S V H hH ι C.map hb
    c hc hc6 g hg g' hg' U T e a hU ha).2).trans ha'.symm

end NormalComparison

/-- A literal normal refinement gives equality after arbitrary target
specialization. The target ring is not assumed reduced or Noetherian. -/
theorem from_model_refinement
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (G : Law R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (M N : NormalModel R W) (ι : N.ring →+* M.ring)
    (C : Comparison N.ring M.ring N.equation M.equation ι)
    (hmap : M.comparison.map ≫ C.map = N.comparison.map)
    (v v' : UnitSection R W G c)
    (hv : FromModel R W G M c v) (hv' : FromModel R W G N c v') : v = v' := by
  obtain ⟨hM, gM, hgM, aM, _, haM, eM, hv⟩ := hv
  obtain ⟨hN, gN, hgN, aN, _, haN, eN, hv'⟩ := hv'
  letI := hM
  letI := hN
  let e := normal_complement_le C N.law N.originLaw M.law M.originLaw c
  have ha := normal_section_pullback C N.law N.originLaw M.law M.originLaw
    c hc hc6 gN hgN gM hgM _ _ e aN aM
    (complement_avoids N.ring N.equation N.law c) haN haM
  apply Units.ext
  rw [hv, hv', ← ha]
  have hh := Scheme.Hom.appLE_comp_appLE M.comparison.map C.map
    (complement N.ring N.equation N.law c)
    (complement M.ring M.equation M.law c) (complement R W G c) e eM
  have hvh := congrArg
    (fun f : Γ(Curve N.ring N.equation, complement N.ring N.equation N.law c) ⟶
      Γ(Curve R W, complement R W G c) => f aN) hh
  simpa only [hmap, CommRingCat.comp_apply] using hvh

/-- The complete independence statement over a normal target, used only as
a provider before specializing universal normal parameter rings. -/
theorem independence_normal
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (M N : NormalModel R W) (v v' : UnitSection R W G c)
    (hv : FromModel R W G M c v) (hv' : FromModel R W G N c v') : v = v' := by
  obtain ⟨g, hg⟩ := normalized_exists R W G hG c hc hc6
  letI := complement_nonempty R W G hG c hc
  obtain ⟨hM, gM, hgM, aM, _, haM, eM, hv⟩ := hv
  obtain ⟨hN, gN, hgN, aN, _, haN, eN, hv'⟩ := hv'
  letI := hM
  letI := hN
  have hbm : IsBaseChange M.ring M.equation M.law R W G M.scalar.toRingHom M.comparison.map :=
    ⟨M.comparison.cartesian, M.comparison.pointed,
      comparison_nsmul M.comparison M.law M.originLaw G hG⟩
  have hbn : IsBaseChange N.ring N.equation N.law R W G N.scalar.toRingHom N.comparison.map :=
    ⟨N.comparison.cartesian, N.comparison.pointed,
      comparison_nsmul N.comparison N.law N.originLaw G hG⟩
  apply Units.ext
  apply (Curve R W).germToFunctionField_injective (complement R W G c)
  rw [hv, hv']
  exact ((relative_kato_arbitrary_base_change M.ring M.equation M.law M.originLaw
    R W G hG M.scalar.toRingHom M.comparison.map hbm c hc hc6 gM hgM g hg
    _ _ eM aM (complement_avoids M.ring M.equation M.law c) haM).2).trans
    ((relative_kato_arbitrary_base_change N.ring N.equation N.law N.originLaw
      R W G hG N.scalar.toRingHom N.comparison.map hbn c hc hc6 gN hgN g hg
      _ _ eN aN (complement_avoids N.ring N.equation N.law c) haN).2).symm

/- A section together with its actual open domain. Pullback therefore keeps
the domain equation as well as all nilpotent information in the section. -/
structure OpenSection (X : Scheme.{u}) where
  domain : X.Opens
  val : Γ(X, domain)

namespace OpenSection

def pull {X Y : Scheme.{u}} (f : X ⟶ Y) (s : OpenSection Y) : OpenSection X :=
  ⟨f ⁻¹ᵁ s.domain, f.app s.domain s.val⟩

theorem pull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : OpenSection Z) : pull f (pull g s) = pull (f ≫ g) s := rfl

theorem ext {X : Scheme.{u}} (s t : OpenSection X) (h : s.domain = t.domain)
    (hv : restrict s.domain t.domain h.ge s.val = t.val) : s = t := by
  cases s with
  | mk U a =>
    cases t with
    | mk V b =>
      dsimp at h
      subst V
      have hab : a = b := by simpa [restrict] using hv
      subst b
      rfl

theorem restrict_eq_of_eq {X : Scheme.{u}} (s t : OpenSection X) (h : s = t)
    (U : X.Opens) (hs : U ≤ s.domain) (ht : U ≤ t.domain) :
    restrict s.domain U hs s.val = restrict t.domain U ht t.val := by
  subst t
  rfl

theorem restrict_pull {X Y : Scheme.{u}} (f : X ⟶ Y) (s : OpenSection Y)
    (U : X.Opens) (h : U ≤ (pull f s).domain) :
    restrict (pull f s).domain U h (pull f s).val = f.appLE s.domain U h s.val := rfl

end OpenSection

section ChosenNormalSection
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic]
  [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
  [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
  (G : Law R W) (hG : IsOriginLaw R W G)
  (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)

include hc6 in
theorem normal_representative_exists :
    ∃ a : Γ(Curve R W, complement R W G c),
      Normalized R W G c (@Scheme.germToFunctionField (Curve R W) _
        (complement R W G c) (complement_nonempty R W G hG c hc) a) ∧ IsUnit a := by
  letI := complement_nonempty R W G hG c hc
  obtain ⟨g, hg⟩ := normalized_exists R W G hG c hc hc6
  obtain ⟨a, ha, _⟩ := RelativeKatoFiberSpecialization.source_unit R W G hG c hc hc6 g hg
    (complement R W G c) (complement_avoids R W G c)
  exact ⟨a, ha.1.symm ▸ hg, ha.2⟩

def normalSection : OpenSection (Curve R W) :=
  ⟨complement R W G c, (normal_representative_exists R W G hG c hc hc6).choose⟩

theorem normalSection_spec :
    Normalized R W G c (@Scheme.germToFunctionField (Curve R W) _
      (complement R W G c) (complement_nonempty R W G hG c hc)
      (normalSection R W G hG c hc hc6).val) ∧
    IsUnit (normalSection R W G hG c hc hc6).val :=
  (normal_representative_exists R W G hG c hc hc6).choose_spec

end ChosenNormalSection

/-- Full open-section naturality over normal bases, retaining the entire
torsion-complement open as well as the complete function. -/
theorem normalSection_naturality
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    {W : WeierstrassCurve R} [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    {V : WeierstrassCurve S} [V.IsElliptic]
    [IsIntegral (Curve S V)] [IsLocallyNoetherian (Curve S V)]
    [IsIntegral (GenericCurve S V)] [IsLocallyNoetherian (GenericCurve S V)]
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law S V) (hH : IsOriginLaw S V H)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull C.map (normalSection R W G hG c hc hc6) =
      normalSection S V H hH c hc hc6 := by
  letI := complement_nonempty R W G hG c hc
  letI := complement_nonempty S V H hH c hc
  have hb : IsBaseChange R W G S V H ι C.map :=
    ⟨C.cartesian, C.pointed, comparison_nsmul C G hG H hH⟩
  have he : C.map ⁻¹ᵁ complement R W G c = complement S V H c := by
    ext x
    change (¬ C.map x ∈ (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G c).support) ↔
      (¬ x ∈ (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal S V H c).support)
    rw [RelativeKatoFiberSpecialization.torsion_support R W G,
      RelativeKatoFiberSpecialization.torsion_support S V H,
      RelativeKatoFiberSpecialization.torsion_preimage R W G S V H ι C.map hb]
  apply OpenSection.ext _ _ he
  rw [OpenSection.restrict_pull]
  letI : Nonempty (normalSection R W G hG c hc hc6).domain := complement_nonempty R W G hG c hc
  letI : Nonempty (normalSection S V H hH c hc hc6).domain := complement_nonempty S V H hH c hc
  exact normal_section_pullback C G hG H hH c hc hc6 _
    (normalSection_spec R W G hG c hc hc6).1 _
    (normalSection_spec S V H hH c hc hc6).1 _ _ _ _ _
    (complement_avoids R W G c) rfl rfl

namespace UniversalSection
open CoefficientParameters

def sectionOver {k R : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic]
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) : OpenSection (Curve R W) :=
  OpenSection.pull (classifyingComparison ι W).map
    (normalSection (CoefficientParameters.Ring k) (universal k) (universalLaw k) (universalLaw_origin k) c hc hc6)

theorem coefficient_naturality {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S] (ι : k →+* R) (ρ : R →+* S)
    (W : WeierstrassCurve R) [W.IsElliptic]
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (coefficientComparison W ρ).map (sectionOver ι W c hc hc6) =
      sectionOver (ρ.comp ι) (W.map ρ) c hc hc6 := by
  unfold sectionOver
  rw [OpenSection.pull_comp, classifyingComparison_comp]

theorem normal_classifying
    {k R : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    sectionOver ι W c hc hc6 = normalSection R W G hG c hc hc6 :=
  normalSection_naturality (classifyingComparison ι W) (universalLaw k)
    (universalLaw_origin k) G hG c hc hc6

theorem normal_comparison
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    (ι : k →+* R) (κ : k →+* S)
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} [V.IsElliptic]
    {ρ : R →+* S} (C : Comparison R S W V ρ)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull C.map (sectionOver ι W c hc hc6) = sectionOver κ V c hc hc6 := by
  have hgR := relative_curve_geometry R W
  have hgS := relative_curve_geometry S V
  letI := hgR.1
  letI := hgR.2.1
  letI := hgR.2.2.2.1
  letI := hgR.2.2.2.2.1
  letI := hgS.1
  letI := hgS.2.1
  letI := hgS.2.2.2.1
  letI := hgS.2.2.2.2.1
  obtain ⟨G, hG⟩ := normal_originLaw_exists R W
  obtain ⟨H, hH⟩ := normal_originLaw_exists S V
  rw [normal_classifying ι W G hG, normal_classifying κ V H hH]
  exact normalSection_naturality C G hG H hH c hc hc6

theorem coefficient_target_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S] (ι : k →+* R) (ρ : R →+* S)
    (W : WeierstrassCurve R) [W.IsElliptic]
    (V : WeierstrassCurve S) [V.IsElliptic] (hV : W.map ρ = V)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (comparisonTargetEq (coefficientComparison W ρ) hV).map
      (sectionOver ι W c hc hc6) = sectionOver (ρ.comp ι) V c hc hc6 := by
  subst V
  exact coefficient_naturality ι ρ W c hc hc6

theorem variable_specialization
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] (ι : k →+* R) (ρ : R →+* S)
    (W : WeierstrassCurve R) [W.IsElliptic] (B : WeierstrassCurve.VariableChange R)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (variableComparison (W.map ρ) (B.map ρ)).map
      (sectionOver (ρ.comp ι) (W.map ρ) c hc hc6) =
        sectionOver (ρ.comp ι) (B.map ρ • W.map ρ) c hc hc6 := by
  have hs := congrArg (fun f => OpenSection.pull f (sectionOver ι W c hc hc6))
    (variableComparison_square W B ρ)
  rw [← OpenSection.pull_comp, ← OpenSection.pull_comp,
    normal_comparison ι ι (variableComparison W B),
    coefficient_target_naturality, coefficient_naturality] at hs
  exact hs.symm

theorem variable_equation_transport
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι κ : k →+* S) (hι : ι = κ)
    (W V : WeierstrassCurve S) [W.IsElliptic] [V.IsElliptic] (hW : W = V)
    (B C : WeierstrassCurve.VariableChange S) (hB : B = C)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (h : OpenSection.pull (variableComparison W B).map (sectionOver ι W c hc hc6) =
      sectionOver ι (B • W) c hc hc6) :
    OpenSection.pull (variableComparison V C).map (sectionOver κ V c hc hc6) =
      sectionOver κ (C • V) c hc hc6 := by
  subst κ
  subst V
  subst C
  exact h

theorem variable_naturality
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι : k →+* S) (W : WeierstrassCurve S) [W.IsElliptic]
    (B : WeierstrassCurve.VariableChange S)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (variableComparison W B).map (sectionOver ι W c hc hc6) =
      sectionOver ι (B • W) c hc hc6 := by
  let R := CoefficientParameters.Ring k
  let T := ChangeParameters.Ring R
  have hn := ChangeParameters.normal_parameters R
  letI : IsDomain T := hn.1
  letI : IsNoetherianRing T := hn.2.1
  letI : IsIntegrallyClosed T := hn.2.2
  let A := (universal k).map (algebraMap R T)
  let C := ChangeParameters.universal R
  let φ := ChangeParameters.specialize (classifying ι W) B
  have hscalar : φ.comp (algebraMap k T) = ι := by
    ext a
    change φ (algebraMap R T (algebraMap k R a)) = ι a
    rw [ChangeParameters.specialize_scalar, classifying_scalar]
  have hbase : φ.comp (algebraMap R T) = classifying ι W :=
    RingHom.ext (ChangeParameters.specialize_scalar (classifying ι W) B)
  have hA : A.map φ = W := by
    change ((universal k).map (algebraMap R T)).map φ = W
    rw [WeierstrassCurve.map_map, hbase, classifying_universal]
  have hC : C.map φ = B := ChangeParameters.specialize_universal _ _
  have h := variable_specialization (algebraMap k T) φ A C c hc hc6
  exact variable_equation_transport (φ.comp (algebraMap k T)) ι hscalar
    (A.map φ) W hA (C.map φ) B hC c hc hc6 h

theorem variable_target_naturality
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι : k →+* S) (W : WeierstrassCurve S) [W.IsElliptic]
    (B : WeierstrassCurve.VariableChange S)
    (V : WeierstrassCurve S) [V.IsElliptic] (hV : B • W = V)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (comparisonTargetEq (variableComparison W B) hV).map
      (sectionOver ι W c hc hc6) = sectionOver ι V c hc hc6 := by
  subst V
  exact variable_naturality ι W B c hc hc6

/-- Local coordinate reconstruction identifies the specified scheme map, so
the specialization identity applies to every pointed Cartesian comparison. -/
theorem local_comparison_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S] [IsLocalRing S]
    (ι : k →+* R) {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic] {ρ : R →+* S}
    (C : Comparison R S W V ρ)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull C.map (sectionOver ι W c hc hc6) =
      sectionOver (ρ.comp ι) V c hc hc6 := by
  obtain ⟨B, hB, φ, hφ, hcB, hm⟩ := local_comparison_coordinates C
  let D := comparisonTargetEq (variableComparison (W.map ρ) B) hB
  have hmap : D.map ≫ (coefficientComparison W ρ).map = C.map := by
    rw [comparisonTargetEq_map, variableComparison_map _ _ φ hφ hcB]
    exact hm.symm
  rw [← hmap, ← OpenSection.pull_comp, coefficient_naturality]
  exact variable_target_naturality (ρ.comp ι) (W.map ρ) B V hB c hc hc6

end UniversalSection

def modelSection {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} (M : NormalModel R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) : OpenSection (Curve R W) :=
  OpenSection.pull M.comparison.map
    (normalSection M.ring M.equation M.law M.originLaw c hc hc6)

theorem modelSection_local
    {R : Type u} [CommRing R] [Algebra ℚ R] [IsLocalRing R]
    {W : WeierstrassCurve R} [W.IsElliptic] (M : NormalModel R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    modelSection M c hc hc6 = UniversalSection.sectionOver (rationalMap R) W c hc hc6 := by
  unfold modelSection
  rw [← UniversalSection.normal_classifying (rationalMap M.ring) M.equation M.law M.originLaw,
    UniversalSection.local_comparison_naturality, rationalMap_naturality M.scalar]

theorem modelSection_baseChange
    {R S : Type u} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    {W : WeierstrassCurve R} (M : NormalModel R W) (ρ : R →ₐ[ℚ] S)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    OpenSection.pull (coefficientComparison W ρ.toRingHom).map (modelSection M c hc hc6) =
      modelSection (baseChangeModel M ρ) c hc hc6 := rfl

theorem from_model_restrict
    {R : Type u} [CommRing R] [Algebra ℚ R] {W : WeierstrassCurve R}
    (G : Law R W) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (M : NormalModel R W) (v : UnitSection R W G c)
    (hv : FromModel R W G M c v) :
    ∃ e : complement R W G c ≤ (modelSection M c hc hc6).domain,
      (v : _) = restrict (modelSection M c hc hc6).domain (complement R W G c) e
        (modelSection M c hc hc6).val := by
  obtain ⟨hU, g, hg, a, _, ha, e, hv⟩ := hv
  letI := hU
  let s := normalSection M.ring M.equation M.law M.originLaw c hc hc6
  have hs := (normalSection_spec M.ring M.equation M.law M.originLaw c hc hc6).1
  have hgEq := normalized_unique M.ring M.equation M.law M.originLaw c hc hc6 g _ hg hs
  have haEq : a = s.val := (Curve M.ring M.equation).germToFunctionField_injective _
    (ha.trans hgEq)
  refine ⟨e, ?_⟩
  rw [hv, haEq]
  rfl

namespace OpenSection

theorem val_eq {X : Scheme.{u}} {U : X.Opens} {a b : Γ(X, U)}
    (h : (⟨U, a⟩ : OpenSection X) = ⟨U, b⟩) : a = b := by
  cases h
  rfl

/-- Jointly surjective flat pullbacks detect sections, using injectivity on
local rings. In particular, this does not discard nilpotents. -/
theorem eq_of_flat_pull_eq {X : Scheme.{u}} {I : Type*}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, Flat (f i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : Y i), f i y = x)
    (s t : OpenSection X) (h : ∀ i, pull (f i) s = pull (f i) t) : s = t := by
  have hd : s.domain = t.domain := by
    ext x
    obtain ⟨i, y, rfl⟩ := hcover x
    have he := congrArg OpenSection.domain (h i)
    exact SetLike.ext_iff.mp he y
  rcases s with ⟨U, a⟩
  rcases t with ⟨V, b⟩
  dsimp at hd
  subst V
  have hab : a = b := by
    apply TopCat.Presheaf.section_ext X.sheaf U a b
    intro x hx
    obtain ⟨i, y, rfl⟩ := hcover x
    have hi : Function.Injective ((f i).stalkMap y) := by
      algebraize [((f i).stalkMap y).hom]
      have : Module.FaithfullyFlat (X.presheaf.stalk (f i y)) ((Y i).presheaf.stalk y) :=
        @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
          (Flat.stalkMap (f i) y) ((f i).toLRSHom.prop y)
      exact ‹RingHom.FaithfullyFlat ((f i).stalkMap y).hom›.injective
    apply hi
    change (f i).stalkMap y (X.presheaf.germ U (f i y) hx a) =
      (f i).stalkMap y (X.presheaf.germ U (f i y) hx b)
    rw [(f i).germ_stalkMap_apply U y hx a, (f i).germ_stalkMap_apply U y hx b]
    have hv : (f i).app U a = (f i).app U b := val_eq (h i)
    rw [hv]
  subst b
  rfl

/-- Base localizations form a jointly surjective flat family of actual
coefficient maps, so they detect complete open sections of the curve. -/
theorem eq_of_localizations
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (s t : OpenSection (Curve R W))
    (h : ∀ p : PrimeSpectrum R,
      pull (coefficientComparison W (algebraMap R (Localization.AtPrime p.asIdeal))).map s =
      pull (coefficientComparison W (algebraMap R (Localization.AtPrime p.asIdeal))).map t) :
    s = t := by
  let Y (p : PrimeSpectrum R) := Curve (Localization.AtPrime p.asIdeal)
    (W.map (algebraMap R (Localization.AtPrime p.asIdeal)))
  let f (p : PrimeSpectrum R) : Y p ⟶ Curve R W :=
    (coefficientComparison W (algebraMap R (Localization.AtPrime p.asIdeal))).map
  have hf (p : PrimeSpectrum R) : Flat (f p) := by
    let S := Localization.AtPrime p.asIdeal
    let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
    letI : Flat b := Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S p.asIdeal.primeCompl))
    exact MorphismProperty.of_isPullback (P := @Flat)
      (coefficientComparison W (algebraMap R S)).cartesian.flip (inferInstance : Flat b)
  letI := hf
  apply eq_of_flat_pull_eq Y f _ s t h
  intro x
  let p : PrimeSpectrum R := structureMap R W x
  let S := Localization.AtPrime p.asIdeal
  let y : Spec (CommRingCat.of S) := IsLocalRing.closedPoint S
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R S)) y = structureMap R W x := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.under_maximalIdeal S p.asIdeal
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (coefficientComparison W (algebraMap R S)).cartesian x y hy.symm
  exact ⟨p, z, hz⟩

end OpenSection

theorem modelSection_independence
    {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} [W.IsElliptic] (M N : NormalModel R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) :
    modelSection M c hc hc6 = modelSection N c hc hc6 := by
  apply OpenSection.eq_of_localizations W
  intro p
  let ρ := IsScalarTower.toAlgHom ℚ R (Localization.AtPrime p.asIdeal)
  change OpenSection.pull (coefficientComparison W ρ.toRingHom).map (modelSection M c hc hc6) =
    OpenSection.pull (coefficientComparison W ρ.toRingHom).map (modelSection N c hc hc6)
  rw [modelSection_baseChange, modelSection_baseChange, modelSection_local, modelSection_local]

end NormalModelUnitIndependence

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaArbitraryDiscriminantR0243
open NormalModelUnitIndependence

/-- Independence of the full Kato unit over every rational-algebra target.
The comparison uses universal normal parameter sections and flat localization
descent, preserving the complete structure sheaf on nonreduced targets. -/
theorem normal_model_unit_independence
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (_hG : IsOriginLaw R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (M M' : NormalModel R W) (v v' : UnitSection R W G c)
    (hv : FromModel R W G M c v) (hv' : FromModel R W G M' c v') : v = v' := by
  obtain ⟨e, he⟩ := from_model_restrict G c hc hc6 M v hv
  obtain ⟨e', he'⟩ := from_model_restrict G c hc hc6 M' v' hv'
  apply Units.ext
  rw [he, he']
  exact OpenSection.restrict_eq_of_eq _ _ (modelSection_independence M M' c hc hc6) _ e e'
end ArithmeticThetaArbitraryKatoUnitR0249

#print axioms ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence.from_model_unique
#print axioms ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence.normal_section_pullback
#print axioms ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence.from_model_refinement
#print axioms ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence.independence_normal
#print axioms ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence.UniversalSection.variable_naturality
#print axioms ArithmeticThetaArbitraryKatoUnitR0249.normal_model_unit_independence
