module
public import Mathlib
public import GlobalFamilyDiscriminantR0180
public import SchemeDiscriminantNaturalityR0244
public import NormalDiscriminantModelR0243
public import SchemeCotangentCoherenceR0205
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaFiveNormalization374
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)

/-- The actual relative and every generic-fibre normalization, without a
choice of function or an assumed existence assertion. -/
def FiveNormalized (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G 5 g ∧
  ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law 5 (C.field g)

/-- The frame condition on every subopen of the actual 24th Hodge tensor. -/
def FiveFrame (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (V : (Base R).Opens) (h : V ≤ ⊤),
    Function.Bijective (fun a : (Base R).presheaf.obj (Opposite.op V) =>
      a • (HodgePower R W 24).presheaf.map (homOfLE h).op d)

/-- Literal scalar 5 and exponent 24 in the real function field and sheaf.
The identity ideal, torsion ideal, origin evaluation and differential tensor
are retained; epsilon is a unit on the whole actual affine chart. -/
def FiveInitial (g : (Curve R W).functionField)
    (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)),
    (IsRegular a ∧ (origin R W).ker.ideal U = Ideal.span ({a} : Set _) ∧
      ((origin R W).ker.comap (G.schemeNsmul 5)).ideal U =
        (origin R W).ker.ideal U) →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      (5 : (Curve R W).functionField) * g =
        (Curve R W).germToFunctionField U.1 ((ε : _) * a^24) ∧
      (HodgePower R W 24).presheaf.map (homOfLE le_top).op d =
        (origin R W).app U.1 (ε : _) • localPower R W 24 U.1 a

/-- Existence is part of the specification, preventing an empty normalized
function class from making its local equations vacuous. -/
def FiveSpecification (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∃ g : (Curve R W).functionField,
    FiveNormalized R W G g ∧ FiveFrame R W d ∧ FiveInitial R W G g d

lemma fiveNormalized_iff (g : (Curve R W).functionField) :
    FiveNormalized R W G g ↔ Normalized R W G 5 g := Iff.rfl

lemma fiveFrame_iff (d : Γ(HodgePower R W 24, ⊤)) :
    FiveFrame R W d ↔ IsFrame (HodgePower R W 24) ⊤ d := Iff.rfl

lemma fiveInitial_iff (g : (Curve R W).functionField)
    (d : Γ(HodgePower R W 24, ⊤)) :
    FiveInitial R W G g d ↔ RepresentsInitial R W G 5 g d := Iff.rfl

include hG

/-- The expanded, nonvacuous property singles out the original exact section. -/
theorem fiveSpecification_iff_localD (d : Γ(HodgePower R W 24, ⊤)) :
    FiveSpecification R W G d ↔ d = localD R W G hG := by
  constructor
  · rintro ⟨g, hg, hd, hi⟩
    apply (local_discriminant_exists R W G hG).unique
    · refine ⟨(fiveFrame_iff R W d).mp hd, ?_⟩
      intro g' hg'
      have he : g = g' := normalized_unique R W G hG 5
        (by norm_num) (by norm_num) g g'
        ((fiveNormalized_iff R W G g).mp hg) hg'
      rw [← he]
      exact (fiveInitial_iff R W G g d).mp hi
    · exact (local_discriminant_exists R W G hG).exists.choose_spec
  · intro hd
    subst d
    obtain ⟨g, hg⟩ := normalized_exists R W G hG 5 (by norm_num) (by norm_num)
    exact ⟨g, (fiveNormalized_iff R W G g).mpr hg,
      (fiveFrame_iff R W _).mpr (localD_frame R W G hG),
      (fiveInitial_iff R W G g _).mpr (localD_represents R W G hG g hg)⟩

/-- No normalized function or canonical frame is assumed as an input. -/
theorem fiveSpecification_existsUnique :
    ∃! d : Γ(HodgePower R W 24, ⊤), FiveSpecification R W G d := by
  refine ⟨localD R W G hG, (fiveSpecification_iff_localD R W G hG _).mpr rfl, ?_⟩
  intro d hd
  exact (fiveSpecification_iff_localD R W G hG d).mp hd

#print axioms fiveNormalized_iff
#print axioms fiveFrame_iff
#print axioms fiveInitial_iff
#print axioms fiveSpecification_iff_localD
#print axioms fiveSpecification_existsUnique
end ArithmeticThetaFiveNormalization374
namespace ArithmeticThetaPalomarNormalKato378
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) (G : Law R W)
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
/-- Actual relative divisor/norm normalization and the condition for EVERY actual generic comparison. -/
def FiveNormalized (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G 5 g ∧
  ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law 5 (C.field g)
end ArithmeticThetaPalomarNormalKato378
namespace ArithmeticThetaPalomarDifferential365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens}
    (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s
section Differentials
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
/-- The actual structural action of R on every ring of sections. -/
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) :=
  ((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
/-- Actual module sheafification of the relative differential presheaf. -/
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (kaehlerPresheaf f)
def kaehlerToSections (U : X.Opens) :
    ((kaehlerPresheaf f).obj (op U) : Type u) → (Γ(kaehler f, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (kaehlerPresheaf f)).app (op U)).hom s
/-- Universal derivation for this same structural map, followed by the sheafification unit. -/
def relativeD (U : X.Opens) (a : Γ(X, U)) : Γ(kaehler f, U) :=
  letI : Algebra R Γ(X, U) := sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X, U) a)
end Differentials
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarNormalInitial381
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaTensorPower
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj
    (ArithmeticThetaPalomarDifferential365.kaehler (structureMap R W))
abbrev HodgePower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :=
  tensorPower (ArithmeticThetaPalomarNormalInitial381.Base R) (Hodge R W) n
def localDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) :
    Γ(Hodge R W, (origin R W) ⁻¹ᵁ U) :=
  ArithmeticThetaPalomarDifferential365.pullSection (origin R W)
    (ArithmeticThetaPalomarDifferential365.relativeD (structureMap R W) U a)
def localPower (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (n : ℕ) (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) :=
  tensorPowerSection (ArithmeticThetaPalomarNormalInitial381.Base R) (Hodge R W) n
    ((origin R W) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)

/-- The frame condition on every subopen of the actual 24th Hodge tensor. -/
def FiveFrame (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (V : (Base R).Opens) (h : V ≤ ⊤),
    Function.Bijective (fun a : (Base R).presheaf.obj (Opposite.op V) =>
      a • (HodgePower R W 24).presheaf.map (homOfLE h).op d)

/-- Literal scalar 5 and exponent 24 in the real function field and sheaf.
The identity ideal, torsion ideal, origin evaluation and differential tensor
are retained; epsilon is a unit on the whole actual affine chart. -/
def FiveInitial (g : (Curve R W).functionField)
    (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)),
    (IsRegular a ∧ (origin R W).ker.ideal U = Ideal.span ({a} : Set _) ∧
      ((origin R W).ker.comap (G.schemeNsmul 5)).ideal U =
        (origin R W).ker.ideal U) →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      (5 : (Curve R W).functionField) * g =
        (Curve R W).germToFunctionField U.1 ((ε : _) * a^24) ∧
      (HodgePower R W 24).presheaf.map (homOfLE le_top).op d =
        (origin R W).app U.1 (ε : _) • localPower R W 24 U.1 a

/-- Existence is part of the specification, preventing an empty normalized
function class from making its local equations vacuous. -/
def FiveSpecification (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∃ g : (Curve R W).functionField,
    ArithmeticThetaPalomarNormalKato378.FiveNormalized R W G g ∧ FiveFrame R W d ∧ FiveInitial R W G g d

namespace Bridges
theorem hodge_eq : Hodge R W = ArithmeticThetaRelativeDiscriminantR0171.Hodge R W := rfl
theorem localPower_eq (n : ℕ) (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) :
    localPower R W n U a = ArithmeticThetaRelativeDiscriminantR0171.localPower R W n U a := rfl
theorem normalized_iff (g : (Curve R W).functionField) :
    ArithmeticThetaPalomarNormalKato378.FiveNormalized R W G g ↔
      ArithmeticThetaFiveNormalization374.FiveNormalized R W G g := Iff.rfl
theorem frame_iff (d : Γ(HodgePower R W 24, ⊤)) :
    FiveFrame R W d ↔ ArithmeticThetaFiveNormalization374.FiveFrame R W d := Iff.rfl
theorem initial_iff (g : (Curve R W).functionField) (d : Γ(HodgePower R W 24, ⊤)) :
    FiveInitial R W G g d ↔ ArithmeticThetaFiveNormalization374.FiveInitial R W G g d := Iff.rfl
theorem specification_iff (d : Γ(HodgePower R W 24, ⊤)) :
    FiveSpecification R W G d ↔ ArithmeticThetaFiveNormalization374.FiveSpecification R W G d := Iff.rfl
include hG
theorem specification_iff_localD (d : Γ(HodgePower R W 24, ⊤)) :
    FiveSpecification R W G d ↔
      d = ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.localD R W G hG :=
  ArithmeticThetaFiveNormalization374.fiveSpecification_iff_localD R W G hG d
end Bridges
include hG
theorem initialTensorExistsUnique :
    ∃! d : Γ(HodgePower R W 24, ⊤), FiveSpecification R W G d := by
  exact ArithmeticThetaFiveNormalization374.fiveSpecification_existsUnique R W G hG
end ArithmeticThetaPalomarNormalInitial381
namespace ArithmeticThetaPalomarDifferential365
open ArithmeticThetaLocalWeierstrassR0203
/-- Kernel of restriction to the actual closed subscheme. -/
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)

/-- Pull back the actual relative differential sheaf along the actual identity. -/
def hodge {R : Type u} [CommRing R] (E : Family (Base R)) : (Base R).Modules :=
  (Scheme.Modules.pullback E.zero).obj (kaehler E.p)
/-- This fixes the entire conormal derivative on every ideal section on every open. -/
def Normalized {R : Type u} [CommRing R] (E : Family (Base R))
    (e : cotangent E ≅ hodge E) : Prop :=
  ∀ (U : E.curve.Opens) (x : Γ(idealModule E.zero.ker, U)),
    e.hom.app (E.zero ⁻¹ᵁ U) (pullSection E.zero x) =
      pullSection E.zero (relativeD E.p U ((idealInclusion E.zero.ker).app U x))
namespace Bridges
open ArithmeticThetaSchemeHodgeR0205
theorem cotangent_eq {S : Scheme.{u}} (E : Family S) :
    cotangent E = Cotangent E := rfl
theorem kaehler_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R) :
    kaehler f = f.kaehler := rfl
theorem derivative_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
    (U : X.Opens) (a : Γ(X, U)) :
    relativeD f U a = ArithmeticThetaCompactifiedDifferentialR0145.relativeD f U a := rfl
theorem normalized_hom_eq {R : Type u} [CommRing R] (E : Family (Base R))
    (e : cotangent E ≅ hodge E) (he : Normalized E e) :
    e.hom = (show cotangent E ⟶ hodge E from affineDifferential E) := by
  apply Scheme.Modules.pullback_hom_ext E.zero
  intro U x
  exact (he U x).trans
    (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback
      E.p E.zero U x).symm
theorem normalized_iff_hom_eq {R : Type u} [CommRing R] (E : Family (Base R))
    (e : cotangent E ≅ hodge E) :
    Normalized E e ↔ e.hom = (show cotangent E ⟶ hodge E from affineDifferential E) := by
  constructor
  · exact normalized_hom_eq E e
  · intro he U x
    rw [he]
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback
      E.p E.zero U x
end Bridges

theorem normalizedConormalHodge :
    ∀ (R : Type u) [CommRing R] (E : Family (Base R)),
      ∃! e : cotangent E ≅ hodge E, Normalized E e := by
  intro R _ E
  letI := ArithmeticThetaSchemeHodgeR0205.AffineConormalHodgeNaturality.differential_isIso E
  let e : cotangent E ≅ hodge E := asIso (ArithmeticThetaSchemeHodgeR0205.affineDifferential E)
  refine ⟨e, ?_, ?_⟩
  · intro U x
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback
      E.p E.zero U x
  · intro e' he'
    apply Iso.ext
    exact Bridges.normalized_hom_eq E e' he'
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarWeierstrass373
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaPalomarDifferential365

theorem projectiveGeometry (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    IsProper (structureMap R W) ∧ SmoothOfRelativeDimension 1 (structureMap R W) ∧
      GeometricallyConnected (structureMap R W) := by
  refine ⟨WeierstrassProjModel.projModelStrCR_isProper W.toProjective,
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective, ?_⟩
  letI : GeometricallyIntegral (structureMap R W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  exact GeometricallyIrreducible.geometricallyConnected (structureMap R W)
/-- The exact original projective curve, structural map and scheme-valued group law. -/
def family (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : Family (ArithmeticThetaPalomarDifferential365.Base R) where
  curve := Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul
           mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel
           mul_natural := G.mul_natural, mul_comm := hG.2 }
  proper := (projectiveGeometry R W).1
  dimension := (projectiveGeometry R W).2.1
  connected := (projectiveGeometry R W).2.2

theorem family_zero (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : (family R W G hG).zero = origin R W := by
  change (G.one (𝟙 (ArithmeticThetaPalomarDifferential365.Base R))).val = origin R W
  simpa only [Category.id_comp] using hG.1 (𝟙 (ArithmeticThetaPalomarDifferential365.Base R))

def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
/-- The actual origin pullback of the actual sheafified relative differential. -/
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj (kaehler (structureMap R W))
def originComparison (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : hodge (family R W G hG) ≅ Hodge R W :=
  pullbackEqIso (family_zero R W G hG) (kaehler (structureMap R W))
/-- The origin comparison is fixed by the actual equality zero=origin. -/
def Normalized (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (e : cotangent (family R W G hG) ≅ Hodge R W) : Prop :=
  ArithmeticThetaPalomarDifferential365.Normalized (family R W G hG)
    (e ≪≫ (originComparison R W G hG).symm)
namespace Bridges

theorem family_eq (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    family R W G hG = ArithmeticThetaSchemeDiscriminantR0244.weierstrassFamily R W G hG := rfl

theorem hodge_eq (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    Hodge R W = ArithmeticThetaRelativeDiscriminantR0171.Hodge R W := rfl

theorem normalized_hom_original (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (e : cotangent (family R W G hG) ≅ Hodge R W) (he : Normalized R W G hG e) :
    e.hom = (show cotangent (family R W G hG) ⟶ Hodge R W from
      (ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG).hom) := by
  let t := originComparison R W G hG
  apply (cancel_mono t.inv).mp
  have h := ArithmeticThetaPalomarDifferential365.Bridges.normalized_hom_eq
    (family R W G hG) (e ≪≫ t.symm) he
  change e.hom ≫ t.inv = _ at h
  change e.hom ≫ t.inv =
    ((show cotangent (family R W G hG) ⟶ hodge (family R W G hG) from
      ArithmeticThetaSchemeHodgeR0205.affineDifferential (family R W G hG)) ≫ t.hom) ≫ t.inv
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
end Bridges

theorem canonicalWeierstrassHodge (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) :
    ∃! e : cotangent (family R W G hG) ≅ Hodge R W, Normalized R W G hG e := by
  let F := family R W G hG
  let t := originComparison R W G hG
  obtain ⟨e, he, hu⟩ := ArithmeticThetaPalomarDifferential365.normalizedConormalHodge R F
  refine ⟨e ≪≫ t, ?_, ?_⟩
  · change ArithmeticThetaPalomarDifferential365.Normalized F ((e ≪≫ t) ≪≫ t.symm)
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using he
  · intro e' he'
    have h := congrArg (fun z => z ≪≫ t) (hu (e' ≪≫ t.symm) he')
    simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using h
end ArithmeticThetaPalomarWeierstrass373
namespace ArithmeticThetaPalomarIdentity357
open ArithmeticThetaLocalWeierstrassR0203
/-- Actual ideal sheaf as kernel of restriction to its closed subscheme. -/
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
/-- Compatibility with the actual canonical structure-sheaf map, not an arbitrary scalar. -/
def Compatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (f : F.curve ⟶ E.curve)
    (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) : Prop :=
  i.hom ≫ idealInclusion F.zero.ker =
    (Scheme.Modules.pullback f).map (idealInclusion E.zero.ker) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
/-- The genuine identity conormal; no arbitrary line bundle is substituted. -/
def cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)

def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) :
    (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F :=
  ((Scheme.Modules.pullbackComp b E.zero).app (idealModule E.zero.ker) ≪≫
    pullbackEqIso hz.symm (idealModule E.zero.ker) ≪≫
    ((Scheme.Modules.pullbackComp F.zero f).app (idealModule E.zero.ker)).symm) ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) : Prop :=
  ∃ i, Compatible E F f i ∧ e = cotangentComparison E F b f hz i
/-- All pointed Cartesian base changes admit a unique inclusion-compatible ideal comparison. -/
theorem identityIdealBaseChange :
    ∀ (S T : Scheme.{u}) (E : Family S) (F : Family T)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve),
      IsPullback f F.p E.p b → F.zero ≫ f = b ≫ E.zero →
      ∃! i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker,
        Compatible E F f i := by
  intro S T E F b f hc hz
  exact ArithmeticThetaSchemeHodgeR0205.cartesian_identity_ideal S T E F b f hc hz

theorem cotangentBaseChange :
    ∀ (S T : Scheme.{u}) (E : Family S) (F : Family T)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve),
      IsPullback f F.p E.p b → ∀ hz : F.zero ≫ f = b ≫ E.zero,
      ∃! e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F,
        CotangentCompatible E F b f hz e := by
  intro S T E F b f hc hz
  obtain ⟨i, hi, hu⟩ := identityIdealBaseChange S T E F b f hc hz
  refine ⟨cotangentComparison E F b f hz i, ⟨i, hi, rfl⟩, ?_⟩
  intro e he
  obtain ⟨j, hj, rfl⟩ := he
  rw [hu j hj]

end ArithmeticThetaPalomarIdentity357
namespace ArithmeticThetaPalomarCanonicalTensor382
open ArithmeticThetaTensorPower
/-- The genuine pullback adjunction on local sections. -/
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens}
    (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
/-- On every open and every local section, with the specified line isomorphism. -/
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Y.Modules) (K : X.Modules)
    (e : (Scheme.Modules.pullback f).obj H ≅ K) (n : ℕ)
    (q : (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X K n) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorPowerSection Y H n U s)) =
      tensorPowerSection X K n (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s))
theorem canonicalTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Y.Modules) (K : X.Modules) (hH : Scheme.Modules.IsInvertible H)
    (e : (Scheme.Modules.pullback f).obj H ≅ K) (n : ℕ) :
    ∃! q : (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X K n,
      Compatible f H K e n q := by
  let q := ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison f H K e n
  refine ⟨q, ?_, ?_⟩
  · intro U s
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section f H K e n U s
  · intro q' hq'
    apply Iso.ext
    apply ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.hom_ext_frames
    intro x
    obtain ⟨U, s, hx, hs⟩ := hH.exists_isFrameOn (f x)
    have hs' : ArithmeticThetaRelativeDiscriminantR0171.IsFrame H U s := fun V hV => hs hV hV
    refine ⟨f ⁻¹ᵁ U, pullSection f (tensorPowerSection Y H n U s), hx, ?_, ?_⟩
    · exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame f _ _
        (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorPower_frame H s hs' n)
    · exact (hq' U s).trans
        (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section f H K e n U s).symm
theorem compatible_iff_original {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Y.Modules) (K : X.Modules) (hH : Scheme.Modules.IsInvertible H)
    (e : (Scheme.Modules.pullback f).obj H ≅ K) (n : ℕ)
    (q : (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X K n) :
    Compatible f H K e n q ↔
      q = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison f H K e n := by
  constructor
  · intro hq
    exact (canonicalTensorComparison f H K hH e n).unique hq
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section f H K e n)
  · intro hq
    subst q
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section f H K e n
#print axioms canonicalTensorComparison
#print axioms compatible_iff_original
end ArithmeticThetaPalomarCanonicalTensor382
namespace ArithmeticThetaPalomarSchemePower383
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaTensorPower
abbrev Cotangent := @ArithmeticThetaPalomarIdentity357.cotangent
/-- Canonical comparison fixed by the actual ideal inclusion and all local tensor powers. -/
def Compatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero)
    (q : (Scheme.Modules.pullback b).obj (tensorPower S (Cotangent E) 24) ≅
      tensorPower T (Cotangent F) 24) : Prop :=
  ∃ e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F,
    ArithmeticThetaPalomarIdentity357.CotangentCompatible E F b f hz e ∧
      ArithmeticThetaPalomarCanonicalTensor382.Compatible b (Cotangent E) (Cotangent F) e 24 q
theorem canonicalSchemePower (S T : Scheme.{u}) (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hc : IsPullback f F.p E.p b)
    (hz : F.zero ≫ f = b ≫ E.zero) :
    ∃! q : (Scheme.Modules.pullback b).obj (tensorPower S (Cotangent E) 24) ≅
      tensorPower T (Cotangent F) 24, Compatible E F b f hz q := by
  let C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b := ⟨f, hc, hz⟩
  let q := ArithmeticThetaSchemeDiscriminantR0244.powerIso C
  have hE := ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.cotangent_invertible E
  have he : ArithmeticThetaPalomarIdentity357.CotangentCompatible E F b f hz
      (ArithmeticThetaSchemeDiscriminantR0244.cotangentIso C) :=
    ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.cotangentIso_compatible C
  refine ⟨q, ⟨ArithmeticThetaSchemeDiscriminantR0244.cotangentIso C, he, ?_⟩, ?_⟩
  · exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section
      b (Cotangent E) (Cotangent F) (ArithmeticThetaSchemeDiscriminantR0244.cotangentIso C) 24
  · rintro q' ⟨e', he', hq'⟩
    have eqe := (ArithmeticThetaPalomarIdentity357.cotangentBaseChange S T E F b f hc hz).unique he' he
    have eqp := (ArithmeticThetaPalomarCanonicalTensor382.compatible_iff_original
      b (Cotangent E) (Cotangent F) hE e' 24 q').mp hq'
    rw [eqe] at eqp
    exact eqp
theorem compatible_iff_original {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b)
    (q : (Scheme.Modules.pullback b).obj (tensorPower S (Cotangent E) 24) ≅
      tensorPower T (Cotangent F) 24) :
    Compatible E F b C.map C.pointed q ↔ q = ArithmeticThetaSchemeDiscriminantR0244.powerIso C := by
  have he : Compatible E F b C.map C.pointed (ArithmeticThetaSchemeDiscriminantR0244.powerIso C) := by
    refine ⟨ArithmeticThetaSchemeDiscriminantR0244.cotangentIso C,
      ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.cotangentIso_compatible C, ?_⟩
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section
      b (Cotangent E) (Cotangent F) (ArithmeticThetaSchemeDiscriminantR0244.cotangentIso C) 24
  constructor
  · intro hq
    exact (canonicalSchemePower S T E F b C.map C.cartesian C.pointed).unique hq he
  · intro hq
    simpa only [hq] using he
#print axioms canonicalSchemePower
#print axioms compatible_iff_original
end ArithmeticThetaPalomarSchemePower383
section PointedProvider
open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
namespace ArithmeticThetaPointedComparison387

theorem kaehler_hom_ext {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) {N : Y.Modules}
    {f g : gY.kaehler ⟶ N}
    (h : ∀ (U : Y.Opens) (a : Γ(Y,U)),
      f.app U (relativeD gY U a) = g.app U (relativeD gY U a)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv gY.kaehlerPresheaf N).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  letI := gY.sectionsAlgebra U.unop
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A Γ(Y,U.unop))
  intro a
  exact h U.unop a

section Pointed
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hc : CategoryTheory.IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 gY]
    (s : Spec (CommRingCat.of A) ⟶ Y) (t : Spec (CommRingCat.of B) ⟶ X)
    (hpt : t ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s)

def PointedCompatible
    (e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
        (Scheme.Modules.pullback t).obj gX.kaehler) : Prop :=
  ∀ (U : Y.Opens) (a : Γ(Y, U)) (V : (Spec (CommRingCat.of B)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ (s ⁻¹ᵁ U))
    (h₂ : V ≤ t ⁻¹ᵁ (φ ⁻¹ᵁ U)),
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₁
      (e.hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (Scheme.Modules.pullbackLocalSection s (relativeD gY U a)))) =
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection t
        (relativeD gX (φ ⁻¹ᵁ U) (φ.app U a)))

theorem pointed_compatible_iff
    (e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
        (Scheme.Modules.pullback t).obj gX.kaehler) :
    PointedCompatible gY gX φ s t e ↔ e = pointedDifferentialIso gY gX φ hc s t hpt := by
  constructor
  · intro he
    apply Iso.ext
    apply ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).homEquiv _ _).injective
    apply ((Scheme.Modules.pullbackPushforwardAdjunction s).homEquiv _ _).injective
    apply kaehler_hom_ext gY
    intro U a
    have h₂ : (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ (s ⁻¹ᵁ U) ≤
        t ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
      change (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s) ⁻¹ᵁ U ≤ (t ≫ φ) ⁻¹ᵁ U
      rw [hpt]
    have h := (he U a _ le_rfl h₂).trans
      (pointedDifferentialIso_D gY gX φ hc s t hpt U a _ le_rfl h₂).symm
    rw [← Scheme.Modules.app_pullbackLocalSection s,
      ← Scheme.Modules.app_pullbackLocalSection s,
      ← Scheme.Modules.app_pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap A B))),
      ← Scheme.Modules.app_pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    simpa [res] using h
  · rintro rfl
    exact pointedDifferentialIso_D gY gX φ hc s t hpt

include hc hpt in
theorem pointed_comparison_exists_unique :
    ∃! e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
        (Scheme.Modules.pullback t).obj gX.kaehler,
      PointedCompatible gY gX φ s t e := by
  refine ⟨pointedDifferentialIso gY gX φ hc s t hpt, ?_, ?_⟩
  · exact (pointed_compatible_iff gY gX φ hc s t hpt _).mpr rfl
  · intro e he
    exact (pointed_compatible_iff gY gX φ hc s t hpt e).mp he
end Pointed
#print axioms kaehler_hom_ext
#print axioms pointed_compatible_iff
#print axioms pointed_comparison_exists_unique
end ArithmeticThetaPointedComparison387
end PointedProvider
namespace ArithmeticThetaPalomarFullScheme385
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaTensorPower ArithmeticThetaPalomarNormalInitial381
abbrev Cotangent := @ArithmeticThetaPalomarIdentity357.cotangent
abbrev Power {S : Scheme.{u}} (E : Family S) := tensorPower S (Cotangent E) 24
abbrev Sections {S : Scheme.{u}} (E : Family S) := Γ(Power E, ⊤)
def res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(M,U)) := M.presheaf.map (homOfLE h).op s
abbrev WFamily := @ArithmeticThetaPalomarWeierstrass373.family
/-- The full normalized conormal derivative and all actual local tensor powers. -/
def WPowerCompatible (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (q : Power (WFamily R W G hG) ≅ HodgePower R W 24) : Prop :=
  ∃ e : Cotangent (WFamily R W G hG) ≅ Hodge R W,
    ArithmeticThetaPalomarWeierstrass373.Normalized R W G hG e ∧
    ∀ (U : (ArithmeticThetaPalomarNormalInitial381.Base R).Opens)
      (s : Γ(Cotangent (WFamily R W G hG),U)),
      q.hom.app U (tensorPowerSection _ _ 24 U s) =
        tensorPowerSection _ _ 24 U (e.hom.app U s)
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange in
theorem wPower_iff_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (q : Power (WFamily R W G hG) ≅ HodgePower R W 24) :
    WPowerCompatible R W G hG q ↔ q = powerCongr _
      (ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG) 24 := by
  let e₀ := ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG
  have he₀ : ArithmeticThetaPalomarWeierstrass373.Normalized R W G hG e₀ := by
    obtain ⟨e, he, _⟩ := ArithmeticThetaPalomarWeierstrass373.canonicalWeierstrassHodge R W G hG
    have h : e = e₀ := Iso.ext (ArithmeticThetaPalomarWeierstrass373.Bridges.normalized_hom_original R W G hG e he)
    exact h ▸ he
  constructor
  · rintro ⟨e, he, hq⟩
    have heq : e = e₀ := Iso.ext (ArithmeticThetaPalomarWeierstrass373.Bridges.normalized_hom_original R W G hG e he)
    subst e
    apply Iso.ext
    apply hom_ext_frames
    intro x
    have hE := ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.cotangent_invertible
      (WFamily R W G hG)
    obtain ⟨U, s, hx, hs⟩ := hE.exists_isFrameOn x
    have hs' : ArithmeticThetaRelativeDiscriminantR0171.IsFrame (Cotangent (WFamily R W G hG)) U s :=
      fun V hV => hs hV hV
    exact ⟨U, tensorPowerSection _ _ 24 U s, hx, tensorPower_frame _ s hs' 24,
      (hq U s).trans (powerCongr_section _ e₀ 24 U s).symm⟩
  · intro hq
    subst q
    exact ⟨e₀, he₀, powerCongr_section _ e₀ 24⟩

theorem canonicalWPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    ∃! q : Power (WFamily R W G hG) ≅ HodgePower R W 24, WPowerCompatible R W G hG q := by
  refine ⟨ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.powerCongr _
    (ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG) 24,
    (wPower_iff_original R W G hG _).mpr rfl, ?_⟩
  intro q hq
  exact (wPower_iff_original R W G hG q).mp hq
abbrev AffineComparison := @ArithmeticThetaArbitraryDiscriminantR0243.Comparison
/-- All regular functions and all common subopens fix the actual pointed differential map. -/
def AffineLineCompatible {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι)
    (e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (Hodge R W) ≅ Hodge S V) : Prop :=
  ∀ (U : (Curve R W).Opens) (a : Γ(Curve R W,U))
    (Z : (ArithmeticThetaPalomarNormalInitial381.Base S).Opens)
    (h₁ : Z ≤ (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U))
    (h₂ : Z ≤ (origin S V) ⁻¹ᵁ (C.map ⁻¹ᵁ U)),
    res (Hodge S V) h₁ (e.hom.app _ (ArithmeticThetaPalomarDifferential365.pullSection
      (Spec.map (CommRingCat.ofHom ι)) (localDifferential R W U a))) =
    res (Hodge S V) h₂ (localDifferential S V (C.map ⁻¹ᵁ U) (C.map.app U a))
def AffinePowerCompatible {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι)
    (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24) : Prop :=
  ∃ e, AffineLineCompatible C e ∧ ArithmeticThetaPalomarCanonicalTensor382.Compatible
    (Spec.map (CommRingCat.ofHom ι)) (Hodge R W) (Hodge S V) e 24 q
theorem affineLine_iff_original {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι)
    (e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (Hodge R W) ≅ Hodge S V) :
    AffineLineCompatible C e ↔ e = ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (ArithmeticThetaPalomarWeierstrass373.projectiveGeometry R W).2.1
  exact ArithmeticThetaPointedComparison387.pointed_compatible_iff
    (structureMap R W) (structureMap S V) C.map C.cartesian (origin R W) (origin S V) C.pointed e
theorem affinePower_iff_original {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι)
    (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24) :
    AffinePowerCompatible C q ↔ q = ArithmeticThetaArbitraryDiscriminantR0243.comparisonPower C := by
  have hH : Scheme.Modules.IsInvertible (Hodge R W) := by
    letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
      (ArithmeticThetaPalomarWeierstrass373.projectiveGeometry R W).2.1
    exact ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap R W).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1).pullback (origin R W)
  constructor
  · rintro ⟨e, he, hq⟩
    rw [(affineLine_iff_original C e).mp he] at hq
    exact (ArithmeticThetaPalomarCanonicalTensor382.compatible_iff_original _ _ _ hH _ 24 q).mp hq
  · intro hq
    subst q
    exact ⟨ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C,
      (affineLine_iff_original C _).mpr rfl,
      ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison_section _ _ _ _ 24⟩

theorem canonicalAffinePower {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι) :
    ∃! q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24,
      AffinePowerCompatible C q := by
  refine ⟨ArithmeticThetaArbitraryDiscriminantR0243.comparisonPower C,
    (affinePower_iff_original C _).mpr rfl, ?_⟩
  intro q hq
  exact (affinePower_iff_original C q).mp hq
def affinePower {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24 :=
  (canonicalAffinePower C).exists.choose
def affinePull {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι) (d : Γ(HodgePower R W 24,⊤)) : Γ(HodgePower S V 24,⊤) :=
  res _ (by simp) ((affinePower C).hom.app _
    (ArithmeticThetaPalomarDifferential365.pullSection (Spec.map (CommRingCat.ofHom ι)) d))
/-- Every actual normal source, with the whole nonvacuous initial specification. -/
def AffineSpecification {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (d : Γ(HodgePower R W 24,⊤)) : Prop :=
  ∀ M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W,
    ∀ d₀ : Γ(HodgePower M.ring M.equation 24,⊤),
      FiveSpecification M.ring M.equation M.law d₀ → d = affinePull M.comparison d₀
theorem affinePull_eq_original {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S}
    (C : AffineComparison R S W V ι) (d : Γ(HodgePower R W 24,⊤)) :
    affinePull C d = ArithmeticThetaArbitraryDiscriminantR0243.pull C d := by
  have hq := (affinePower_iff_original C _).mp (canonicalAffinePower C).exists.choose_spec
  unfold affinePull affinePower
  rw [hq]
  rfl

theorem affine_iff_original {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (d : Γ(HodgePower R W 24,⊤)) :
    AffineSpecification W d ↔ ArithmeticThetaArbitraryDiscriminantR0243.IsD2 W d := by
  constructor
  · intro h M
    have ha := h M (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.localD
      M.ring M.equation M.law M.originLaw)
      ((ArithmeticThetaPalomarNormalInitial381.Bridges.specification_iff_localD
        M.ring M.equation M.law M.originLaw _).mpr rfl)
    simpa only [affinePull_eq_original, ArithmeticThetaArbitraryDiscriminantR0243.value] using ha
  · intro h M d₀ hd₀
    rw [(ArithmeticThetaPalomarNormalInitial381.Bridges.specification_iff_localD
      M.ring M.equation M.law M.originLaw d₀).mp hd₀, affinePull_eq_original]
    exact h M

theorem normal_test_exists (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W,
      ∃! d₀ : Γ(HodgePower M.ring M.equation 24,⊤), FiveSpecification M.ring M.equation M.law d₀ := by
  obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model R W
  exact ⟨M, ArithmeticThetaPalomarNormalInitial381.initialTensorExistsUnique M.ring M.equation M.law M.originLaw⟩
/-- Canonical value uses the uniquely normalized actual power map, whose existence is proved. -/
def wPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : Power (WFamily R W G hG) ≅ HodgePower R W 24 :=
  (canonicalWPower R W G hG).exists.choose
def wValue (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (d : Sections (WFamily R W G hG)) :=
  (wPower R W G hG).hom.app ⊤ d
abbrev Comparison := @ArithmeticThetaSchemeDiscriminantR0244.Comparison
def schemePower {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) : (Scheme.Modules.pullback b).obj (Power E) ≅ Power F :=
  (ArithmeticThetaPalomarSchemePower383.canonicalSchemePower S T E F b C.map C.cartesian C.pointed).exists.choose
def pull {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) (d : Sections E) : Sections F :=
  res (Power F) (by simp)
    ((schemePower C).hom.app _ (ArithmeticThetaPalomarDifferential365.pullSection b d))
/-- Every original affine Weierstrass test, over arbitrary coefficient algebras. -/
def SchemeSpecification (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) (d : Sections E) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (b : ArithmeticThetaPalomarNormalInitial381.Base R ⟶ S),
    b ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    ∀ C : Comparison E (WFamily R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      AffineSpecification W (wValue R W G hG (pull C d))
theorem wPower_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : wPower R W G hG =
      ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.powerCongr _
        (ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG) 24 :=
  (wPower_iff_original R W G hG _).mp (canonicalWPower R W G hG).exists.choose_spec

theorem wValue_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (d : Sections (WFamily R W G hG)) :
    wValue R W G hG d = ArithmeticThetaSchemeDiscriminantR0244.weierstrassValue R W G hG d := by
  unfold wValue
  rw [wPower_eq_original]
  rfl

theorem schemePower_eq_original {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) : schemePower C = ArithmeticThetaSchemeDiscriminantR0244.powerIso C :=
  (ArithmeticThetaPalomarSchemePower383.compatible_iff_original E F b C _).mp
    (ArithmeticThetaPalomarSchemePower383.canonicalSchemePower S T E F b C.map C.cartesian C.pointed).exists.choose_spec

theorem pull_eq_original {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) (d : Sections E) :
    pull C d = ArithmeticThetaSchemeDiscriminantR0244.pull C d := by
  unfold pull
  rw [schemePower_eq_original]
  rfl

theorem scheme_iff_original (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) (d : Sections E) :
    SchemeSpecification k σ E d ↔ ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d := by
  constructor
  · intro h R _ _ W _ G hG b hb C
    letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
    have ha := (affine_iff_original W _).mp (h R W G hG b hb C)
    simpa only [wValue_eq_original, pull_eq_original] using ha
  · intro h R _ _ W _ G hG b hb C
    letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
    apply (affine_iff_original W _).mpr
    simpa only [wValue_eq_original, pull_eq_original] using h R W G hG b hb C

theorem scheme_exists (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) :
    ∃ d : Sections E, SchemeSpecification k σ E d := by
  obtain ⟨d, hd⟩ := ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_existence k S σ E
  exact ⟨d, (scheme_iff_original k σ E d).mpr hd⟩

theorem scheme_naturality (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S)
    (T : Scheme.{u}) (τ : T ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (F : Family T)
    (b : T ⟶ S) (hb : b ≫ σ = τ) (C : Comparison E F b)
    (d : Sections E) (e : Sections F)
    (hd : SchemeSpecification k σ E d) (he : SchemeSpecification k τ F e) : pull C d = e := by
  rw [pull_eq_original]
  exact ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality k S σ E T τ F b hb C d e
    ((scheme_iff_original k σ E d).mp hd) ((scheme_iff_original k τ F e).mp he)

theorem recover_original_080 (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) :
    ∃ d : ArithmeticThetaSchemeDiscriminantR0244.Sections E,
      ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d := by
  obtain ⟨d, hd⟩ := scheme_exists k S σ E
  exact ⟨d, (scheme_iff_original k σ E d).mp hd⟩

theorem recover_original_081 (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S)
    (T : Scheme.{u}) (τ : T ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (F : Family T)
    (b : T ⟶ S) (hb : b ≫ σ = τ) (C : Comparison E F b)
    (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F)
    (hd : ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d)
    (he : ArithmeticThetaSchemeDiscriminantR0244.IsD2 k τ F e) :
    ArithmeticThetaSchemeDiscriminantR0244.pull C d = e := by
  rw [← pull_eq_original]
  exact scheme_naturality k S σ E T τ F b hb C d e
    ((scheme_iff_original k σ E d).mpr hd) ((scheme_iff_original k τ F e).mpr he)
end ArithmeticThetaPalomarFullScheme385
