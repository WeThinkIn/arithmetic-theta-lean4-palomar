module

public import SchemeFullLevelUniversalR0204
public import GlobalSchemeClassifierR0204

@[expose] public section

/-! The identity cotangent on general test schemes and its specified comparison
with the accepted affine Hodge sheaf. Only ordinary definitions occur here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The actual conormal I/I² at the identity, expressed as e*I. -/
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj E.zero.ker.module

/-- Compatibility with the inclusion of the actual identity ideal in O. -/
def IdealCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (f : F.curve ⟶ E.curve)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) : Prop :=
  i.hom ≫ F.zero.ker.moduleι =
    (Scheme.Modules.pullback f).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom

/-- The comparison is induced by the actual ideal comparison and pointed square. -/
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) :
    (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F :=
  squarePullbackIso b E.zero F.zero f hz.symm E.zero.ker.module ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i

/-- Canonical cotangent comparison: the witnessing ideal isomorphism preserves
its actual ideal inclusion; no arbitrary line is chosen. -/
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F) : Prop :=
  ∃ i, IdealCompatible E F f i ∧ e = cotangentComparison E F b f hz i

/-- On an affine base use the accepted canonical derivative, including its
normalization on every ideal section. -/
abbrev affineDifferential {R : Type u} [CommRing R] (E : Family (Base R)) :
    Cotangent E ⟶ (Scheme.Modules.pullback E.zero).obj E.p.kaehler :=
  ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap E.p E.zero

/-- Reuse the canonical affine differential base-change isomorphism verbatim. -/
def affineHodgeComparison {R V : Type u} [CommRing R] [CommRing V]
    (E : Family (Base R)) (F : Family (Base V)) (ι : R →+* V)
    (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p (Spec.map (CommRingCat.ofHom ι)))
    (hz : F.zero ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ E.zero) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj
      ((Scheme.Modules.pullback E.zero).obj E.p.kaehler) ≅
        (Scheme.Modules.pullback F.zero).obj F.p.kaehler := by
  letI : Algebra R V := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 E.p := E.dimension
  exact pointedDifferentialIso E.p F.p f hc E.zero F.zero hz

/-- Identity and composition are equalities of actual sheaf maps. -/
def CotangentCoherence : Prop :=
  (∀ (S : Scheme.{u}) (E : Family S)
    (hz : E.zero ≫ 𝟙 E.curve = 𝟙 S ≫ E.zero)
    (e : (Scheme.Modules.pullback (𝟙 S)).obj (Cotangent E) ≅ Cotangent E),
    CotangentCompatible E E (𝟙 S) (𝟙 E.curve) hz e →
      e.hom = (Scheme.Modules.pullbackId S).hom.app (Cotangent E)) ∧
  (∀ (S T U : Scheme.{u}) (E : Family S) (F : Family T) (G : Family U)
    (b : T ⟶ S) (a : U ⟶ T) (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve)
    (hf : F.zero ≫ f = b ≫ E.zero) (hg : G.zero ≫ g = a ≫ F.zero)
    (hgf : G.zero ≫ (g ≫ f) = (a ≫ b) ≫ E.zero)
    (ef : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (eg : (Scheme.Modules.pullback a).obj (Cotangent F) ≅ Cotangent G)
    (egf : (Scheme.Modules.pullback (a ≫ b)).obj (Cotangent E) ≅ Cotangent G),
    CotangentCompatible E F b f hf ef → CotangentCompatible F G a g hg eg →
    CotangentCompatible E G (a ≫ b) (g ≫ f) hgf egf →
      (Scheme.Modules.pullback a).map ef.hom ≫ eg.hom =
        ((Scheme.Modules.pullbackComp a b).app (Cotangent E)).hom ≫ egf.hom)

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)

abbrev universalFamily := ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily L A

/-- Exactly the existing Hodge sheaf, restricted to the compatible quotient. -/
abbrev ModularHodge : (Base Q.quotient.ring).Modules :=
  (Scheme.Modules.pullback Q.inclusion).obj
    ((Scheme.Modules.pullback (universalFamily k L A).zero).obj
      (universalFamily k L A).p.kaehler)

/-- A classifier's Hodge isomorphism is normalized by the actual conormal
map of its universal family, rather than an unspecified scalar. -/
def ClassifierHodge {S : Scheme.{u}} (E : Family S)
    (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve)
    (e : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E) : Prop :=
  ∃ (hz : E.zero ≫ f = (b ≫ Q.inclusion) ≫ (universalFamily k L A).zero)
    (i : (Scheme.Modules.pullback f).obj (universalFamily k L A).zero.ker.module ≅ E.zero.ker.module),
    IdealCompatible (universalFamily k L A) E f i ∧
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pullback Q.inclusion).map (affineDifferential (universalFamily k L A))) ≫
        e.hom =
      ((Scheme.Modules.pullbackComp b Q.inclusion).app (Cotangent (universalFamily k L A))).hom ≫
        (cotangentComparison (universalFamily k L A) E (b ≫ Q.inclusion) f hz i).hom

/-- Naturality keeps the same actual family map and the entire sheaf morphism. -/
def ClassifierHodgeNatural : Prop :=
  ∀ (S T : Scheme.{u}) (E : Family S) (F : Family T)
    (a : T ⟶ S) (g : F.curve ⟶ E.curve) (hg : F.zero ≫ g = a ≫ E.zero)
    (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve)
    (eE : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E)
    (eF : (Scheme.Modules.pullback (a ≫ b)).obj (ModularHodge k L A B C Q) ≅ Cotangent F)
    (eG : (Scheme.Modules.pullback a).obj (Cotangent E) ≅ Cotangent F),
    ClassifierHodge k L A B C Q E b f eE →
    ClassifierHodge k L A B C Q F (a ≫ b) (g ≫ f) eF →
    CotangentCompatible E F a g hg eG →
      (Scheme.Modules.pullback a).map eE.hom ≫ eG.hom =
        ((Scheme.Modules.pullbackComp a b).app (ModularHodge k L A B C Q)).hom ≫ eF.hom

/-- Constructed general-scheme classification with its canonical weight-one
cotangent identification and all-base-change naturality. -/
def HodgeUniversal : Prop :=
  Universal k L A B C Q ∧
  (∀ (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L)
    (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve),
    Classifies k L A B C Q σ E M b f →
    ∃! e : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E,
      ClassifierHodge k L A B C Q E b f e) ∧
  ClassifierHodgeNatural k L A B C Q

end ArithmeticThetaSchemeHodgeR0205
