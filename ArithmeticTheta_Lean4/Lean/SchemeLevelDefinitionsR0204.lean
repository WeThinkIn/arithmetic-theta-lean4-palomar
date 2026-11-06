import SchemeLocalWeierstrassR0203
import ArbitraryAffineClassificationR0202

/-! Full markings and classifying maps for general elliptic families.
These definitions contain no local equation or assumed classification of a family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}}
    (t : T ⟶ S) : ℕ → SchemeHomOver t E.p → SchemeHomOver t E.p
  | 0, _ => E.law.one t
  | n + 1, x => E.law.mul t (multiple E t n x) x

/-- A full ordered marking, tested on the actual identity subscheme. -/
structure FullLevel {S : Scheme.{u}} (E : Family S) (L : ℕ) where
  x : SchemeHomOver (𝟙 S) E.p
  y : SchemeHomOver (𝟙 S) E.p
  killed_x : multiple E (𝟙 S) L x = E.law.one (𝟙 S)
  killed_y : multiple E (𝟙 S) L y = E.law.one (𝟙 S)
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (E.law.mul (𝟙 S)
      (multiple E (𝟙 S) i.val x) (multiple E (𝟙 S) j.val y)).val)
      (Set.range E.zero)

/-- Compatibility with multiplication on every actual scheme-valued point. -/
def Multiplicative {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) : Prop :=
  ∀ (U : Scheme.{u}) (t : U ⟶ T)
    (x y : SchemeHomOver t F.p) (x' y' : SchemeHomOver (t ≫ b) E.p),
    x'.val = x.val ≫ f → y'.val = y.val ≫ f →
    (E.law.mul _ x' y').val = (F.law.mul t x y).val ≫ f

def MarkedCartesian {S T : Scheme.{u}} {L : ℕ} (E : Family S) (F : Family T)
    (M : FullLevel E L) (N : FullLevel F L) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) : Prop :=
  IsPullback f F.p E.p b ∧ F.zero ≫ f = b ≫ E.zero ∧
  Multiplicative E F b f ∧ N.x.val ≫ f = b ≫ M.x.val ∧
  N.y.val ≫ f = b ≫ M.y.val

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)

/-- Group preservation for a comparison with the same accepted universal family. -/
def UniversalMultiplicative {S : Scheme.{u}} (E : Family S)
    (b : S ⟶ Base A.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ S)
    (x y : SchemeHomOver t E.p)
    (x' y' : SchemeHomOver (t ≫ b) A.descent.family.projection),
    x'.val = x.val ≫ f → y'.val = y.val ≫ f →
    (A.descent.family.law.mul _ x' y').val = (E.law.mul t x y).val ≫ f

/-- The global comparison fixes the k-map, Cartesian square, origin, labels,
and actual group operation; no classifying map is supplied in the input family. -/
def Classifies (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
    (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
    (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L)
    (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) : Prop :=
  b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = σ ∧
  IsPullback f E.p A.descent.family.projection (b ≫ Q.inclusion) ∧
  E.zero ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val ∧
  M.x.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.x.val ∧
  M.y.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.y.val ∧
  UniversalMultiplicative k L A E (b ≫ Q.inclusion) f

/-- Actual affine local classifying data, with the lifted original full marking. -/
structure LocalClassifier (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
    (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
    (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L) where
  presentation : LocalPresentation k S σ E
  level : ArithmeticThetaFullLevelCoverR0175.FullLevel presentation.ring
    presentation.equation presentation.law L (𝟙 (Base presentation.ring))
  x_eq : level.x.val ≫ presentation.comparison = presentation.base ≫ M.x.val
  y_eq : level.y.val ≫ presentation.comparison = presentation.base ≫ M.y.val
  base : Base presentation.ring ⟶ Base Q.quotient.ring
  comparison : ArithmeticThetaRelativeKatoR0169.Curve presentation.ring
    presentation.equation ⟶ A.descent.family.curve
  classifies : ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q
    presentation.ring presentation.equation presentation.law level base comparison

/-- Every general marked family has unique classifying maps; conversely every
base map has an actual marked pullback family. Comparison commutes with arbitrary
base changes, including nonflat maps and nonreduced or empty test schemes. -/
def Universal (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
    (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
    (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) : Prop :=
  (∀ (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L),
    ∃! b : S ⟶ Base Q.quotient.ring,
      ∃! f : E.curve ⟶ A.descent.family.curve, Classifies k L A B C Q σ E M b f) ∧
  (∀ (S : Scheme.{u}) (σ : S ⟶ Base k) (b : S ⟶ Base Q.quotient.ring),
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = σ →
    ∃ (E : Family S) (M : FullLevel E L) (f : E.curve ⟶ A.descent.family.curve),
      Classifies k L A B C Q σ E M b f) ∧
  (∀ (S T : Scheme.{u}) (σ : S ⟶ Base k) (τ : T ⟶ Base k)
    (E : Family S) (F : Family T) (M : FullLevel E L) (N : FullLevel F L)
    (a : T ⟶ S) (g : F.curve ⟶ E.curve), a ≫ σ = τ →
    MarkedCartesian E F M N a g →
    ∀ (b : S ⟶ Base Q.quotient.ring) (c : T ⟶ Base Q.quotient.ring)
      (f : E.curve ⟶ A.descent.family.curve) (h : F.curve ⟶ A.descent.family.curve),
      Classifies k L A B C Q σ E M b f → Classifies k L A B C Q τ F N c h →
      c = a ≫ b ∧ h = g ≫ f)

end ArithmeticThetaSchemeLevelR0204
