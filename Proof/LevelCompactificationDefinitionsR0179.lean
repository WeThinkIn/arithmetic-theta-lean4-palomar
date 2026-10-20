module

public import NormalAffineClassifyingConstructionR0178
public import CyclicQuotientUniversalFactorizationR0173

@[expose] public section

/-! Smooth projective completions of the actual compatible level base.
The compactification and level-reduction maps are outputs of new obligations.
No generalized elliptic boundary model or Tate parameter is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLevelCompactificationR0179
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178

/-- Precisely the already constructed compatible marked atlas and quotient. -/
structure LevelData (k : Type u) [Field k] (L : ℕ) where
  atlas : LegendreAtlas k L
  two : TwoMarking k L atlas
  canonical : CanonicalTwo k L atlas two
  cover : CompatibleCover k L atlas two
  quotient : CompatibleQuotient k L atlas two cover

variable (k : Type u) [Field k] (L : ℕ)

abbrev OpenBase (D : LevelData k L) := Base D.quotient.quotient.ring

def openStructure (D : LevelData k L) : OpenBase k L D ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k D.quotient.quotient.ring))

/-- The descended Legendre parameter must pull back to the SAME level projection. -/
def IsParameter (D : LevelData k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) : Prop :=
  D.quotient.quotient.q ≫ p = D.cover.inclusion ≫ D.atlas.level.projection ∧
  p ≫ legendreBaseMap k = openStructure k L D

/-- A projective smooth compactification of the actual affine base. Density
rules out arbitrary extra proper components. The closed immersion witnesses
projectivity, not only properness. Geometric connectedness is not assumed. -/
structure Compactification (D : LevelData k L) where
  space : Scheme.{u}
  projection : space ⟶ Base k
  inclusion : OpenBase k L D ⟶ space
  over_eq : inclusion ≫ projection = openStructure k L D
  openImmersion : IsOpenImmersion inclusion
  dense : DenseRange inclusion.base
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  dimension : ℕ
  embedding : space ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)
  closedImmersion : IsClosedImmersion embedding
  embedding_over : embedding ≫
    ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = projection

def boundary (D : LevelData k L) (X : Compactification k L D) : Set X.space :=
  (Set.range X.inclusion.base)ᶜ

/-- Both the field and module structures use the actual geometric base map. -/
def FiniteResidue (D : LevelData k L) (X : Compactification k L D) (x : X.space) : Prop :=
  letI : Algebra k (X.space.residueField x) :=
    (ArithmeticThetaCurveDegree.baseToResidue k X.projection x).toAlgebra
  letI : Module k (X.space.residueField x) :=
    @Algebra.toModule k (X.space.residueField x) _ _
      (ArithmeticThetaCurveDegree.baseToResidue k X.projection x).toAlgebra
  FiniteDimensional k (X.space.residueField x)

/-- Identify a map by actual classifying comparisons and BOTH reduced marking
sections. Tests are the full normal affine domain covered by the accepted
classifying theorem. No pointwise or arbitrary-coordinate replacement. -/
def RespectsReduction [CharZero k] {d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (f : OpenBase k L D ⟶ OpenBase k d E) : Prop :=
  f ≫ openStructure k d E = openStructure k L D ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (N : FullLevel R W G d (𝟙 (Base R)))
    (hx : N.x = G.nsmul (𝟙 (Base R)) (L / d) M.x)
    (hy : N.y = G.nsmul (𝟙 (Base R)) (L / d) M.y)
    (b : Base R ⟶ OpenBase k L D) (b' : Base R ⟶ OpenBase k d E)
    (a : Curve R W ⟶ D.atlas.descent.family.curve)
    (a' : Curve R W ⟶ E.atlas.descent.family.curve),
    Classifies k L D.atlas D.two D.cover D.quotient R W G M b a →
    Classifies k d E.atlas E.two E.cover E.quotient R W G N b' a' →
    b ≫ f = b'

def IsReduction [CharZero k] {d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (f : OpenBase k L D ⟶ OpenBase k d E) : Prop :=
  RespectsReduction k L D E f ∧ IsFinite f ∧ Etale f ∧ Surjective f ∧
    ∀ y, f.finrank y = levelDegree L / levelDegree d

/-- Extension of the actual reduction, including the Cartesian open square:
no extra boundary point may lie over the target interior. -/
def ExtendsReduction {d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (X : Compactification k L D) (Y : Compactification k d E)
    (f : OpenBase k L D ⟶ OpenBase k d E) (F : X.space ⟶ Y.space) : Prop :=
  F ≫ Y.projection = X.projection ∧
  X.inclusion ≫ F = f ≫ Y.inclusion ∧
  IsPullback X.inclusion f F Y.inclusion ∧
  IsFinite F ∧ Flat F ∧ Surjective F ∧
  ∀ y, F.finrank y = levelDegree L / levelDegree d

end ArithmeticThetaLevelCompactificationR0179
