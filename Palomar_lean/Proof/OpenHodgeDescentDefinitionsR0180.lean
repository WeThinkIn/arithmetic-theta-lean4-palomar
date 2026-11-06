module

public import LevelCompactificationDefinitionsR0179
public import SmoothProjectiveLevelCompletionR0179
public import CompactifiedLevelForgettingR0179
public import LegendreLevelAtlasDefinitionsR0176
public import RelativeHodgePowerBaseChangeR0171

@[expose] public section

/-! Actual elliptic-family charts, intrinsic sections and cyclic quotients on
full-level bases. All existence assertions are future obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaOpenHodgeR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower

abbrev zero {S : Type u} [CommRing S] (E : EllipticFamily S) : Base S ⟶ E.curve :=
  (E.law.one (𝟙 _)).val
abbrev hodge {S : Type u} [CommRing S] (E : EllipticFamily S) :=
  (Scheme.Modules.pullback (zero E)).obj E.projection.kaehler
abbrev power {S : Type u} [CommRing S] (E : EllipticFamily S) (n : ℕ) :=
  tensorPower (Base S) (hodge E) n

/-- A genuine pointed Cartesian Weierstrass comparison, including the actual
multiplication maps. No section or expansion equality is an input. -/
structure Test (S : Type u) [CommRing S] (E : EllipticFamily S)
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) where
  scalar : S →+* R
  map : Curve R W ⟶ E.curve
  cartesian : IsPullback map (structureMap R W) E.projection (baseMap S R scalar)
  origin_eq : origin R W ≫ map = baseMap S R scalar ≫ zero E
  nsmul_eq : ∀ n, G.schemeNsmul n ≫ map = map ≫ E.law.schemeNsmul n

/-- Constructed affine charts; the base can be disconnected. Each chart ring
is a genuine normal Noetherian rational domain. -/
structure Chart (S : Type u) [CommRing S] (E : EllipticFamily S) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  equation : WeierstrassCurve ring
  [elliptic : equation.IsElliptic]
  law : Law ring equation
  originLaw : IsOriginLaw ring equation law
  comparison : Test S E ring equation law
  openImmersion : IsOpenImmersion (baseMap S ring comparison.scalar)
attribute [instance] Chart.commRing Chart.domain Chart.noetherian Chart.normal
  Chart.rational Chart.elliptic

structure Atlas (S : Type u) [CommRing S] (E : EllipticFamily S) where
  count : ℕ
  chart : Fin count → Chart S E
  covers : ∀ x : Base S, ∃ i, x ∈ Set.range (baseMap S (chart i).ring (chart i).comparison.scalar)

/-- Reuse the accepted general pointed differential comparison. -/
def comparison {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) :
    (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (hodge E) ≅ Hodge R W := by
  letI : Algebra S R := C.scalar.toAlgebra
  letI : SmoothOfRelativeDimension 1 E.projection := E.smooth
  exact pointedDifferentialIso E.projection (structureMap R W) C.map
    C.cartesian (zero E) (origin R W) C.origin_eq

def powerComparison {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) :
    (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n :=
  tensorComparison (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n

def pullSection {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤)) : Γ(HodgePower R W n, ⊤) :=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))

/-- Intrinsic D2 is characterized against every actual Weierstrass test,
through the proved canonical differential map, using five times the normalized
five-Kato function. This is a construction predicate, not an assumed section. -/
def IsD2 {S : Type u} [CommRing S] (E : EllipticFamily S)
    (d : Γ(power E 24, ⊤)) : Prop :=
  IsFrame (power E 24) ⊤ d ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G →
    ∀ (C : Test S E R W G) (g : (Curve R W).functionField),
    Normalized R W G 5 g → RepresentsInitial R W G 5 g (pullSection C 24 d)

/-- A unit value is tested via the actual point, its Cartesian transport,
and the source's regular-unit evaluation predicate, including specializations. -/
def IsKatoValue {S : Type u} [CommRing S] (E : EllipticFamily S)
    (c : ℕ) (P : Base S ⟶ E.curve) (v : S) : Prop :=
  IsUnit v ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G →
    ∀ (C : Test S E R W G) (P' : Base R ⟶ Curve R W),
    P' ≫ structureMap R W = 𝟙 _ →
    P' ≫ C.map = baseMap S R C.scalar ≫ P →
    ∀ g : (Curve R W).functionField, Normalized R W G c g →
      HasValue R W P' g (C.scalar v)

structure Pointed (S : Type u) [CommRing S] (E F : EllipticFamily S) where
  map : E.curve ⟶ F.curve
  over_eq : map ≫ F.projection = E.projection
  zero_eq : zero E ≫ map = zero F

def imagePoint {S : Type u} [CommRing S] {E F : EllipticFamily S}
    (f : Pointed S E F) {T : Scheme.{u}} (t : T ⟶ Base S)
    (P : SchemeHomOver t E.projection) : SchemeHomOver t F.projection :=
  ⟨P.val ≫ f.map, by rw [Category.assoc, f.over_eq, P.property]⟩

def IsHom {S : Type u} [CommRing S] {E F : EllipticFamily S}
    (f : Pointed S E F) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Base S) (P Q : SchemeHomOver t E.projection),
    imagePoint f t (E.law.mul t P Q) = F.law.mul t (imagePoint f t P) (imagePoint f t Q)

def familyHodgeMap {S : Type u} [CommRing S] {E F : EllipticFamily S}
    (f : Pointed S E F) : hodge F ⟶ hodge E :=
  (pullbackEqIso f.zero_eq.symm F.projection.kaehler).hom ≫
    ((Scheme.Modules.pullbackComp (zero E) f.map).app F.projection.kaehler).inv ≫
    (Scheme.Modules.pullback (zero E)).map
      (differentialMap F.projection E.projection f.map (by simpa using f.over_eq))

/-- Actual finite etale quotient, with the specified scheme-theoretic cyclic
kernel and categorical factorization through pointed group maps. -/
structure Quotient (S : Type u) [CommRing S] (E : EllipticFamily S)
    (m : ℕ) (P : Base S ⟶ E.curve) where
  target : EllipticFamily S
  arrow : Pointed S E target
  hom : IsHom arrow
  finite : IsFinite arrow.map
  etale : Etale arrow.map
  surjective : Surjective arrow.map
  degree : ∀ z, arrow.map.finrank z = m
  kernel : (zero target).ker.comap arrow.map =
    ⨅ i : Fin m, (P ≫ E.law.schemeNsmul i.val).ker
  universal : ∀ (F : EllipticFamily S) (f : Pointed S E F), IsHom f →
    (∀ i : Fin m, P ≫ E.law.schemeNsmul i.val ≫ f.map = zero F) →
    ∃! g : Pointed S target F, IsHom g ∧ arrow.map ≫ g.map = f.map

variable (k : Type u) [Field k] (L : ℕ) (A : LegendreAtlas k L)
abbrev levelFamily := A.descent.family

def kernelPoint (m : ℕ) : Base A.quotient.ring ⟶ (levelFamily k L A).curve :=
  ((levelFamily k L A).law.nsmul (𝟙 _) (L / m) A.marking.x).val

def liftPoint (m N a b : ℕ) : Base A.quotient.ring ⟶ (levelFamily k L A).curve :=
  ((levelFamily k L A).law.mul (𝟙 _)
    ((levelFamily k L A).law.nsmul (𝟙 _) (L / (m*N) * b) A.marking.x)
    ((levelFamily k L A).law.nsmul (𝟙 _) (L / N * a) A.marking.y)).val

def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv v

/-- Local-frame formula for the SAME actual Hodge pullback. At c=1+12N,
weight=(c²-1)/2 and exponent=(c²-1)/48. No cusp expansion is assumed or claimed. -/
def IsNormalizedPower (m N : ℕ)
    (Q : Quotient A.quotient.ring (levelFamily k L A) m (kernelPoint k L A m))
    (d : Γ(power Q.target 24, ⊤)) (v : A.quotient.ring)
    (F : Γ(power (levelFamily k L A) (((1+12*N)^2-1)/2), ⊤)) : Prop :=
  ∀ (U : (Base A.quotient.ring).Opens) (η : Γ(hodge Q.target, U))
    (a : (Base A.quotient.ring).presheaf.obj (Opposite.op U)),
    IsFrame (hodge Q.target) U η →
    res (power Q.target 24) le_top d =
      a • tensorPowerSection (Base A.quotient.ring) (hodge Q.target) 24 U η →
    res (power (levelFamily k L A) (((1+12*N)^2-1)/2)) le_top F =
      ((Base A.quotient.ring).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (scalar A.quotient.ring
          ((algebraMap k A.quotient.ring (m : k)⁻¹)^(((1+12*N)^2-1)/2) * v)) *
        a^(((1+12*N)^2-1)/48)) •
      tensorPowerSection (Base A.quotient.ring) (hodge (levelFamily k L A))
        (((1+12*N)^2-1)/2) U ((familyHodgeMap Q.arrow).app U η)

end ArithmeticThetaOpenHodgeR0180
