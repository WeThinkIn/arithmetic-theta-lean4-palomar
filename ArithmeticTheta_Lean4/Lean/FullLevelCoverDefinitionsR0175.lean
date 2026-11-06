import CyclicQuotientArbitraryBaseChangeR0173
import CyclicQuotientTorsionKatoValueR0173

/-! The full torsion marking functor on the actual relative elliptic curve.
This is an affine-family prerequisite, not a modular-curve compactification.
No representing scheme, cover geometry or torsion lift is assumed to exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeCyclicQuotientR0173

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

/-- Two killed sections whose nonzero residue combinations avoid the actual
identity subscheme. The test scheme may be nonreduced or disconnected. -/
structure FullLevel (L : ℕ) {T : Scheme.{u}} (t : T ⟶ Base R) where
  x : SchemeHomOver t (structureMap R W)
  y : SchemeHomOver t (structureMap R W)
  killed_x : G.nsmul t L x = G.one t
  killed_y : G.nsmul t L y = G.one t
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val)
      (Set.range (origin R W))

/-- Universal marking data; representability is a separate proved predicate. -/
structure LevelScheme (L : ℕ) where
  space : Scheme.{u}
  projection : space ⟶ Base R
  level : FullLevel R W G L projection

def Represents {L : ℕ} (D : LevelScheme R W G L) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Base R) (A : FullLevel R W G L t),
    ∃! q : SchemeHomOver t D.projection,
      q.val ≫ D.level.x.val = A.x.val ∧ q.val ≫ D.level.y.val = A.y.val

/-- The full GL(2,Z/L) cover degree, without imposing a Weil pairing. -/
def levelDegree (L : ℕ) : ℕ := Nat.card ((ZMod L × ZMod L) ≃+ (ZMod L × ZMod L))

def coordinatePoint {L : ℕ} (A : FullLevel R W G L (𝟙 (Base R)))
    (i j : Fin L) : Base R ⟶ Curve R W :=
  (G.mul (𝟙 (Base R)) (G.nsmul (𝟙 (Base R)) i.val A.x)
    (G.nsmul (𝟙 (Base R)) j.val A.y)).val

def torsionStructure (L : ℕ) :
    Spec (CommRingCat.of ((Fin L × Fin L) → R)) ⟶ Base R :=
  Spec.map (CommRingCat.ofHom (algebraMap R ((Fin L × Fin L) → R)))

def torsionComponent (L : ℕ) (i j : Fin L) :
    Base R ⟶ Spec (CommRingCat.of ((Fin L × Fin L) → R)) :=
  Spec.map (CommRingCat.ofHom
    (Pi.evalRingHom (fun _ : Fin L × Fin L => R) (i,j)))

def kernelPoint {L : ℕ} (m : ℕ)
    (A : FullLevel R W G L (𝟙 (Base R))) : Base R ⟶ Curve R W :=
  (G.nsmul (𝟙 (Base R)) (L / m) A.x).val

/-- Source lift for target coordinates (a,b): (L/(mN))*b*x + (L/N)*a*y.
The first marking is the toric direction at a future designated Tate cusp. -/
def liftPoint {L : ℕ} (m N a b : ℕ)
    (A : FullLevel R W G L (𝟙 (Base R))) : Base R ⟶ Curve R W :=
  (G.mul (𝟙 (Base R))
    (G.nsmul (𝟙 (Base R)) (L / (m*N) * b) A.x)
    (G.nsmul (𝟙 (Base R)) (L / N * a) A.y)).val

variable [IsDomain R]

/-- A constructed normal integral finite etale splitting extension. Every
algebraic structure, geometric map and marking is tied to the same S and ι. -/
structure LevelExtension (L : ℕ) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  inclusion : R →+* ring
  [elliptic : (W.map inclusion).IsElliptic]
  law : Law ring (W.map inclusion)
  originLaw : IsOriginLaw ring (W.map inclusion) law
  curveMap : Curve ring (W.map inclusion) ⟶ Curve R W
  cartesian : IsBaseChange R W G ring (W.map inclusion) law inclusion curveMap
  finite : IsFinite (baseMap R ring inclusion)
  etale : Etale (baseMap R ring inclusion)
  surjective : Surjective (baseMap R ring inclusion)
  degree : ∀ z, 0 < (baseMap R ring inclusion).finrank z ∧
    (baseMap R ring inclusion).finrank z ≤ levelDegree L
  level : FullLevel ring (W.map inclusion) law L (𝟙 (Base ring))

attribute [instance] LevelExtension.commRing LevelExtension.domain
  LevelExtension.noetherian LevelExtension.normal LevelExtension.rational
  LevelExtension.elliptic

end ArithmeticThetaFullLevelCoverR0175
