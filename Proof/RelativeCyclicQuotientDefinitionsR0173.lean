module

public import RelativeMultiplicationHodgeWeightR0172
public import EtaleHodgePullbackIsomorphismR0172
public import PointedHodgeBaseChangeR0172
public import AlgebraizedSplitMarkedDivisorR0136

@[expose] public section

/-! Cyclic quotients of actual relative elliptic curves. The input is one
section of exact fiberwise order; neither a quotient nor a Hodge comparison
is assumed in that input. All kernels below are actual ideal sheaves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeIsogenyHodgeR0172

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

/-- A split cyclic subgroup, with exact order on every fiber. -/
structure CyclicSection (n : ℕ) where
  point : Base R ⟶ Curve R W
  over_eq : point ≫ structureMap R W = 𝟙 _
  killed : point ≫ G.schemeNsmul n = origin R W
  disjoint : ∀ i j : Fin n, i ≠ j →
    Disjoint (Set.range (point ≫ G.schemeNsmul i.val))
      (Set.range (point ≫ G.schemeNsmul j.val))

def multiple {n : ℕ} (P : CyclicSection R W G n) (i : Fin n) :
    Base R ⟶ Curve R W := P.point ≫ G.schemeNsmul i.val

def kernelIdeal {n : ℕ} (P : CyclicSection R W G n) :
    (Curve R W).IdealSheafData := ⨅ i : Fin n, (multiple R W G P i).ker

def splitStructure (n : ℕ) : Spec (CommRingCat.of (Fin n → R)) ⟶ Base R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Fin n → R)))

def component (n : ℕ) (i : Fin n) : Base R ⟶ Spec (CommRingCat.of (Fin n → R)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i))

def mapPoint {V : WeierstrassCurve R} (f : PointedMap R W V)
    {X : Scheme.{u}} (t : X ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) : SchemeHomOver t (structureMap R V) :=
  ⟨x.val ≫ f.map, by rw [Category.assoc, f.over_eq, x.property]⟩

/-- Compatibility with the group operation on all scheme-valued points. -/
def IsGroupHom {V : WeierstrassCurve R} (H : Law R V) (f : PointedMap R W V) : Prop :=
  ∀ (X : Scheme.{u}) (t : X ⟶ Base R)
    (x y : SchemeHomOver t (structureMap R W)),
    mapPoint R W f t (G.mul t x y) =
      H.mul t (mapPoint R W f t x) (mapPoint R W f t y)

/-- The actual finite etale map has degree n and exactly the prescribed
scheme-theoretic kernel. The target is a genuine projective Weierstrass curve. -/
def IsQuotient {n : ℕ} (P : CyclicSection R W G n)
    {V : WeierstrassCurve R} (f : PointedMap R W V) : Prop :=
  IsFinite f.map ∧ Etale f.map ∧ Surjective f.map ∧
    (∀ x, f.map.finrank x = n) ∧
    (origin R V).ker.comap f.map = kernelIdeal R W G P

/-- Full source-lift hypotheses: its N-multiple belongs to this cyclic kernel,
and the lift is disjoint from every kernel section on the entire base. -/
def LiftConditions {n : ℕ} (P : CyclicSection R W G n) (N : ℕ)
    (Q : Base R ⟶ Curve R W) : Prop :=
  Q ≫ structureMap R W = 𝟙 _ ∧
    (∃ i : Fin n, Q ≫ G.schemeNsmul N = multiple R W G P i) ∧
    (∀ i : Fin n, Disjoint (Set.range Q) (Set.range (multiple R W G P i)))

end ArithmeticThetaRelativeCyclicQuotientR0173
