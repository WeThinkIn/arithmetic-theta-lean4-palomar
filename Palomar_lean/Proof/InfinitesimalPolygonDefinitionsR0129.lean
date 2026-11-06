module

public import IndexedAdjacentCoordinatesR0058
public import TateNodeCompletion
public import CompletedCoordinateRestrictionsR0058
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

/-! Concrete infinitesimal Tate polygon data. Atlas fields specify the exact
rings, maps, covering and intersections. Properness, flatness, existence and
algebraization are not assumed by the definitions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
open CategoryTheory

abbrev Trunc (R : Type u) [CommRing R] (t : R) (n : ℕ) :=
  R ⧸ (Ideal.span {t}) ^ (n+1)
def trunc (R : Type u) [CommRing R] (t : R) (n : ℕ) : R →+* Trunc R t n :=
  Ideal.Quotient.mk _
def truncMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (s : S) (h : f t = s) (n : ℕ) :
    Trunc R t n →+* Trunc S s n :=
  Ideal.quotientMap _ f (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, h])
def truncReduce (R : Type u) [CommRing R] (t : R) (n N : ℕ) (h : n ≤ N) :
    Trunc R t N →+* Trunc R t n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

variable (k : Type u) [Field k] [CharZero k]
abbrev R (n : ℕ) := Trunc (PowerSeries k) PowerSeries.X n
abbrev A (n : ℕ) := Trunc (ArithmeticThetaNodeCharts.Node k)
  (ArithmeticThetaNodeCharts.t k) n
abbrev RawOpen (side : Bool) := ArithmeticThetaIndexedOverlapsR0058.Open k 0 side
def openParameter (side : Bool) : RawOpen k side :=
  algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side)
    (ArithmeticThetaNodeCharts.t k)
abbrev B (n : ℕ) (side : Bool) := Trunc (RawOpen k side) (openParameter k side) n

def base (n : ℕ) : R k n →+* A k n :=
  truncMap (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
    PowerSeries.X (ArithmeticThetaNodeCharts.t k) rfl n
def restriction (n : ℕ) (side : Bool) : A k n →+* B k n side :=
  truncMap (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side))
    (ArithmeticThetaNodeCharts.t k) (openParameter k side) rfl n

def rawAdjacent : RawOpen k false ≃+* RawOpen k true :=
  ArithmeticThetaIndexedOverlapsR0058.adjacent k 1 0

def IsAdjacent (n : ℕ) (E : B k n false ≃+* B k n true) : Prop :=
  E.toRingHom.comp (trunc (RawOpen k false) (openParameter k false) n) =
    (trunc (RawOpen k true) (openParameter k true) n).comp (rawAdjacent k).toRingHom

abbrev Hat := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev HatA (n : ℕ) := Trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n
abbrev HatOpen (side : Bool) := ArithmeticThetaIndexedOverlapsR0058.OpenHat k 0 side
abbrev HatB (n : ℕ) (side : Bool) := Trunc (HatOpen k side)
  (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n

def CompletionComparison (n : ℕ) (e : HatA k n ≃+* A k n)
    (o : ∀ side : Bool, HatB k n side ≃+* B k n side) : Prop :=
  e.toRingHom.comp ((trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n).comp
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) =
    (trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n).comp
      (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k).toRingHom ∧
  (∀ side : Bool, (o side).toRingHom.comp
      ((trunc (HatOpen k side)
        (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n).comp
        (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side)) =
      trunc (RawOpen k side) (openParameter k side) n) ∧
  (∀ (side : Bool) (s : Hat k),
    o side (trunc (HatOpen k side)
      (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n
      (Classical.choose (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions
        k 0 side) s)) =
    restriction k n side (e (trunc (Hat k)
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n s)))

def specR (n : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (R k n))
def specA (n : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (A k n))
def specB (n : ℕ) (side : Bool) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (B k n side))
def structureMap (n : ℕ) : specA k n ⟶ specR k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (base k n))
def rightLeg (n : ℕ) : specB k n true ⟶ specA k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (restriction k n true))
def leftLeg (n : ℕ) (E : B k n false ≃+* B k n true) :
    specB k n true ⟶ specA k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (E.toRingHom.comp (restriction k n false)))
def next (r : ℕ) (hr : 0 < r) (i : Fin r) : Fin r :=
  ⟨(i.val+1)%r, Nat.mod_lt _ hr⟩

/-- A realization of the explicit cyclic atlas. All intersections are fixed:
adjacent ones are the specified coordinate open; nonadjacent ones are empty. -/
structure Atlas (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true) where
  X : AlgebraicGeometry.Scheme.{u}
  p : X ⟶ specR k n
  chart : Fin r → (specA k n ⟶ X)
  chart_open : ∀ i, AlgebraicGeometry.IsOpenImmersion (chart i)
  covers : ∀ x : X, ∃ (i : Fin r) (a : specA k n), chart i a = x
  chart_over : ∀ i, chart i ≫ p = structureMap k n
  adjacent : ∀ i, CategoryTheory.IsPullback (leftLeg k n E) (rightLeg k n)
    (chart i) (chart (next r hr i))
  disjoint : ∀ i j, i ≠ j → next r hr i ≠ j → next r hr j ≠ i →
    Disjoint (Set.range (chart i)) (Set.range (chart j))

def baseReduction (n N : ℕ) (h : n ≤ N) : specR k n ⟶ specR k N :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (truncReduce (PowerSeries k) PowerSeries.X n N h))
def chartReduction (n N : ℕ) (h : n ≤ N) : specA k n ⟶ specA k N :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h))

def IsReduction (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (D : Atlas k r n hr E) (T : Atlas k r N hr F) (i : D.X ⟶ T.X) : Prop :=
  i ≫ T.p = D.p ≫ baseReduction k n N h ∧
    ∀ j : Fin r, D.chart j ≫ i = chartReduction k n N h ≫ T.chart j

/-- A tower has explicit maps and their equations, without assumed geometry. -/
structure Tower (r : ℕ) (hr : 0 < r) where
  overlap : ∀ n, B k n false ≃+* B k n true
  overlap_spec : ∀ n, IsAdjacent k n (overlap n)
  atlas : ∀ n, Atlas k r n hr (overlap n)
  transition : ∀ n N (h : n ≤ N), (atlas n).X ⟶ (atlas N).X
  transition_spec : ∀ n N h, IsReduction k r n N hr h (atlas n) (atlas N) (transition n N h)
  identity : ∀ n, transition n n (le_refl n) = 𝟙 (atlas n).X
  composition : ∀ n N P (h : n ≤ N) (h' : N ≤ P),
    transition n N h ≫ transition N P h' = transition n P (le_trans h h')

end ArithmeticThetaInfinitesimalPolygonR0129
