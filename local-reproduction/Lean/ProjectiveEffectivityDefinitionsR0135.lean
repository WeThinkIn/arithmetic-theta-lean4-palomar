import ProperFormalFunctions
import GlobalPositiveSectionRealizationR0134
import CompatibleFormalSectionBasisR0134
import PositiveSectionMultiplicationR0134
import PositiveGlobalGenerationR0134
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.LaurentSeries

/-! Concrete homogeneous equations and projective effectivity for the accepted
cyclic polygon tower. The model record contains maps only; its geometric
properties are separate predicates to be proved. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaProjectiveEffectivityR0135
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPositiveLineR0134
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [CharZero k]

def CubicBases (r : ℕ) (hr : 0 < r) (T : Tower k r hr) (a : Fin r → kˣ) :=
  ∀ n : ℕ, Fin (3*r) → Sections k r n hr (T.overlap n) a 3

def CompatibleBases {r : ℕ} {hr : 0 < r} (T : Tower k r hr)
    (a : Fin r → kˣ) (b : CubicBases k r hr T a) : Prop :=
  (∀ n, IsBasis k r n hr (T.overlap n) a 3 (b n)) ∧
  (∀ n N (h : n ≤ N) j i,
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h ((b N j).val i) = (b n j).val i)

def FormalSection (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d : ℕ) :=
  {s : ∀ n, Sections k r n hr (T.overlap n) a d //
    ∀ n N (h : n ≤ N) i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((s N).val i) = (s n).val i}

def evaluate {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
    (b : CubicBases k r hr T a) (n : ℕ) (i : Fin r) :
    MvPolynomial (Fin (3*r)) (PowerSeries k) →+* A k n :=
  MvPolynomial.eval₂Hom ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
    (fun j => (b n j).val i)

def taggedEvaluate {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
    (b : CubicBases k r hr T a) (n : ℕ) (i : Fin r) :
    MvPolynomial (Fin (3*r)) (R k n) →+* Polynomial (A k n) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (base k n))
    (fun j => Polynomial.C ((b n j).val i) * Polynomial.X)

def coefficientReduction (r n : ℕ) :
    MvPolynomial (Fin (3*r)) (PowerSeries k) →+* MvPolynomial (Fin (3*r)) (R k n) :=
  MvPolynomial.map (trunc (PowerSeries k) PowerSeries.X n)

def relationsAt {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
    (b : CubicBases k r hr T a) (n : ℕ) : Ideal (MvPolynomial (Fin (3*r)) (R k n)) :=
  ⨅ i : Fin r, RingHom.ker (taggedEvaluate k b n i)

def formalRelations {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
    (b : CubicBases k r hr T a) : Ideal (MvPolynomial (Fin (3*r)) (PowerSeries k)) :=
  ⨅ n : ℕ, Ideal.comap (coefficientReduction k r n) (relationsAt k b n)

def HomogeneousPresentation {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    {a : Fin r → kˣ} (b : CubicBases k r hr T a) : Prop :=
  (∀ d : ℕ, 0 < d → ∀ s : FormalSection k r hr T a (3*d),
    ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), p.IsHomogeneous d ∧
      ∀ n i, evaluate k b n i p = (s.val n).val i) ∧
  (∀ d : ℕ, 0 < d → ∀ n, ∀ s : Sections k r n hr (T.overlap n) a (3*d),
    ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), p.IsHomogeneous d ∧
      ∀ i, evaluate k b n i p = s.val i)

def RelationEffectivity {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    {a : Fin r → kˣ} (b : CubicBases k r hr T a) : Prop :=
  (∀ n, Ideal.map (coefficientReduction k r n) (formalRelations k b) = relationsAt k b n) ∧
  (∃ (l : ℕ) (f : Fin l → MvPolynomial (Fin (3*r)) (PowerSeries k)) (degree : Fin l → ℕ),
    (∀ j, (f j).IsHomogeneous (degree j)) ∧
      Ideal.span (Set.range f) = formalRelations k b)

def projectiveSpace (S : Type u) [CommRing S] (N : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin N) S)

def projectiveStructure (S : Type u) [CommRing S] (N : ℕ) :
    projectiveSpace S N ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin N) S) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap S ((MvPolynomial.homogeneousSubmodule (Fin N) S) 0)))

def coefficientChartMap {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} {a : Fin r → kˣ}
    (b : Fin (3*r) → Sections k r n hr E a 3) (i : Fin r) :
    MvPolynomial (Fin (3*r)) (PowerSeries k) →+* Γ(specA k n, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom.comp
    (MvPolynomial.eval₂Hom ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
      (fun j => (b j).val i))

def RealizesEmbedding {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} {a : Fin r → kˣ}
    (D : Atlas k r n hr E) (b : Fin (3*r) → Sections k r n hr E a 3)
    (j : D.X ⟶ projectiveSpace (PowerSeries k) (3*r)) : Prop :=
  ∀ i : Fin r,
    ∃ h : Ideal.map (coefficientChartMap k b i)
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k))).toIdeal = ⊤,
      D.chart i ≫ j = Proj.fromOfGlobalSections
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k))
        (coefficientChartMap k b i) h

def baseInclusion (n : ℕ) : specR k n ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (trunc (PowerSeries k) PowerSeries.X n))

def ProjectiveSystem {r : ℕ} {hr : 0 < r} (T : Tower k r hr)
    (a : Fin r → kˣ) (b : CubicBases k r hr T a)
    (j : ∀ n, (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r)) : Prop :=
  (∀ n, IsClosedImmersion (j n) ∧ RealizesEmbedding k (T.atlas n) (b n) (j n) ∧
    j n ≫ projectiveStructure (PowerSeries k) (3*r) = (T.atlas n).p ≫ baseInclusion k n) ∧
  (∀ n N (h : n ≤ N), T.transition n N h ≫ j N = j n)

structure Model {r : ℕ} {hr : 0 < r} (T : Tower k r hr) where
  X : Scheme.{u}
  p : X ⟶ Spec (CommRingCat.of (PowerSeries k))
  inclusion : ∀ n, (T.atlas n).X ⟶ X

def IsModel {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (M : Model k T) : Prop :=
  IsProper M.p ∧ Flat M.p ∧
  (∀ n, IsPullback (M.inclusion n) (T.atlas n).p M.p (baseInclusion k n)) ∧
  (∀ n N (h : n ≤ N), T.transition n N h ≫ M.inclusion N = M.inclusion n)

def genericBase : Spec (CommRingCat.of (LaurentSeries k)) ⟶
    Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))

def genericStructure {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T) :=
  CategoryTheory.Limits.pullback.snd M.p (genericBase k)

end ArithmeticThetaProjectiveEffectivityR0135
