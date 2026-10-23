module

public import CanonicalCartierLineReductionR0133
public import SplitFiniteMarkedDivisorR0133
public import GlobalCartierIdealLineR0133

@[expose] public section

/-! Numerators of sections of O(dD), for the actual marked divisor D.
Cross multiplication is used only in the actual overlap rings; the sheaf
comparison is a new obligation, not a hypothesis of this definition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCartierR0133
variable (k : Type u) [Field k] [CharZero k]

def equation (r n : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) : A k n :=
  pairEquation k n (a i) (a (next r hr i))

def Compatible (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s : Fin r → A k n) : Prop :=
  ∀ i : Fin r,
    E (restriction k n false (s i)) *
        restriction k n true (equation k r n hr a (next r hr i)) ^ d =
      restriction k n true (s (next r hr i)) *
        E (restriction k n false (equation k r n hr a i)) ^ d

def Sections (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ) : Type u :=
  {s : Fin r → A k n // Compatible k r n hr E a d s}

def IsBasis (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (b : Fin (d*r) → Sections k r n hr E a d) : Prop :=
  ∀ s : Sections k r n hr E a d, ∃! c : Fin (d*r) → R k n,
    ∀ i : Fin r, s.val i = ∑ j : Fin (d*r), base k n (c j) * (b j).val i

def ReductionFacts (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N) : Prop :=
  let red := truncReduce (ArithmeticThetaNodeCharts.Node k)
    (ArithmeticThetaNodeCharts.t k) n N h
  (∀ s : Sections k r N hr (T.overlap N) a d,
    Compatible k r n hr (T.overlap n) a d (fun i => red (s.val i))) ∧
  (∀ s : Sections k r n hr (T.overlap n) a d,
    ∃ v : Sections k r N hr (T.overlap N) a d, ∀ i, red (v.val i) = s.val i) ∧
  (∀ s : Sections k r N hr (T.overlap N) a d,
    (∀ i, red (s.val i) = 0) ↔
    ∃ v : Sections k r N hr (T.overlap N) a d, ∀ i,
      s.val i = base k N (parameter k N ^ (n+1)) * v.val i)

def GloballyGenerated (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ) : Prop :=
  ∀ i : Fin r, Ideal.span
    (Set.range (fun s : Sections k r n hr E a d => s.val i)) = ⊤

def MultiplicationSurjective (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d e : ℕ) : Prop :=
  ∀ s : Sections k r n hr E a (d+e), ∃ (l : ℕ)
    (v : Fin l → Sections k r n hr E a d)
    (w : Fin l → Sections k r n hr E a e),
    ∀ i, s.val i = ∑ j : Fin l, (v j).val i * (w j).val i

def FormalBasisFacts (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d : ℕ) : Prop :=
  ∃ b : ∀ n : ℕ, Fin (d*r) → Sections k r n hr (T.overlap n) a d,
    (∀ n, IsBasis k r n hr (T.overlap n) a d (b n)) ∧
    (∀ (n N : ℕ) (h : n ≤ N) (j : Fin (d*r)) (i : Fin r),
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((b N j).val i) = (b n j).val i) ∧
    (∀ s : ∀ n, Sections k r n hr (T.overlap n) a d,
      (∀ (n N : ℕ) (h : n ≤ N) (i : Fin r),
        truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
          n N h ((s N).val i) = (s n).val i) →
      ∃! c : Fin (d*r) → PowerSeries k, ∀ (n : ℕ) (i : Fin r),
        (s n).val i = ∑ j : Fin (d*r),
          base k n (trunc (PowerSeries k) PowerSeries.X n (c j)) * (b n j).val i)

def powerIdealModule {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (d : ℕ) : D.X.Modules :=
  GlobalCartierIdealLineR0133.idealModule ((markedIdeal k r n hr D a)^d)

def GlobalDualSections {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (d : ℕ) : Type u :=
  powerIdealModule k D a d ⟶ (SheafOfModules.unit D.X.ringCatSheaf : D.X.Modules)

def Realizes {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (d : ℕ) (s : Sections k r n hr E a d)
    (φ : GlobalDualSections k D a d) : Prop :=
  ∀ i : Fin r,
    let f := D.chart i
    let M := (Scheme.Modules.pullback f).obj (powerIdealModule k D a d)
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion ((markedIdeal k r n hr D a)^d)) ≫
        unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ t : Γ(M, ⊤),
      j.app ⊤ t = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        ((equation k r n hr a i)^d) ∧
      q.app ⊤ t = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val i)
end ArithmeticThetaPositiveLineR0134
