module

public import SimultaneousUnaryCommonCoverR0187
public import ComputedFamilyFormalUnaryConsumerR0127
public import FinitePullbackSectionDegree
public import TensorProductLaws
public import PullbackTensorSections

@[expose] public section

/-! Source-facing arithmetic indexing and actual common tensor-line sections.
All existence and expansion assertions below are obligation conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaLatticeSectionsR0188
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaOrthogonalAlgorithm ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaPullback
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183

abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
abbrev Cosets {n h : ℕ} (A : Matrices n h) (i : Fin h) :=
  Fin (basisMatrix (A i)).det.natAbs

def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)

def centered (m : ℕ) (a : Fin m) : ℤ :=
  if 2 * a.val < m then (a.val : ℤ) else (a.val : ℤ) - (m : ℤ)

/-- Enumerate the distinct pairs actually used by the chosen preimage cosets. -/
structure Indexing {n h : ℕ} (A : Matrices n h) where
  representatives : (i : Fin h) → Cosets A i → preimageLattice (basisMatrix (A i))
  residue : (i : Fin h) → Cosets A i → (j : Fin n) → Fin (naturalNorms (A i) j)
  count : ℕ
  pair : Fin count → ℕ × ℤ
  index : (i : Fin h) → Cosets A i → Fin n → Fin count

def Indexed {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
  (∀ i, Representatives (basisMatrix (A i)) (U.representatives i)) ∧
  (∀ i a j, ∃ z : ℤ,
    (naturalNorms (A i) j : ℚ) * (U.representatives i a).val j =
      ((U.residue i a j).val : ℚ) + (naturalNorms (A i) j : ℚ) * (z : ℚ)) ∧
  Function.Injective U.pair ∧
  (∀ i a j, U.pair (U.index i a j) =
    (naturalNorms (A i) j, centered (naturalNorms (A i) j) (U.residue i a j))) ∧
  (∀ z : Fin U.count, ∃ i a j, U.index i a j = z)

/-- Literal q=t^(24*N^2) substitution; no chosen series functional. -/
def expanded {n h : ℕ} (A : Matrices n h) (c : Fin h → ℂ) : PowerSeries ℂ :=
  PowerSeries.subst (PowerSeries.X ^ ArithmeticThetaCompactUnaryR0183.level (commonN A)) (ArithmeticThetaComputed.thetaMap A c)

def FormalIdentity {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
  ∀ c : Fin h → ℂ, expanded A c =
    ∑ i : Fin h, c i • (∑ a : Cosets A i, ∏ j : Fin n,
      unarySeries ℂ (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2)

/-- Actual pullback of the effective cusp half-divisor line. -/
abbrev coverLine {k : Type} [Field k] [CharZero k] {L : ℕ}
    {D : LevelData k L} {X : Compactification k L D} {x : X.space}
    (A : DivisorLine (Component k L D X x)) {b : ℕ}
    (R : RootCover k (Component k L D X x) (projection k L D X x) b) :=
  (Scheme.Modules.pullback R.map).obj A.line

/-- Degree is the residue-weighted degree for the actual structural morphism.
Normal covers and finiteness are produced, not silently inferred from finrank. -/
def CoverDegree (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (A : DivisorLine (Component k L D X x)) (b n : ℕ)
    (R : RootCover k (Component k L D X x) (projection k L D X x) b) : Prop :=
  letI := R.integral
  ∃ hY : IsLocallyNoetherian R.space, letI := hY
    ArithmeticThetaCurveDegree.OneDimensionalCharts R.space ∧
    ArithmeticThetaNormalizedSections.NormalAffine R.space ∧
    Scheme.Modules.IsInvertible (coverLine A R) ∧
    (∃ ι : Type, Nonempty (ArithmeticThetaLineRoot.NormalFrameCover R.space
      (tensorPower R.space (coverLine A R) n) ι)) ∧
    ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover R.space
      (tensorPower R.space (coverLine A R) n) ι)
      (t : Sections R.space (tensorPower R.space (coverLine A R) n))
      (E : R.space →₀ ℤ), t ≠ 0 →
      ArithmeticThetaSectionOrder.MatchesSectionOrder R.space
        (tensorPower R.space (coverLine A R) n) C t E →
      24 * ArithmeticThetaCurveDegree.weightedDegree k (R.map ≫ projection k L D X x) E =
        (n : ℤ) * (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
          (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ∧
      48 * ArithmeticThetaCurveDegree.weightedDegree k (R.map ≫ projection k L D X x) E ≤
        (n : ℤ) * (b : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ)

/-- Scalars on the actual curve use its displayed structure morphism. -/
def baseScalar (k : Type) [Field k] {Y : Scheme}
    (b : Y ⟶ Spec (CommRingCat.of k)) (c : k) : Y.presheaf.obj (Opposite.op ⊤) :=
  b.appTop (ArithmeticThetaOpenHodgeR0180.scalar k c)

/-- The common geometric realization retains the cusp divisor line, the finite
map, the square isomorphism, its normalized frame and all actual unary sections.
The sigma sections are explicitly their coset tensor polynomials. -/
def GeometricFamily {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    {D : LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A))}
    {X : Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D}
    (H : Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D X)
    (V : DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D X) : Prop :=
  let N := commonN A
  let L := ArithmeticThetaCompactUnaryR0183.level N
  let x := V.disk (closedPoint ℂ)
  ∃ (J : DivisorLine (Component ℂ L D X x)), IsCuspHalfLine ℂ L D X x J ∧
    ∃ R : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x)
        (24 * (exponent N)^U.count),
      CoverDegree ℂ L D X x J (24 * (exponent N)^U.count) n R ∧
      ∃ (g : Disk ℂ ⟶ R.space)
        (hg : g ≫ (R.map ≫ inclusion ℂ L D X x) = V.disk),
        IsDominant (genericInclusion ℂ ≫ g) ∧
        ∃ (β : tensorPower R.space (coverLine J R) 2 ≅
            (Scheme.Modules.pullback (R.map ≫ inclusion ℂ L D X x)).obj H.line)
          (η : Sections (Disk ℂ) ((Scheme.Modules.pullback V.disk).obj H.line))
          (e : Sections (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R))),
          ExtendsGenerator ℂ L H V η ∧
          ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ e ∧
          (squareOnDisk ℂ (R.map ≫ inclusion ℂ L D X x) (coverLine J R) H.line
            β g V.disk hg).hom.app ⊤
            (tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R)) 2 ⊤ e) = η ∧
          ∃ (t : Fin U.count → Sections R.space (coverLine J R))
            (σ : Fin h → Sections R.space (tensorPower R.space (coverLine J R) n)),
            (∀ j, t j ≠ 0 ∧ pullbackGlobalSection g (coverLine J R) (t j) =
              ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ)
                (unarySeries ℂ N (U.pair j).1 (U.pair j).2) • e) ∧
            (∀ i, σ i = ∑ a : Cosets A i,
              tensorProductSection R.space (coverLine J R) n ⊤ (fun j => t (U.index i a j))) ∧
            (∀ c : Fin h → ℂ,
              pullbackPowerSection g (coverLine J R) n
                (∑ i : Fin h, baseScalar ℂ (R.map ≫ projection ℂ L D X x) (c i) • σ i) =
                ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (expanded A c) •
                  tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R)) n ⊤ e)

end ArithmeticThetaLatticeSectionsR0188
