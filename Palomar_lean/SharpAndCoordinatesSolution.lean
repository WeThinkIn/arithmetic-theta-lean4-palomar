module
public import AlgebraicTateCoordinatesR0143
public import CoordinateExactPolesR0143
public import AlgebraicModelCubicR0144
public import GlobalNormalizedDifferentialR0145
public import Mathlib
public import SharpMatrixKernelR0195
public import ComputedCoefficientMatrix
public import LatticeShellFinite
@[expose] public section
section Package00
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
namespace ArithmeticThetaPalomarCoordinates377
def NormalizedFrame (k : Type u) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
    (h3 : 3 ≤ r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
      (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s)
    (d : ℕ) (e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s d) : Prop :=
  ∀ (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s d) (n : ℕ),
    let i := ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj
      (ArithmeticThetaIdentitySectionsR0138.powerModule k M s d)
    let j := (Scheme.Modules.pullback f).map
      (ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.idealInclusion (s.ker^d)) ≫
        ArithmeticThetaPolygonCartierR0133.unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ ArithmeticThetaPolygonCartierR0133.unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso
        (CommRingCat.of (ArithmeticThetaInfinitesimalPolygonR0129.A k n))).inv
          (ArithmeticThetaIdentitySectionsR0138.equation k r n i ^ d) ∧
      ArithmeticThetaInfinitesimalPolygonR0129.trunc (PowerSeries k) PowerSeries.X n
        (ArithmeticThetaGenericEvaluationR0140.frameValue k M s d e φ) =
        ArithmeticThetaPolygonCohomologyR0131.markedPoint k n 1
          ((Scheme.ΓSpecIso (CommRingCat.of
            (ArithmeticThetaInfinitesimalPolygonR0129.A k n))).hom (q.app ⊤ z))
theorem normalizedFrame_iff (k : Type u) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (e : IdentityFrame k M s d) :
    ArithmeticThetaPalomarCoordinates377.NormalizedFrame k h3 M hM s hs d e ↔
      ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k h3 M hM s hs d e := by
  constructor
  · intro he φ n
    obtain ⟨z, hz, hv⟩ := he φ n
    obtain ⟨z', hz', hv'⟩ := AlgebraizedThetaSaturationR0138.algebraicFormal_realizes
      k h3 M hM s hs d φ n (zeroIndex r hr)
    letI := NormalizedIdentityFrameR0140.algebraicChart_mono k h3 M hM s hs d n
    have hzz : z = z' := GlobalCartierIdealLineR0133.mono_app_injective
      (CanonicalCartierLineReductionR0133.pulledInclusion
        (NormalizedIdentityFrameR0140.algebraicChart k M n)
        (GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ d))) ⊤
      (hz.trans hz'.symm)
    dsimp only [CanonicalCartierLineReductionR0133.pulledInclusion] at hv'
    rw [hzz, hv'] at hv
    exact hv.trans (congrArg (ArithmeticThetaPolygonCohomologyR0131.markedPoint k n 1)
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _))
  · intro he φ n
    obtain ⟨z, hz, hv⟩ := AlgebraizedThetaSaturationR0138.algebraicFormal_realizes
      k h3 M hM s hs d φ n (zeroIndex r hr)
    refine ⟨z, hz, ?_⟩
    dsimp only [CanonicalCartierLineReductionR0133.pulledInclusion] at hv
    rw [he φ n, hv]
    exact congrArg (ArithmeticThetaPolygonCohomologyR0131.markedPoint k n 1)
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _).symm
theorem algebraic_tate_coordinates :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
      (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s),
      ∀ odd : Bool, ∃! φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s
        (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd),
        ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ := by
  exact ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates
#print axioms algebraic_tate_coordinates
theorem coordinate_exact_poles :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → CategoryTheory.IsIso (ArithmeticThetaAlgebraicCoordinatesR0143.pulled k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) s φ) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaPalomarCoordinates377.NormalizedFrame k h3 M hM s hs (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e → ArithmeticThetaGenericEvaluationR0140.frameValue k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e φ = 1 := by
  intro k _ _ r hr h3 T M hM s hs odd φ hφ
  have h := ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_exact_poles k r hr h3 T M hM s hs odd φ hφ
  exact ⟨h.1, fun e he => h.2 e ((normalizedFrame_iff k h3 M hM s hs _ e).mp he)⟩
#print axioms coordinate_exact_poles
theorem algebraic_model_cubic :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ArithmeticThetaCubicModelR0144.ModelCubic k M s X Y := by
  exact ArithmeticThetaCubicModelR0144.algebraic_model_cubic
#print axioms algebraic_model_cubic
theorem global_normalized_differential (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ∃! e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
      (genericStructure k M).kaehler, IsGlobalDifferentialFrame k M s X Y e := by
  exact ArithmeticThetaCompactifiedDifferentialR0145.global_normalized_differential k r hr h3 T he M hM s hs X Y hX hY
#print axioms global_normalized_differential
/-- Reverse recovery of the literal original 020 statement. -/
theorem original_coordinate_exact_poles :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → CategoryTheory.IsIso (ArithmeticThetaAlgebraicCoordinatesR0143.pulled k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) s φ) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k h3 M hM s hs (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e → ArithmeticThetaGenericEvaluationR0140.frameValue k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e φ = 1 := by
  intro k _ _ r hr h3 T M hM s hs odd φ hφ
  have h := coordinate_exact_poles k r hr h3 T M hM s hs odd φ hφ
  exact ⟨h.1, fun e he => h.2 e ((normalizedFrame_iff k h3 M hM s hs _ e).mpr he)⟩
#print axioms normalizedFrame_iff
#print axioms original_coordinate_exact_poles
end ArithmeticThetaPalomarCoordinates377
end
end Package00
section Package01
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarSharp360
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
noncomputable def thetaMap {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
def pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j
def project {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => pairing A b b * v i - pairing A b v * b i
def step {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun i j => if k < j then project A (fun a => C a k) (fun a => C a j) i
    else C i j)
def runPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).take k).foldl (step A) 1
def basisMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := runPrefix A n
def norms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  pairing A (fun i => basisMatrix A i j) (fun i => basisMatrix A i j)
def naturalNorms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
  (norms A j).toNat
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def distinctNorms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (distinctNorms A).card
def level (N : ℕ) : ℕ := 24 * N^2
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
end ArithmeticThetaPalomarSharp360
namespace ArithmeticThetaPalomarSharp360.Bridges
open ArithmeticThetaPalomarSharp360
variable {n h : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ)
lemma validGram_eq : validGram A = ArithmeticThetaComputed.validGram A := rfl
lemma theta_eq : theta A = ArithmeticThetaComputed.theta A := rfl
lemma thetaMap_eq (As : Matrices n h) : thetaMap As = ArithmeticThetaComputed.thetaMap As := rfl
lemma pairing_eq (x y : Fin n → ℤ) : pairing A x y = ArithmeticThetaOrthogonalAlgorithm.pairing A x y := rfl
lemma project_eq (b v : Fin n → ℤ) : project A b v = ArithmeticThetaOrthogonalAlgorithm.project A b v := rfl
lemma step_eq (k : Fin n) : step A C k = ArithmeticThetaOrthogonalAlgorithm.step A C k := rfl
lemma runPrefix_eq (k : ℕ) : runPrefix A k = ArithmeticThetaOrthogonalAlgorithm.runPrefix A k := rfl
lemma basisMatrix_eq : basisMatrix A = ArithmeticThetaOrthogonalAlgorithm.basisMatrix A := rfl
lemma norms_eq (j : Fin n) : norms A j = ArithmeticThetaOrthogonalAlgorithm.norms A j := rfl
lemma naturalNorms_eq (j : Fin n) : naturalNorms A j = ArithmeticThetaOrthogonalAlgorithm.naturalNorms A j := rfl
lemma shell_finite (hA : validGram A) (a : ℕ) : Finite {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a : ℚ)} :=
  (ArithmeticThetaLattice.exact_shell_finite n _ hA.2.2 (a : ℚ)).to_subtype
lemma coefficientMatrix_complex_eq (As : Matrices n h) (hAs : ∀ i, validGram (As i)) (B : ℕ) :
    (coefficientMatrix As B).map (algebraMap ℚ ℂ) =
      (ArithmeticThetaComputed.coefficientMatrix As B).map (algebraMap ℚ ℂ) := by
  ext a i
  change ((coefficientMatrix As B a i : ℚ) : ℂ) =
    ((ArithmeticThetaComputed.coefficientMatrix As B a i : ℚ) : ℂ)
  rw [ArithmeticThetaComputed.computed_coefficient_matrix n h B As hAs a i]
  simp [coefficientMatrix, ArithmeticThetaComputed.theta]
end ArithmeticThetaPalomarSharp360.Bridges
namespace ArithmeticThetaPalomarSharp360
/-- Full original sharp kernel conclusion plus actual shell finiteness. -/
theorem sharpFiniteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    (∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧
    (n = 0 → cutoff A = 0 ∧ ∀ c : Fin h → ℂ,
      thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  obtain ⟨hk, hz⟩ := ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel n h hh A hA
  refine ⟨fun i a => Bridges.shell_finite (A i) (hA i) a, ?_, hz⟩
  intro B hB
  rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B]
  exact hk B hB
theorem original049Correspondence :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧ ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro n h hh A hA
  have hs := sharpFiniteDetermination n h hh A hA
  refine ⟨?_, hs.2.2⟩
  intro B hB
  have hk := hs.2.1 B hB
  rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B] at hk
  exact hk
end ArithmeticThetaPalomarSharp360
end
end Package01
