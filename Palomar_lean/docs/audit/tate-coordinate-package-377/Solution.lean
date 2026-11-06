module
public import AlgebraicTateCoordinatesR0143
public import CoordinateExactPolesR0143
public import AlgebraicModelCubicR0144
public import GlobalNormalizedDifferentialR0145
@[expose] public section
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
