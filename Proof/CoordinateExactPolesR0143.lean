module

public import AlgebraicTateCoordinatesR0143
public import AlgebraicIdentityEvaluationR0140

@[expose] public section

/-! Exact poles of the literal algebraic Tate coordinates at the marked identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaAlgebraicCoordinatesR0143
namespace CoordinateExactPolesR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaGenericEvaluationR0140
open NormalizedIdentityFrameR0140

variable (k : Type u) [Field k] [CharZero k]

lemma marked_x (n : ℕ) : markedPoint k n 1 (coordX k n) = 1 := by
  simp [markedPoint, mkPoint, coordX, markedUnit, trunc, ArithmeticThetaNodeCharts.x, ArithmeticThetaNodeCharts.quotientMap]

lemma marked_equation (r n : ℕ) (hr : 0 < r) :
    markedPoint k n 1 (equation k r n (zeroIndex r hr)) = 0 := by
  unfold equation
  simp only [show (zeroIndex r hr).val = 0 from rfl, ↓reduceIte,
    map_mul, map_sub, map_one, marked_x, sub_self, zero_mul]

lemma numerator_identity (odd : Bool) (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    markedPoint k n 1 (numerator k odd r n (zeroIndex r hr)) = 1 := by
  have hz : (zeroIndex r hr).val = 0 := rfl
  have hlast' : ¬ 1 = r := by omega
  cases odd <;>
    simp only [numerator, Bool.false_eq_true, ↓reduceIte, hz, Nat.zero_add,
      Nat.sub_zero, hlast', and_false, map_sub, map_add, map_mul,
      map_pow, map_sum, map_one, map_ofNat, marked_x, marked_equation,
      degree, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, sub_zero, mul_one, one_mul,
      AlgebraicIdentityEvaluationR0140.marked_base]
  rw [show (1 + 1 : R k n) = trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)) by rw [map_ofNat, map_ofNat]; norm_num,
    ← map_mul, ← map_mul]
  simp

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma normalized_value (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (odd : Bool) (φ : Dual k M s (degree odd))
    (hφ : RealizesCoordinate k odd M s φ)
    (e : IdentityFrame k M s (degree odd))
    (he : NormalizedFrame k h3 M hM s hs (degree odd) e) :
    frameValue k M s (degree odd) e φ = 1 := by
  apply AlgebraizedThetaSaturationR0138.powerSeries_ext
  intro n
  rw [he φ n, map_one]
  obtain ⟨z, hz, hv⟩ := hφ n (zeroIndex r hr)
  obtain ⟨z', hz', hv'⟩ := AlgebraizedThetaSaturationR0138.algebraicFormal_realizes
    k h3 M hM s hs (degree odd) φ n (zeroIndex r hr)
  let := algebraicChart_mono k h3 M hM s hs (degree odd) n
  have hzz : z = z' := mono_app_injective
    (pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker ^ degree odd))) ⊤
      (hz.trans hz'.symm)
  dsimp only [pulledInclusion] at hv'
  rw [hzz, hv'] at hv
  have hvv := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm.injective hv
  rw [hvv]
  exact numerator_identity k odd r n hr h3

end CoordinateExactPolesR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaPolygonCartierR0133
open CanonicalCartierLineReductionR0133 GlobalCartierIdealLineR0133
open NormalizedIdentityFrameR0140

theorem coordinate_exact_poles :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → CategoryTheory.IsIso (ArithmeticThetaAlgebraicCoordinatesR0143.pulled k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) s φ) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k h3 M hM s hs (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e → ArithmeticThetaGenericEvaluationR0140.frameValue k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e φ = 1 := by
  intro k _ _ r hr h3 T M hM s hs odd φ hφ
  have hv := CoordinateExactPolesR0143.normalized_value k h3 M hM s hs odd φ hφ
  refine ⟨?_, hv⟩
  obtain ⟨e, he⟩ := normalized_identity_frame k r hr h3 T M hM s hs (degree odd)
  have hmap := frameValue_morphism k M s (degree odd) e φ
  rw [hv e he] at hmap
  have hid : e.inv ≫ pulled k M s (degree odd) s φ = 𝟙 _ := by
    rw [show pulled k M s (degree odd) s φ = pulledInclusion s φ from rfl, hmap]
    apply unit_hom_ext
    simp [fromSection_apply]
  have hp : pulled k M s (degree odd) s φ = e.hom := by
    apply (cancel_epi e.inv).mp
    rw [hid, e.inv_hom_id]
  rw [hp]
  infer_instance

end ArithmeticThetaAlgebraicCoordinatesR0143
#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_exact_poles
