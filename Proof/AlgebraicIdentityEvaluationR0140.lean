module

public import NormalizedIdentityFrameR0140
public import ThetaNumeratorIdentityValueR0140

@[expose] public section

/-! Actual algebraic identity evaluation from compatible finite reductions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140
namespace AlgebraicIdentityEvaluationR0140
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaIndexedOverlapsR0058 (nodeEquiv)
open ArithmeticThetaAnnularThetaR0128 (specialize)
variable (k : Type u) [Field k] [CharZero k]

lemma marked_base (n : ℕ) (c : R k n) :
    markedPoint k n 1 (base k n c) = c := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  change (MvPolynomial.eval₂Hom ((RingHom.id (R k n)).comp (trunc _ PowerSeries.X n))
    (fun j : Fin 2 => if j = 0 then (markedUnit k n 1 : R k n)
      else parameter k n * ↑((markedUnit k n 1)⁻¹))) (MvPolynomial.C f) = _
  simp [trunc]

lemma reduction_of (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1 a

lemma specialization_node (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    markedPoint k n 1 (trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a)) =
      trunc (PowerSeries k) PowerSeries.X n
        (ArithmeticThetaScaledTateCompletionExtensionR0048.nodeMap k 1 0
          (by decide) (by decide) 1 one_ne_zero a) := by
  have hh : (markedPoint k n 1).comp
      ((trunc _ (ArithmeticThetaNodeCharts.t k) n).comp (nodeEquiv k).toRingHom) =
      (trunc (PowerSeries k) PowerSeries.X n).comp
        (ArithmeticThetaScaledTateCompletionExtensionR0048.nodeMap k 1 0
          (by decide) (by decide) 1 one_ne_zero) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, markedPoint, mkPoint, nodeEquiv, trunc,
        ArithmeticThetaScaledTateCompletionExtensionR0048.nodeMap,
        ArithmeticThetaScaledTateCompletionExtensionR0048.baseMap]
    · intro j
      fin_cases j <;>
        simp [RingHom.comp_apply, markedPoint, mkPoint, nodeEquiv, trunc, markedUnit,
          parameter, ArithmeticThetaScaledTateCompletionExtensionR0048.nodeMap,
          ArithmeticThetaScaledTateCompletionExtensionR0048.baseMap]
  exact RingHom.congr_fun hh a

/-- Specializing the completed node at the identity commutes with every quotient. -/
lemma specialize_reduction (n : ℕ) (z : Hat k) :
    markedPoint k n 1 (completedReduction k n z) =
      trunc (PowerSeries k) PowerSeries.X n (specialize k 1 z) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (completedReduction k n z)
  let a' := (nodeEquiv k).symm a
  have hh : completedReduction k n z = completedReduction k n
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a') := by
    rw [reduction_of, show nodeEquiv k a' = a from (nodeEquiv k).apply_symm_apply a]
    exact ha.symm
  have hm := Ideal.Quotient.eq.mp
    ((Classical.choose (finite_stage_completion_comparison k n)).injective hh)
  have ht : specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      PowerSeries.X :=
    (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) 1 one_ne_zero).1
  have hmap : Ideal.map (specialize k 1)
      ((Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^(n+1)) =
      (Ideal.span {PowerSeries.X})^(n+1) := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, ht]
  have hs := Ideal.mem_map_of_mem (specialize k 1) hm
  rw [hmap, map_sub] at hs
  have he := Ideal.Quotient.eq.mpr hs
  change trunc (PowerSeries k) PowerSeries.X n (specialize k 1 z) =
    trunc (PowerSeries k) PowerSeries.X n
      (specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a')) at he
  rw [hh, reduction_of, specialization_node, he]
  rw [show specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a') =
      ArithmeticThetaScaledTateCompletionExtensionR0048.nodeMap k 1 0
        (by decide) (by decide) 1 one_ne_zero a' from
      ArithmeticThetaScaledAnnularR0050.specialization_node_agreement k 1 0
        (by decide) (by decide) 1 one_ne_zero a']

end AlgebraicIdentityEvaluationR0140

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open NormalizedIdentityFrameR0140
open AlgebraicIdentityEvaluationR0140

/-- Full identity value of any realized algebraic section in the normalized frame. -/
theorem algebraic_identity_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s), ∀ (e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s m), ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k (ArithmeticThetaGenericEvaluationR0140.thetaChartBound m hm he) M hM s hs m e → ∀ (b : ℕ) (w : Fin m → PowerSeries k) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s m), ArithmeticThetaIdentitySectionsR0138.Realizes k (hm := hm) he M s b w φ → PowerSeries.X^b * ArithmeticThetaGenericEvaluationR0140.frameValue k M s m e φ = PowerSeries.X^((2*m)^2) * (↑(ArithmeticThetaGenericEvaluationR0140.commonUnit k m hm) : PowerSeries k) * ∑ ν : Fin m, w ν * ArithmeticThetaSchrodingerR0119.unary k m ν := by
  intro k _ _ m hm he T M hM s hs e he' b w φ hφ
  rw [← theta_numerator_identity_value k m hm he w]
  apply AlgebraizedThetaSaturationR0138.powerSeries_ext
  intro n
  rw [map_mul, map_pow, he' φ n]
  rw [← specialize_reduction]
  obtain ⟨z, hz, hv⟩ := hφ n (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))
  obtain ⟨z', hz', hv'⟩ := AlgebraizedThetaSaturationR0138.algebraicFormal_realizes
    k (thetaChartBound m hm he) M hM s hs m φ n
      (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))
  let := algebraicChart_mono k (thetaChartBound m hm he) M hM s hs m n
  have hzz : z = z' := mono_app_injective
    (pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^m))) ⊤
      (hz.trans hz'.symm)
  dsimp only [pulledInclusion] at hv'
  rw [hzz, hv'] at hv
  erw [(Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply] at hv
  have hvv := congrArg (markedPoint k n 1) hv
  rw [map_mul] at hvv
  rw [marked_base] at hvv
  exact hvv

end ArithmeticThetaGenericEvaluationR0140
#print axioms ArithmeticThetaGenericEvaluationR0140.algebraic_identity_evaluation
