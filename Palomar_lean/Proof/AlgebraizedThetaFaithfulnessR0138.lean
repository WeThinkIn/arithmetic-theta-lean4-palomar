module

public import AlgebraizedThetaSectionsR0138
public import CompletedChartThetaIndependenceR0128

@[expose] public section

/-! Faithfulness of full theta coefficients for the actual identity-divisor dual. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace AlgebraizedThetaFaithfulnessR0138
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open AlgebraizedThetaSectionsR0138
variable (k : Type u) [Field k] [CharZero k]

/-- All infinitesimal reductions jointly detect a completed-node element. -/
lemma completedReduction_ext (f g : Hat k)
    (h : ∀ n, completedReduction k n f = completedReduction k n g) : f = g := by
  apply AdicCompletion.ext_evalₐ
  intro n
  let I := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1
  have hfg : I.FG := by
    exact Submodule.fg_span (by simp)
  have ht := (Classical.choose (finite_stage_completion_comparison k n)).injective (h n)
  have hm : f - g ∈ (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^(n+1) :=
    Ideal.Quotient.eq.mp ht
  have hmap : I.map (algebraMap _ (Hat k)) =
      Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k} := by
    rw [show I = Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1} from rfl,
      Ideal.map_span, Set.image_singleton]
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted]
  have hm' : f - g ∈ (I.map (algebraMap _ (Hat k)))^n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (hmap ▸ hm)
  rw [← ArithmeticThetaNodeCharts.completion_eval_kernel I hfg n] at hm'
  change AdicCompletion.evalₐ I n (f-g) = 0 at hm'
  exact sub_eq_zero.mp (by simpa only [map_sub] using hm')

/-- Cancellation is in the actual completed domain, including the vertical factor. -/
lemma thetaNumerator_injective (m : ℕ) (hm : 0 < m) (he : Even m)
    (i : Fin (2*m)) : Function.Injective (fun w => thetaNumerator k m hm he w i) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  letI : IsDomain (Hat k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by decide)).1
  have ht : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
    intro hz
    have h := (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) (1 : k) one_ne_zero).1
    rw [show ArithmeticThetaScaledAnnularR0050.tau k 1 = 0 from hz, map_zero] at h
    exact PowerSeries.X_ne_zero h.symm
  have hx : ArithmeticThetaAnnularTorsionPrereqR0053.cx k ≠ 0 := by
    intro hz
    have h := (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) (1 : k) one_ne_zero).2.1
    rw [show ArithmeticThetaScaledAnnularR0050.cx k 1 = 0 from hz, map_zero] at h
    simp at h
  intro w w' h
  unfold thetaNumerator at h
  have hu := mul_right_cancel₀
    (pow_ne_zero m (Units.ne_zero ((gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹))) h
  have hv := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ hx)) hu
  unfold ArithmeticThetaAnnularThetaR0128.uniformSection at hv
  have hc := mul_left_cancel₀ (pow_ne_zero _ ht) hv
  exact ArithmeticThetaAnnularThetaR0128.completed_chart_theta_independence k m he i.val hc

lemma realizes_reductions {m : ℕ} {hm : 0 < m} (he : Even m)
    {T : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (w : Fin m → PowerSeries k) (φ : Dual k M s m)
    (hφ : Realizes k (hm := hm) he M s 0 w φ) (h3 : 3 ≤ 2*m) (n : ℕ) :
    StageRealizes k (T.atlas n) m (finiteNumerator k m hm he w n)
      (reduceDual k h3 M hM s hs m n φ) := by
  have hc := theta_numerator_compatibility k m hm he T w
  let v : FormalNumerators k (T := T) m :=
    ⟨fun n => ⟨finiteNumerator k m hm he w n, hc.1 n⟩, hc.2⟩
  apply (realizes_iff_reductions k h3 M hM s hs m v φ).mp ?_ n
  intro N i
  obtain ⟨z, hz, hv⟩ := hφ N i
  refine ⟨z, hz, ?_⟩
  simp only [pow_zero, map_one, one_mul] at hv
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k N))).commRingCatIsoToRingEquiv.eq_symm_apply.mpr hv

end AlgebraizedThetaFaithfulnessR0138
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open AlgebraizedThetaFaithfulnessR0138

/-- Equality of actual algebraic dual-ideal sections is exactly equality of all
power-series coefficients, with no nonzero-vector hypothesis. -/
theorem algebraized_theta_faithfulness :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m),
    ∀ (T : Tower k (2*m) (Nat.mul_pos (by decide) hm)),
    ∀ (M : Model k T), IsModel k T M →
    ∀ (s : baseScheme k ⟶ M.X), MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s →
    ∀ (w w' : Fin m → PowerSeries k) (φ φ' : Dual k M s m),
    Realizes k (hm := hm) he M s 0 w φ → Realizes k (hm := hm) he M s 0 w' φ' →
    (φ = φ' ↔ w = w') := by
  intro k _ _ m hm he T M hM s hs w w' φ φ' hφ hφ'
  have h3 : 3 ≤ 2*m := by obtain ⟨a, ha⟩ := he; omega
  constructor
  · intro heq
    subst φ'
    apply thetaNumerator_injective k m hm he (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))
    apply completedReduction_ext
    intro n
    have hc := theta_numerator_compatibility k m hm he T w
    have hc' := theta_numerator_compatibility k m hm he T w'
    have h1 := (IdentityStageSectionRealizationR0138.realizes_iff k (2*m) n
      (Nat.mul_pos (by decide) hm) h3 (T.overlap_spec n) (T.atlas n) m
      ⟨_, hc.1 n⟩ _).mp (realizes_reductions k he M hM s hs w φ hφ h3 n)
    have h2 := (IdentityStageSectionRealizationR0138.realizes_iff k (2*m) n
      (Nat.mul_pos (by decide) hm) h3 (T.overlap_spec n) (T.atlas n) m
      ⟨_, hc'.1 n⟩ _).mp (realizes_reductions k he M hM s hs w' φ hφ' h3 n)
    exact congrFun (h1.symm.trans h2) _
  · intro hw
    subst w'
    obtain ⟨ψ, hψ, hu⟩ := algebraized_theta_sections k m hm he T M hM s hs w
    exact (hu φ hφ).trans (hu φ' hφ').symm

end ArithmeticThetaIdentitySectionsR0138
#print axioms ArithmeticThetaIdentitySectionsR0138.algebraized_theta_faithfulness
