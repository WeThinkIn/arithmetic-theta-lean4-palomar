import CyclicConstantDefinitionsR0088

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaCyclicConstantsR0088

open ArithmeticThetaAnnularTorsionPrereqR0053

variable (k : Type u) [Field k] [CharZero k]

private lemma chart_tau_ne_zero :
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
    ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

private lemma chart_to_generic_injective :
    Function.Injective (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) := by
  letI : IsDomain (ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  exact IsLocalization.injective (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))

private lemma chart_base_injective :
    Function.Injective (ArithmeticThetaAnnularTorsionPrereqR0053.base k) := by
  let σ := ArithmeticThetaScaledAnnularR0050.specialization k 1 0
    (by omega) (by omega) (1 : k) (by simp)
  intro a b hab
  have hleft (x : PowerSeries k) :
      σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k x) = x := by
    simpa [σ, ArithmeticThetaAnnularTorsionPrereqR0053.base] using
      (ArithmeticThetaScaledAnnularR0050.specialization_base k 1 0
        (by omega) (by omega) (1 : k) (by simp) x)
  exact (hleft a).symm.trans ((congrArg σ hab).trans (hleft b))

private lemma scalar_base_injective :
    Function.Injective (scalarBase k) := by
  have hbase : Function.Injective (ArithmeticThetaAnnularTorsionPrereqR0053.base k) :=
    chart_base_injective k
  have hgeneric : Function.Injective
      (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) :=
    chart_to_generic_injective k
  have hchart : Function.Injective
      ((ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k).comp
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k)) :=
    hgeneric.comp hbase
  exact (IsFractionRing.injective
    (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
    (FunctionField k)).comp hchart

theorem laurent_scalar_graph :
    ∃! F : LaurentSeries k →+* FunctionField k,
      (∀ a : PowerSeries k,
        F (algebraMap (PowerSeries k) (LaurentSeries k) a) = scalarBase k a) ∧
      (∀ (c : LaurentSeries k) (v : FunctionField k),
        ScalarValue k c v ↔ F c = v) := by
  have hg : Function.Injective (scalarBase k) := scalar_base_injective k
  let F : LaurentSeries k →+* FunctionField k :=
    IsFractionRing.lift (A := PowerSeries k) (K := LaurentSeries k)
      (L := FunctionField k) (g := scalarBase k) hg
  have hFbase : ∀ a : PowerSeries k,
      F (algebraMap (PowerSeries k) (LaurentSeries k) a) = scalarBase k a := by
    intro a
    exact IsFractionRing.lift_algebraMap (A := PowerSeries k) (K := LaurentSeries k)
      (L := FunctionField k) (g := scalarBase k) hg a
  have hFt : F (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) =
      fieldParameter k := by
    simpa [fieldParameter] using hFbase PowerSeries.X
  have hfieldParameter_ne : fieldParameter k ≠ 0 := by
    intro h
    exact PowerSeries.X_ne_zero (hg (by simpa [fieldParameter] using h))
  have hgraph : ∀ (c : LaurentSeries k) (v : FunctionField k),
      ScalarValue k c v ↔ F c = v := by
    intro c v
    constructor
    · rintro ⟨n, a, hca, hav⟩
      have hmap : F c * fieldParameter k ^ n = scalarBase k a := by
        calc
          F c * fieldParameter k ^ n =
              F c * F (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n := by
                rw [hFt]
          _ = F (c * (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n) := by
                rw [← F.map_pow, ← F.map_mul]
          _ = F (algebraMap (PowerSeries k) (LaurentSeries k) a) := by rw [hca]
          _ = scalarBase k a := hFbase a
      apply mul_right_cancel₀ (pow_ne_zero n hfieldParameter_ne)
      exact hmap.trans hav.symm
    · intro hFc
      obtain ⟨n, a, hca⟩ :=
        IsLocalization.Away.surj (R := PowerSeries k) (S := LaurentSeries k)
          PowerSeries.X c
      refine ⟨n, a, hca, ?_⟩
      have hmap : F c * fieldParameter k ^ n = scalarBase k a := by
        calc
          F c * fieldParameter k ^ n =
              F c * F (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n := by
                rw [hFt]
          _ = F (c * (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n) := by
                rw [← F.map_pow, ← F.map_mul]
          _ = F (algebraMap (PowerSeries k) (LaurentSeries k) a) := by rw [hca]
          _ = scalarBase k a := hFbase a
      simpa [hFc] using hmap
  refine ⟨F, ⟨hFbase, hgraph⟩, ?_⟩
  intro G hG
  apply IsFractionRing.ringHom_ext (A := PowerSeries k) (K := LaurentSeries k)
    (L := FunctionField k)
  intro a
  exact (hG.1 a).trans (hFbase a).symm

end ArithmeticThetaCyclicConstantsR0088
