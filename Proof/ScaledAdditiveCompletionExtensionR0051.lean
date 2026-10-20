module

public import ScaledNormalRecoveryDefinitionsR0051
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

/-! Additive extension along the actual rescaled adic filtrations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaScaledNormalRecoveryR0051

section General
variable {A B : Type*} [CommRing A] [CommRing B]
variable (I : Ideal A) (J : Ideal B) (r : ℕ) (p : A →+ B)
variable (hp : ∀ n a, a ∈ I ^ (r * n) → p a ∈ J ^ n)

private def additiveStage (n : ℕ) :
    A ⧸ (I ^ (r * n) • ⊤ : Ideal A) →+ B ⧸ (J ^ n • ⊤ : Ideal B) :=
  QuotientAddGroup.lift (I ^ (r * n) • ⊤ : Ideal A).toAddSubgroup
    ((J ^ n • ⊤ : Ideal B).mkQ.toAddMonoidHom.comp p) (by
      intro a ha
      change Submodule.Quotient.mk (p a) = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      have ha' : a ∈ I ^ (r * n) := by simpa using ha
      simpa using hp n a ha')

private lemma additiveStage_mk (n : ℕ) (a : A) :
    additiveStage I J r p hp n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (p a) := rfl

private def additiveCompletion : AdicCompletion I A →+ AdicCompletion J B where
  toFun z := ⟨fun n => additiveStage I J r p hp n (z.val (r * n)), by
    intro m n hmn
    have hmaps :
        (AdicCompletion.transitionMap J B hmn).toAddMonoidHom.comp
          (additiveStage I J r p hp n) =
        (additiveStage I J r p hp m).comp
          (AdicCompletion.transitionMap I A (Nat.mul_le_mul_left r hmn)).toAddMonoidHom := by
      ext a
      induction a using Submodule.Quotient.induction_on with
      | _ a => rfl
    exact (DFunLike.congr_fun hmaps (z.val (r * n))).trans
      (congrArg (additiveStage I J r p hp m) (z.property (Nat.mul_le_mul_left r hmn)))⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact (additiveStage I J r p hp n).map_zero
  map_add' z w := by
    apply Subtype.ext
    funext n
    exact (additiveStage I J r p hp n).map_add _ _

private lemma additiveCompletion_of (a : A) :
    additiveCompletion I J r p hp (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion J B) (p a) := by
  apply Subtype.ext
  funext n
  rfl

private lemma completedPower_iff (K : Ideal A) (hK : K.FG) (n : ℕ)
    (z : AdicCompletion K A) :
    z ∈ (K.map (algebraMap A (AdicCompletion K A))) ^ n ↔ z.val n = 0 := by
  rw [← Ideal.map_pow]
  change z ∈ (Ideal.map (algebraMap A (AdicCompletion K A)) (K ^ n)).restrictScalars A ↔ _
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hK]
  rfl

private lemma additiveCompletion_filtered (hI : I.FG) (hJ : J.FG) (n : ℕ)
    (z : AdicCompletion I A)
    (hz : z ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ (r * n)) :
    additiveCompletion I J r p hp z ∈ (J.map (algebraMap B (AdicCompletion J B))) ^ n := by
  apply (completedPower_iff J hJ n _).2
  change additiveStage I J r p hp n (z.val (r * n)) = 0
  rw [(completedPower_iff I hI (r * n) z).1 hz, map_zero]
end General

/-- Every backward filtered additive map extends, with whole-node agreement and
with the estimate on the actual powers of the completed ideals. -/
theorem additive_extension_exists :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      ∀ p : (ArithmeticThetaNodeCharts.Node k →+ ArithmeticThetaScaledTateBridgeR0046.Node k r),
      BackwardFiltered k r p →
      ∃ P : (ArithmeticThetaNodeCharts.CompletedNode k →+ ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r),
        AdditiveExtension k r p P := by
  intro k _ _ r _hr p hp
  let I := ArithmeticThetaNodeCharts.nodeIdeal k
  let J := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r
  refine ⟨additiveCompletion I J r p hp, ?_, ?_⟩
  · intro b
    exact additiveCompletion_of I J r p hp b
  · intro n b hb
    have hI : I.FG := Submodule.fg_span (by simp)
    have hJ : J.FG := Submodule.fg_span (by simp)
    have hi : I.map (algebraMap _ (AdicCompletion I (ArithmeticThetaNodeCharts.Node k))) =
        ArithmeticThetaNodeCharts.completedIdeal k := by
      simp [I, ArithmeticThetaNodeCharts.nodeIdeal, ArithmeticThetaNodeCharts.completedIdeal,
        ArithmeticThetaNodeCharts.toCompleted, Ideal.map_span]
      rfl
    have hj : (J.map (algebraMap _ (AdicCompletion J (ArithmeticThetaScaledTateBridgeR0046.Node k r)))) ^ n =
        ArithmeticThetaScaledTateBridgeR0046.completedPower k r n := by
      simp [J, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
        ArithmeticThetaScaledTateBridgeR0046.completedPower,
        ArithmeticThetaScaledTateBridgeR0046.completedParameter,
        ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
      rfl
    rw [← hj]
    apply additiveCompletion_filtered I J r p hp hI hJ n b
    rwa [hi]

end ArithmeticThetaScaledNormalRecoveryR0051
