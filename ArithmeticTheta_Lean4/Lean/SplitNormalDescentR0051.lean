import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

namespace ArithmeticThetaScaledNormalRecoveryR0051

universe u v

/-- A normal domain descends along a split linear ring embedding. -/
theorem normal_domain_of_split :
    ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsDomain S]
      [IsIntegrallyClosed S] (f : R →+* S) (p : S →+ R),
      (∀ a : R, p (f a) = a) →
      (∀ (a : R) (b : S), p (f a * b) = a * p b) →
      IsDomain R ∧ IsIntegrallyClosed R := by
  intro R S _ _ _ _ f p hpf hlin
  have hf : Function.Injective f := Function.LeftInverse.injective hpf
  letI : IsDomain R := Function.Injective.isDomain f hf
  constructor
  · infer_instance
  · rw [isIntegrallyClosed_iff (FractionRing R)]
    intro x hx
    let g : R →+* FractionRing S := (algebraMap S (FractionRing S)).comp f
    have hg : Function.Injective g :=
      (IsFractionRing.injective S (FractionRing S)).comp hf
    let q : FractionRing R →+* FractionRing S := IsFractionRing.lift hg
    have hq_alg : (algebraMap S (FractionRing S)).comp f =
        q.comp (algebraMap R (FractionRing R)) := by
      ext r
      simp [q, g, IsFractionRing.lift_algebraMap]
    have hqx : IsIntegral S (q x) :=
      IsIntegral.map_of_comp_eq f q hq_alg hx
    obtain ⟨s, hs⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hqx
    obtain ⟨a, b, hb, hxab⟩ := IsFractionRing.div_surjective R x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hfb0 : f b ≠ 0 := by
      intro h
      apply hb0
      apply hf
      simpa using h
    have hmf_b : algebraMap S (FractionRing S) (f b) ≠ 0 := by
      intro h
      apply hfb0
      apply IsFractionRing.injective S (FractionRing S)
      simpa using h
    have hfrac : algebraMap S (FractionRing S) (f a) /
        algebraMap S (FractionRing S) (f b) =
        algebraMap S (FractionRing S) s := by
      calc
        algebraMap S (FractionRing S) (f a) /
            algebraMap S (FractionRing S) (f b) =
            q (algebraMap R (FractionRing R) a /
              algebraMap R (FractionRing R) b) := by
              simp [q, g, IsFractionRing.lift_algebraMap]
        _ = q x := by rw [hxab]
        _ = algebraMap S (FractionRing S) s := hs.symm
    have hafs : f a = s * f b := by
      apply IsFractionRing.injective S (FractionRing S)
      rw [map_mul]
      exact (div_eq_iff hmf_b).mp hfrac
    have hab : a = b * p s := by
      calc
        a = p (f a) := (hpf a).symm
        _ = p (s * f b) := by rw [hafs]
        _ = p (f b * s) := by rw [mul_comm]
        _ = b * p s := hlin b s
    have hmb : algebraMap R (FractionRing R) b ≠ 0 := by
      intro h
      apply hb0
      apply IsFractionRing.injective R (FractionRing R)
      simpa using h
    refine ⟨p s, ?_⟩
    rw [← hxab]
    apply (eq_div_iff hmb).mpr
    rw [← map_mul, hab]
    ac_rfl

end ArithmeticThetaScaledNormalRecoveryR0051
