module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

/-! The height-one intersection theorem for Noetherian normal domains. -/
namespace ArithmeticThetaSectionCompletion

universe u v

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]

/-- The ideal of denominators clearing a fraction into the base ring. -/
def denominatorIdeal (x : K) : Ideal R where
  carrier := {b | ∃ a : R, x * algebraMap R K b = algebraMap R K a}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro b c ⟨a, ha⟩ ⟨d, hd⟩
    exact ⟨a + d, by simp [map_add, mul_add, ha, hd]⟩
  smul_mem' := by
    rintro r b ⟨a, ha⟩
    refine ⟨r * a, ?_⟩
    simp only [smul_eq_mul, map_mul]
    calc
      x * (algebraMap R K r * algebraMap R K b) =
          algebraMap R K r * (x * algebraMap R K b) := by ring
      _ = _ := by rw [ha]

lemma denominatorIdeal_eq_top_iff (x : K) :
    denominatorIdeal (R := R) x = ⊤ ↔ ∃ a : R, algebraMap R K a = x := by
  rw [Ideal.eq_top_iff_one]
  change (∃ a : R, x * algebraMap R K 1 = algebraMap R K a) ↔ _
  simp only [map_one, mul_one]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

lemma denominatorIdeal_le_mul (x : K) (r : R) :
    denominatorIdeal (R := R) x ≤ denominatorIdeal (algebraMap R K r * x) := by
  rintro b ⟨a, ha⟩
  exact ⟨r * a, by simp only [map_mul]; rw [mul_assoc, ha]⟩

/-- Fractions regular at every height-one prime, in denominator form. -/
def regularAtHeightOne (x : K) : Prop :=
  ∀ (p : Ideal R), p.IsPrime → p.height = 1 →
    ∃ a b : R, b ∉ p ∧ x * algebraMap R K b = algebraMap R K a

lemma regularAtHeightOne_mul {x : K} (hx : regularAtHeightOne (R := R) x) (r : R) :
    regularAtHeightOne (R := R) (algebraMap R K r * x) := by
  intro p hp hh
  obtain ⟨a, b, hb, hab⟩ := hx p hp hh
  exact ⟨r * a, b, hb, by simp only [map_mul]; rw [mul_assoc, hab]⟩

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K]

/-- A prime proper denominator ideal has height one in a Noetherian normal domain. -/
lemma prime_denominatorIdeal_height (x : K)
    (hp : (denominatorIdeal (R := R) x).IsPrime) :
    (denominatorIdeal (R := R) x).height = 1 := by
  let p := denominatorIdeal (R := R) x
  have hinj := IsFractionRing.injective R K
  have hp0 : p ≠ ⊥ := by
    obtain ⟨a, b, hb⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
    have heq : x * algebraMap R K (b : R) = algebraMap R K a := by
      rw [← hb, IsLocalization.mk'_spec]
    intro hzero
    have : (b : R) = 0 := by
      have : (b : R) ∈ p := ⟨a, heq⟩
      simpa only [hzero, Ideal.mem_bot] using this
    exact (nonZeroDivisors.ne_zero b.property) this
  have hnot : ¬ ∀ b ∈ p, ∃ a ∈ p, x * algebraMap R K b = algebraMap R K a := by
    intro hstable
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) p
    have hN : N ≠ ⊥ := by
      intro hzero
      apply hp0
      apply le_antisymm _ bot_le
      intro b hb
      have : algebraMap R K b ∈ N := Submodule.mem_map.mpr ⟨b, hb, rfl⟩
      rw [hzero, Submodule.mem_bot] at this
      exact (show b = 0 from hinj (by simpa using this))
    have hi : IsIntegral R x := isIntegral_of_smul_mem_submodule N hN
      ((IsNoetherian.noetherian p).map _) x (by
        rintro z ⟨b, hb, rfl⟩
        obtain ⟨a, ha, he⟩ := hstable b hb
        exact Submodule.mem_map.mpr ⟨a, ha, he.symm⟩)
    exact hp.ne_top ((denominatorIdeal_eq_top_iff x).mpr
      (IsIntegrallyClosed.algebraMap_eq_of_integral hi))
  push Not at hnot
  obtain ⟨b, hb, hbad⟩ := hnot
  have hbmem := hb
  obtain ⟨a, ha⟩ := hb
  have han : a ∉ p := fun hap => hbad a hap ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : a = 0 := hinj (by simpa using ha.symm)
    exact han (this ▸ p.zero_mem)
  have hmin : p ∈ (Ideal.span {b}).minimalPrimes := by
    refine ⟨⟨hp, Ideal.span_le.mpr (by simpa using hbmem)⟩, ?_⟩
    intro q hq hqp c hc
    obtain ⟨d, hd⟩ := hc
    have he : a * c = b * d := hinj (by
      simp only [map_mul]
      rw [← ha, ← hd]
      ring)
    have hac : a * c ∈ q := he ▸ q.mul_mem_right d
      (hq.2 (Ideal.subset_span (Set.mem_singleton b)))
    exact (hq.1.mem_or_mem hac).resolve_left (fun h => han (hqp h))
  apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hmin)
  exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp0)

/-- A Noetherian normal domain is the intersection of its height-one localizations
inside its actual fraction field. -/
theorem normal_domain_height_one_intersection :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] (g : K),
      (∀ (p : Ideal R), p.IsPrime → p.height = 1 →
        ∃ a b : R, b ∉ p ∧ g * algebraMap R K b = algebraMap R K a) →
      ∃ a : R, algebraMap R K a = g := by
  intro R _ _ _ _ K _ _ _ g hg
  by_contra hbad
  let S : Set (Ideal R) := {p | p ≠ ⊤ ∧
    ∃ x : K, regularAtHeightOne (R := R) x ∧ p = denominatorIdeal x}
  obtain ⟨p, ⟨hp, x, hx, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherianRing R) S
      ⟨denominatorIdeal g, (denominatorIdeal_eq_top_iff g).not.mpr hbad, g, hg, rfl⟩
  have hprime : (denominatorIdeal (R := R) x).IsPrime := by
    refine ⟨hp, ?_⟩
    intro a b hab
    rw [or_iff_not_imp_left]
    intro ha
    have hproper : denominatorIdeal (R := R) (algebraMap R K a * x) ≠ ⊤ := by
      rw [ne_eq, denominatorIdeal_eq_top_iff]
      rintro ⟨c, hc⟩
      exact ha ⟨c, by rw [mul_comm]; exact hc.symm⟩
    have heq := (denominatorIdeal_le_mul x a).eq_of_not_lt
      (hmax _ ⟨hproper, algebraMap R K a * x, regularAtHeightOne_mul hx a, rfl⟩)
    rw [heq]
    obtain ⟨c, hc⟩ := hab
    exact ⟨c, by rw [← hc, map_mul]; ring⟩
  obtain ⟨a, b, hb, heq⟩ := hx _ hprime (prime_denominatorIdeal_height x hprime)
  exact hb ⟨a, heq⟩

end ArithmeticThetaSectionCompletion
