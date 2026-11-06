module

public import TateNodeNormalForm
public import TateNodeTorusCharts
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

@[expose] public section

/-!
Regularity and normality of the algebraic node.
The auxiliary crossing presentation below is definitionally the supplied Node.
General local-height, branch-kernel and Nagata arguments are adapted from
fermats-last-theorem/P2M/Sol/S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible.lean
and S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime.lean.
They are included as source and checked here without the P2M export machinery.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
universe u
namespace ArithmeticThetaAnnularGeometry
namespace AlgebraicNodeSupport

open MvPolynomial

namespace CrossingPresentation

variable (W : Type*) [CommRing W]

abbrev CrossingQuotient (t : W) : Type _ :=
  MvPolynomial (Fin 2) W ⧸ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}

variable {W}

namespace CrossingQuotient

variable (t : W)

abbrev mk : MvPolynomial (Fin 2) W →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.mkₐ W (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)})

theorem mk_apply (p : MvPolynomial (Fin 2) W) :
    mk t p = Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) p := rfl

theorem mk_surjective : Function.Surjective (mk t) := Ideal.Quotient.mkₐ_surjective W _

theorem mk_X_mul_mk_X : mk t (X 0) * mk t (X 1) = algebraMap W (CrossingQuotient W t) t := by
  rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl


end CrossingQuotient
end CrossingPresentation
open CrossingPresentation IsLocalRing

namespace CrossingResolutionR1

noncomputable section

section General

variable {A : Type*} [CommRing A]

theorem isRegularRing_localization [IsRegularRing A] (M : Submonoid A) :
    IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro q hq
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

theorem isRegularLocalRing_atPrime_of_disjoint (M : Submonoid A) [IsRegularRing (Localization M)]
    (P : Ideal A) [hP : P.IsPrime] (h : Disjoint (M : Set A) (P : Set A)) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  set Q : Ideal (Localization M) := P.map (algebraMap A (Localization M)) with hQdef
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP h
  have hc : Q.comap (algebraMap A (Localization M)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP h
  have hM : (Q.comap (algebraMap A (Localization M))).primeCompl = P.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  have : IsLocalization P.primeCompl (Localization.AtPrime Q) := by
    rw [← hM]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q) Q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime P)).toRingEquiv

variable [IsNoetherianRing A]

theorem isRegularLocalRing_of_span_eq (P : Ideal A) [P.IsPrime] (S : Finset A)
    (hS : Ideal.span (S : Set A) = P) (h : (S.card : ℕ∞) ≤ P.height) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  subst hS
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.span (S : Set A))
    (Localization.AtPrime (Ideal.span (S : Set A))),
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
  have hfin : ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A)).Finite := S.finite_toSet.image _
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime
    (Ideal.span (S : Set A))) hfin
  have h2 : ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A)).ncard ≤ S.card := by
    calc _ ≤ (S : Set A).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  have h3 : ((Ideal.span ((algebraMap A (Localization.AtPrime (Ideal.span (S : Set A)))) ''
      (S : Set A))).spanFinrank : ℕ∞) ≤ (Ideal.span (S : Set A)).height :=
    le_trans (by exact_mod_cast h1.trans h2) h
  exact_mod_cast (WithBot.coe_le_coe.mpr h3)

theorem one_le_height_of_bot_lt [IsDomain A] (P : Ideal A) [P.IsPrime] (hP : ⊥ < P) :
    (1 : ℕ∞) ≤ P.height := by
  have h := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := (⊥ : Ideal A)) (J := P) hP
  rw [Ideal.height_bot] at h
  exact Order.one_le_iff_pos.mpr h

theorem two_le_height_of_lt_of_lt [IsDomain A] (Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hQ : ⊥ < Q) (hQP : Q < P) : (2 : ℕ∞) ≤ P.height := by
  have h1 := one_le_height_of_bot_lt Q hQ
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQP
  have h12 : (1 : ℕ∞) < P.height := lt_of_le_of_lt h1 h2
  have := Order.add_one_le_of_lt h12
  simpa [one_add_one_eq_two] using this

theorem isRegularLocalRing_of_mem_of_ker_eq_span [IsDomain A] {D : Type*} [CommRing D]
    [IsDomain D] [IsPrincipalIdealRing D] (ρ : A →+* D) (hρ : Function.Surjective ρ)
    {z : A} (hz : z ≠ 0) (hker : RingHom.ker ρ = Ideal.span {z})
    (P : Ideal A) [hP : P.IsPrime] (hzP : z ∈ P) : IsRegularLocalRing (Localization.AtPrime P) := by
  classical
  have hkerP : RingHom.ker ρ ≤ P := by
    rw [hker, Ideal.span_singleton_le_iff_mem]; exact hzP

  have hzprime : (Ideal.span {z} : Ideal A).IsPrime := by
    rw [← hker]; exact RingHom.ker_isPrime ρ
  have hbot : (⊥ : Ideal A) < Ideal.span {z} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]; exact hz

  have hmapP : (P.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρ hkerP
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.map ρ)).principal
  obtain ⟨G, rfl⟩ := hρ g
  have hPeq : P = Ideal.span {z, G} := by
    have h1 : P = (P.map ρ).comap ρ := by
      rw [Ideal.comap_map_of_surjective _ hρ, ← RingHom.ker_eq_comap_bot,
        left_eq_sup]; exact hkerP
    have h2 : (P.map ρ) = (Ideal.span {G}).map ρ := by
      rw [hg, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]
    rw [h1, h2, Ideal.comap_map_of_surjective _ hρ, ← RingHom.ker_eq_comap_bot, hker,
      ← Ideal.span_union, Set.union_singleton]
  by_cases hPz : P = Ideal.span {z}
  ·
    have hreg := isRegularLocalRing_of_span_eq (Ideal.span {z}) {z} (by simp)
      (by simpa using one_le_height_of_bot_lt (Ideal.span {z}) hbot)
    subst hPz
    exact hreg
  ·
    have hlt : Ideal.span {z} < P :=
      lt_of_le_of_ne (by rw [Ideal.span_singleton_le_iff_mem]; exact hzP) (Ne.symm hPz)
    have h2 := two_le_height_of_lt_of_lt (Ideal.span {z}) P hbot hlt
    refine isRegularLocalRing_of_span_eq P {z, G} (by rw [hPeq]; simp) ?_
    exact le_trans (by exact_mod_cast Finset.card_le_two) h2

end General

section Chart

variable {R : Type*} [CommRing R] (t : R)

open CrossingPresentation.CrossingQuotient

local notation "𝔵" => (CrossingPresentation.CrossingQuotient.mk t (MvPolynomial.X 0))

local notation "𝔶" => (CrossingPresentation.CrossingQuotient.mk t (MvPolynomial.X 1))

abbrev rel : MvPolynomial (Fin 2) R := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t

theorem xy_eq : 𝔵 * 𝔶 = algebraMap R (CrossingQuotient R t) t := mk_X_mul_mk_X t

theorem mk_C (a : R) : mk t (MvPolynomial.C a) = algebraMap R (CrossingQuotient R t) a := by
  change mk t (algebraMap R (MvPolynomial (Fin 2) R) a) = _
  exact AlgHom.commutes _ a

theorem exists_normalForm (f : CrossingQuotient R t) :
    ∃ p q : Polynomial R, f = Polynomial.aeval 𝔵 p + 𝔶 * Polynomial.aeval 𝔶 q := by
  obtain ⟨F, rfl⟩ := mk_surjective t f
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Polynomial.C a, 0, ?_⟩
    simp only [Polynomial.aeval_C, map_zero, mul_zero, add_zero]
    exact mk_C t a
  | add p q hp hq =>
    obtain ⟨p₁, q₁, h₁⟩ := hp
    obtain ⟨p₂, q₂, h₂⟩ := hq
    refine ⟨p₁ + p₂, q₁ + q₂, ?_⟩
    rw [map_add, h₁, h₂, map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hPQ⟩ := hp
    have hxy := xy_eq t
    fin_cases i
    ·
      refine ⟨Polynomial.X * P + Polynomial.C (t * Q.coeff 0), Polynomial.C t * Q.divX, ?_⟩
      have hQ : Polynomial.aeval 𝔶 Q = 𝔶 * Polynomial.aeval 𝔶 Q.divX +
          algebraMap R _ (Q.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hQ]
      linear_combination (Polynomial.aeval 𝔶 Q.divX * 𝔶 + (algebraMap R _ (Q.coeff 0))) * hxy
    ·
      refine ⟨Polynomial.C t * P.divX, Polynomial.C (P.coeff 0) + Polynomial.X * Q, ?_⟩
      have hP : Polynomial.aeval 𝔵 P = 𝔵 * Polynomial.aeval 𝔵 P.divX +
          algebraMap R _ (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.mk_one, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hP]
      linear_combination (Polynomial.aeval 𝔵 P.divX) * hxy

abbrev Resid : Type _ := R ⧸ Ideal.span ({t} : Set R)

theorem algebraMap_resid_t : algebraMap R (Polynomial (Resid t)) t = 0 := by
  rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t), map_zero]

noncomputable def branchY : CrossingQuotient R t →ₐ[R] Polynomial (Resid t) :=
  Ideal.Quotient.liftₐ (Ideal.span {rel t})
    (MvPolynomial.aeval ![(0 : Polynomial (Resid t)), Polynomial.X]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [algebraMap_resid_t t])

noncomputable def branchX : CrossingQuotient R t →ₐ[R] Polynomial (Resid t) :=
  Ideal.Quotient.liftₐ (Ideal.span {rel t})
    (MvPolynomial.aeval ![Polynomial.X, (0 : Polynomial (Resid t))]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [algebraMap_resid_t t])

theorem branchY_mk (F : MvPolynomial (Fin 2) R) :
    branchY t (mk t F) = MvPolynomial.aeval ![(0 : Polynomial (Resid t)), Polynomial.X] F := rfl

theorem branchX_mk (F : MvPolynomial (Fin 2) R) :
    branchX t (mk t F) = MvPolynomial.aeval ![Polynomial.X, (0 : Polynomial (Resid t))] F := rfl

@[scoped simp] theorem branchY_x : branchY t 𝔵 = 0 := by
  rw [branchY_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchY_y : branchY t 𝔶 = Polynomial.X := by
  rw [branchY_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchX_x : branchX t 𝔵 = Polynomial.X := by
  rw [branchX_mk, MvPolynomial.aeval_X]; rfl

@[scoped simp] theorem branchX_y : branchX t 𝔶 = 0 := by
  rw [branchX_mk, MvPolynomial.aeval_X]; rfl

theorem branchY_aeval_x (p : Polynomial R) :
    branchY t (Polynomial.aeval 𝔵 p) = Polynomial.C (algebraMap R (Resid t) (p.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_x, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_aeval_y (q : Polynomial R) :
    branchY t (Polynomial.aeval 𝔶 q) = q.map (algebraMap R (Resid t)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_y, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_x (p : Polynomial R) :
    branchX t (Polynomial.aeval 𝔵 p) = p.map (algebraMap R (Resid t)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_x, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_y (q : Polynomial R) :
    branchX t (Polynomial.aeval 𝔶 q) = Polynomial.C (algebraMap R (Resid t) (q.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_y, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_surjective : Function.Surjective (branchY t) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap R (Resid t))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval 𝔶 G, by rw [branchY_aeval_y, hG]⟩

theorem branchX_surjective : Function.Surjective (branchX t) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap R (Resid t))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval 𝔵 G, by rw [branchX_aeval_x, hG]⟩

theorem exists_eq_C_mul_of_map_eq_zero {q : Polynomial R} (hq : q.map (algebraMap R (Resid t)) = 0) :
    ∃ q' : Polynomial R, q' * Polynomial.C t = q := by
  have : q ∈ RingHom.ker (Polynomial.mapRingHom (algebraMap R (Resid t))) := hq
  rw [Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.map_span,
    Set.image_singleton] at this
  exact Ideal.mem_span_singleton'.mp this

theorem ker_branchY : RingHom.ker (branchY t) = Ideal.span {𝔵} := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm t f
    rw [map_add, map_mul, branchY_aeval_x, branchY_y, branchY_aeval_y] at hf
    have hq : q.map (algebraMap R (Resid t)) = 0 := by
      ext n
      have := congrArg (fun g => Polynomial.coeff g (n+1)) hf
      simpa [Polynomial.coeff_C, Polynomial.coeff_X_mul] using this
    have hp0 : algebraMap R (Resid t) (p.coeff 0) = 0 := by
      have := congrArg (fun g => Polynomial.coeff g 0) hf
      simpa [hq] using this
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hp0
    obtain ⟨a, ha⟩ := hp0
    obtain ⟨q', hq'⟩ := exists_eq_C_mul_of_map_eq_zero t hq
    have hP : Polynomial.aeval 𝔵 p = 𝔵 * Polynomial.aeval 𝔵 p.divX +
        algebraMap R _ (p.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [Ideal.mem_span_singleton']
    refine ⟨Polynomial.aeval 𝔵 p.divX + 𝔶 * algebraMap R _ a + 𝔶 * 𝔶 * Polynomial.aeval 𝔶 q',
      ?_⟩
    rw [hP, ← ha, ← hq', map_mul, map_mul, Polynomial.aeval_C]
    linear_combination (𝔶 * Polynomial.aeval 𝔶 q' + algebraMap R _ a) * xy_eq t
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchY_x]

theorem ker_branchX : RingHom.ker (branchX t) = Ideal.span {𝔶} := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm t f
    rw [map_add, map_mul, branchX_aeval_x, branchX_y, zero_mul, add_zero] at hf
    obtain ⟨p', hp'⟩ := exists_eq_C_mul_of_map_eq_zero t hf
    rw [Ideal.mem_span_singleton']
    refine ⟨𝔵 * Polynomial.aeval 𝔵 p' + Polynomial.aeval 𝔶 q, ?_⟩
    rw [← hp', map_mul, Polynomial.aeval_C]
    linear_combination (Polynomial.aeval 𝔵 p') * xy_eq t
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchX_y]

theorem x_ne_zero [Nontrivial (Resid t)] : (𝔵 : CrossingQuotient R t) ≠ 0 := by
  intro h
  have := congrArg (branchX t) h
  rw [branchX_x, map_zero] at this
  exact Polynomial.X_ne_zero this

theorem y_ne_zero [Nontrivial (Resid t)] : (𝔶 : CrossingQuotient R t) ≠ 0 := by
  intro h
  have := congrArg (branchY t) h
  rw [branchY_y, map_zero] at this
  exact Polynomial.X_ne_zero this


end Chart
end
end CrossingResolutionR1
namespace P2mNagata

open IsLocalization

variable {R : Type*} [CommRing R] [IsDomain R]

lemma pow_dvd_of_pow_dvd_mul_left {x r : R} (hx : Prime x) (hr : ¬x ∣ r) :
    ∀ (n : ℕ) (c : R), x ^ n ∣ r * c → x ^ n ∣ c := by
  intro n
  induction n with
  | zero => intro c _; simp
  | succ n ih =>
    intro c h
    have hxc : x ∣ c := by
      have : x ∣ r * c := (dvd_pow_self x n.succ_ne_zero).trans h
      exact (hx.dvd_or_dvd this).resolve_left hr
    obtain ⟨c', rfl⟩ := hxc
    rw [pow_succ, mul_left_comm] at h
    have h' : x ^ n ∣ r * c' := by
      obtain ⟨d, hd⟩ := h
      refine ⟨d, mul_left_cancel₀ hx.ne_zero ?_⟩
      rw [hd]; ring
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left x (ih c' h')

variable {x : R} (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]

lemma algebraMap_injective (hx0 : x ≠ 0) : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (M := Submonoid.powers x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)

lemma prime_of_prime_algebraMap (hx : Prime x) {r₀ : R} (hr₀ : ¬x ∣ r₀) (hunit : ¬IsUnit r₀)
    (hprime : Prime (algebraMap R S r₀)) : Prime r₀ := by
  have hinj := algebraMap_injective S hx.ne_zero
  refine ⟨fun h => hprime.ne_zero (by rw [h, map_zero]), hunit, fun a b hab => ?_⟩

  have key : ∀ a : R, algebraMap R S r₀ ∣ algebraMap R S a → r₀ ∣ a := by
    intro a ⟨d, hd⟩
    obtain ⟨c, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) d
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) x).mp s.2

    have h1 : algebraMap R S (a * x ^ n) = algebraMap R S (r₀ * c) := by
      rw [map_mul, map_mul, hd, hn, mul_assoc, IsLocalization.mk'_spec]
    have h2 : a * x ^ n = r₀ * c := hinj h1
    have h3 : x ^ n ∣ r₀ * c := ⟨a, by rw [← h2, mul_comm]⟩
    obtain ⟨c', rfl⟩ := pow_dvd_of_pow_dvd_mul_left hx hr₀ n c h3
    refine ⟨c', mul_right_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
    rw [h2]; ring
  have : algebraMap R S r₀ ∣ algebraMap R S a * algebraMap R S b := by
    rw [← map_mul]; exact map_dvd (algebraMap R S) hab
  rcases hprime.dvd_or_dvd this with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key b h)

theorem main [IsNoetherianRing R] (hx : Prime x) [IsDomain S] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R := by
  classical
  have hinj := algebraMap_injective S hx.ne_zero
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun P hP0 hP => ?_
  by_cases hxP : x ∈ P
  · exact ⟨x, hxP, hx⟩

  have hdisj : Disjoint (Submonoid.powers x : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hxP (hP.mem_of_pow_mem n hn)
  have hPS : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S P hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    intro h
    apply hP0
    rw [eq_bot_iff]
    intro r hr
    have : algebraMap R S r ∈ P.map (algebraMap R S) := Ideal.mem_map_of_mem _ hr
    rw [h, Ideal.mem_bot] at this
    exact (Ideal.mem_bot).mpr (hinj (by rw [this, map_zero]))
  obtain ⟨π, hπP, hπ⟩ :=
    (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp ‹_›) _ hPS0 hPS

  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) π
  have hunit_s : IsUnit (algebraMap R S s) := IsLocalization.map_units S s
  have hr_assoc : Associated (IsLocalization.mk' S r s) (algebraMap R S r) := by
    refine ⟨hunit_s.unit, ?_⟩
    rw [IsUnit.unit_spec, IsLocalization.mk'_spec]
  have hrS : Prime (algebraMap R S r) := hr_assoc.prime hπ
  have hrP : r ∈ P := by
    have hmem : algebraMap R S r ∈ P.map (algebraMap R S) := by
      have := Ideal.mul_mem_right (algebraMap R S s) _ hπP
      rwa [IsLocalization.mk'_spec] at this
    have : r ∈ (P.map (algebraMap R S)).under R := Ideal.mem_comap.mpr hmem
    rwa [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hP hdisj] at this
  have hr0 : r ≠ 0 := fun h => hrS.ne_zero (by rw [h, map_zero])

  obtain ⟨e, r₀, hxr₀, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hx.not_isUnit
  have hr₀P : r₀ ∈ P :=
    (hP.mem_or_mem hrP).resolve_left fun h => hxP (hP.mem_of_pow_mem e h)
  have hr₀S : Prime (algebraMap R S r₀) := by
    have hassoc : Associated (algebraMap R S (x ^ e * r₀)) (algebraMap R S r₀) := by
      refine ⟨((IsLocalization.map_units S
        (⟨x ^ e, (Submonoid.mem_powers_iff _ _).mpr ⟨e, rfl⟩⟩ : Submonoid.powers x)).unit)⁻¹, ?_⟩
      rw [map_mul, mul_comm (algebraMap R S (x ^ e)), mul_assoc, IsUnit.mul_val_inv, mul_one]
    exact hassoc.prime hrS
  have hr₀unit : ¬IsUnit r₀ := fun h => hP.ne_top (P.eq_top_of_isUnit_mem hr₀P h)
  exact ⟨r₀, hr₀P, prime_of_prime_algebraMap S hx hxr₀ hr₀unit hr₀S⟩

end P2mNagata


end AlgebraicNodeSupport

open ArithmeticThetaNodeCharts
open AlgebraicNodeSupport.CrossingResolutionR1

/-- The coefficient ring is a discrete valuation ring, and localization preserves
regularity of its one-variable polynomial ring. -/
theorem torus_regular (k : Type u) [Field k] : IsRegularRing (Torus k) := by
  let M := Submonoid.powers (Polynomial.X : Polynomial (Base k))
  have : IsRegularRing (Localization M) := isRegularRing_localization M
  exact IsRegularRing.of_ringEquiv (R := Localization M)
    (IsLocalization.algEquiv M (Localization M) (Torus k)).toRingEquiv

/-- The Laurent torus is factorial with its canonical polynomial localization. -/
theorem torus_factorial (k : Type u) [Field k] : UniqueFactorizationMonoid (Torus k) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial (Base k))) (Torus k)

/-- The branch supplies a prime coordinate and regularity at every prime on it. -/
theorem node_branch_regular_prime (k : Type u) [Field k] [CharZero k] :
    Prime (x k) ∧ ∀ (P : Ideal (Node k)) [P.IsPrime], x k ∈ P →
      IsRegularLocalRing (Localization.AtPrime P) := by
  have : IsDomain (Node k) := (node_flat_domain_parameter k).1
  have hmax : (Ideal.span ({parameter k} : Set (Base k))).IsMaximal := by
    have heq := (IsDiscreteValuationRing.irreducible_iff_uniformizer (parameter k)).mp
      (show Irreducible (parameter k) from PowerSeries.X_irreducible)
    rw [← heq]
    infer_instance
  let := hmax
  let : Field (Resid (parameter k)) := Ideal.Quotient.field _
  have hx : x k ≠ 0 := by
    intro h
    have ht := (node_flat_domain_parameter k).2.2.1
    apply ht
    rw [← node_xy, h, zero_mul]
  have hker : RingHom.ker (branchY (parameter k)) = Ideal.span {x k} :=
    ker_branchY (parameter k)
  have : (Ideal.span {x k}).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  refine ⟨(Ideal.span_singleton_prime hx).mp inferInstance, ?_⟩
  intro P hP hxP
  exact isRegularLocalRing_of_mem_of_ker_eq_span (A := Node k)
    (branchY (parameter k)).toRingHom (branchY_surjective (parameter k)) hx hker P hxP

/-- Regularity and normality of the actual total algebraic node. -/
theorem algebraic_node_regular_normal :
    ∀ (k : Type u) [Field k] [CharZero k],
      IsRegularRing (ArithmeticThetaNodeCharts.Node k) ∧
        IsIntegrallyClosed (ArithmeticThetaNodeCharts.Node k) := by
  intro k _ _
  have : IsDomain (Node k) := (node_flat_domain_parameter k).1
  obtain ⟨e, _, _⟩ := (node_torus_chart_equivalences k).1
  have : IsRegularRing (Torus k) := torus_regular k
  have : IsRegularRing (XChart k) :=
    @IsRegularRing.of_ringEquiv (Torus k) inferInstance (XChart k) inferInstance
      e.symm (torus_regular k)
  obtain ⟨hxprime, hbranch⟩ := node_branch_regular_prime k
  have hreg : IsRegularRing (Node k) := by
    rw [isRegularRing_iff]
    intro P hP
    by_cases hxP : x k ∈ P
    · exact hbranch P hxP
    · exact isRegularLocalRing_atPrime_of_disjoint (Submonoid.powers (x k)) P
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime (I := P) (x k)).mpr hxP)
  have : IsDomain (XChart k) := MulEquiv.isDomain (Torus k) e.toMulEquiv
  have : UniqueFactorizationMonoid (Torus k) := torus_factorial k
  have : UniqueFactorizationMonoid (XChart k) :=
    MulEquiv.uniqueFactorizationMonoid e.symm.toMulEquiv inferInstance
  have : UniqueFactorizationMonoid (Node k) :=
    AlgebraicNodeSupport.P2mNagata.main (XChart k) hxprime
  exact ⟨hreg, inferInstance⟩

end ArithmeticThetaAnnularGeometry
