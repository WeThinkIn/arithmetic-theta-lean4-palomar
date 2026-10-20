module

public import CompletedSectionKernelsR0053
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Horizontal Cartier equations split into the actual continuous sections. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularTorsionPrereqR0053

private lemma horizontal_factorization (k : Type u) [Field k] [CharZero k]
    (side : Bool) (c : ℕ) (ζ : k) (hc : 0 < c) (hζ : IsPrimitiveRoot ζ c) :
    (∏ b : Fin c, sectionEquation k side (ζ ^ b.val)) = coord k side ^ c - 1 := by
  have hp := X_pow_sub_C_eq_prod hζ hc (one_pow c : (1 : k) ^ c = 1)
  have he := congrArg (Polynomial.eval₂RingHom ((base k).comp PowerSeries.C)
    (coord k side)) hp
  simpa [sectionEquation, Polynomial.eval₂_pow, ← Fin.prod_univ_eq_prod_range] using he.symm

private lemma section_pairwise (k : Type u) [Field k] [CharZero k]
    (side : Bool) (c : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ c) :
    ∀ b d : Fin c, b ≠ d →
      sectionIdeal k side (ζ ^ b.val) ⊔ sectionIdeal k side (ζ ^ d.val) = ⊤ := by
  intro b d hbd
  have hne : ζ ^ b.val - ζ ^ d.val ≠ 0 := by
    intro h
    exact hbd (Fin.ext (hζ.pow_inj b.isLt d.isLt (sub_eq_zero.mp h)))
  let J := sectionIdeal k side (ζ ^ b.val) ⊔ sectionIdeal k side (ζ ^ d.val)
  have hb : sectionEquation k side (ζ ^ b.val) ∈ J :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hd : sectionEquation k side (ζ ^ d.val) ∈ J :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hm : base k (PowerSeries.C (ζ ^ b.val - ζ ^ d.val)) ∈ J := by
    convert J.sub_mem hd hb using 1
    simp only [sectionEquation, map_sub]
    ring
  exact J.eq_top_of_isUnit_mem hm
    (((isUnit_iff_ne_zero.mpr hne).map PowerSeries.C).map (base k))

theorem horizontal_split_reduced :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (c : ℕ) (ζ : k),
      1 < c → Nat.Coprime c 6 → IsPrimitiveRoot ζ c →
      (∏ b : Fin c, sectionEquation k side (ζ ^ b.val)) = coord k side ^ c - 1 ∧
      horizontalIdeal k side c = (∏ b : Fin c, sectionIdeal k side (ζ ^ b.val)) ∧
      (horizontalIdeal k side c).IsRadical ∧
      horizontalEquation k side c ∈ nonZeroDivisors (Chart k) ∧
      (∀ b d : Fin c, b ≠ d →
        sectionIdeal k side (ζ ^ b.val) ⊔ sectionIdeal k side (ζ ^ d.val) = ⊤) ∧
      ∃ (σ : Fin c → (Chart k →+* Base k))
        (e : (Chart k ⧸ horizontalIdeal k side c) ≃+* (Fin c → Base k)),
        (∀ b : Fin c, SectionAt k side (ζ ^ b.val) (σ b)) ∧
        (∀ (f : Chart k) (b : Fin c),
          e (Ideal.Quotient.mk (horizontalIdeal k side c) f) b = σ b f) := by
  intro k _ _ side c ζ hc _hcop hζ
  classical
  have hz : ∀ b : Fin c, ζ ^ b.val ≠ 0 :=
    fun b => pow_ne_zero _ (hζ.ne_zero (by omega))
  have hs := fun b : Fin c => completed_section_kernels k side (ζ ^ b.val) (hz b)
  choose σ hσ using fun b : Fin c => (hs b).1.exists
  have hprops := fun b : Fin c => (hs b).2 (σ b) (hσ b)
  let J : Fin c → Ideal (Chart k) := fun b => sectionIdeal k side (ζ ^ b.val)
  have hfac := horizontal_factorization k side c ζ (by omega) hζ
  have hprod : horizontalIdeal k side c = ∏ b : Fin c, J b := by
    rw [show (∏ b : Fin c, J b) = Ideal.span {(∏ b : Fin c,
      sectionEquation k side (ζ ^ b.val))} from
        Ideal.prod_span_singleton Finset.univ _]
    rw [hfac]
    simpa only [horizontalIdeal, horizontalEquation, neg_sub] using
      (Ideal.span_singleton_neg (x := coord k side ^ c - 1))
  have hpair := section_pairwise k side c ζ hζ
  have hcop : Pairwise (fun b d => IsCoprime (J b) (J d)) := by
    intro b d hbd
    exact Ideal.isCoprime_iff_sup_eq.mpr (hpair b d hbd)
  have hinf : horizontalIdeal k side c = ⨅ b, J b := by
    rw [hprod]
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := J) (fun b _ d _ hbd => hcop hbd)
  have hrad : (horizontalIdeal k side c).IsRadical := by
    rw [hinf]
    exact Ideal.isRadical_iInf J (fun b => (hprops b).2.2.1.isRadical)
  have hnzd : horizontalEquation k side c ∈ nonZeroDivisors (Chart k) := by
    have hp : (∏ b : Fin c, sectionEquation k side (ζ ^ b.val)) ∈
        nonZeroDivisors (Chart k) :=
      prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors (fun b _ => (hprops b).2.2.2)
    rw [hfac] at hp
    rw [mem_nonZeroDivisors_iff] at hp ⊢
    constructor
    · intro z hz
      apply hp.1 z
      dsimp [horizontalEquation] at hz
      linear_combination -hz
    · intro z hz
      apply hp.2 z
      dsimp [horizontalEquation] at hz
      linear_combination -hz
  let f : Chart k →+* (Fin c → Base k) := RingHom.pi σ
  have hker : RingHom.ker f = horizontalIdeal k side c := by
    rw [hinf]
    ext z
    simp only [RingHom.mem_ker, f, RingHom.pi_apply, funext_iff, Pi.zero_apply,
      Ideal.mem_iInf]
    exact forall_congr' (fun b => by dsimp [J]; rw [← (hprops b).2.1]; rfl)
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨z, hz⟩ := Ideal.pi_quotient_surjective hcop
      (fun b => Ideal.Quotient.mk (J b) (base k (v b)))
    refine ⟨z, funext (fun b => ?_)⟩
    have hm : z - base k (v b) ∈ J b := Ideal.Quotient.eq.mp (hz b)
    dsimp [J] at hm
    rw [← (hprops b).2.1] at hm
    have he : σ b (z - base k (v b)) = 0 := hm
    rw [map_sub, show σ b (base k (v b)) = v b from
      DFunLike.congr_fun (hσ b).1 (v b)] at he
    exact sub_eq_zero.mp he
  let e : (Chart k ⧸ horizontalIdeal k side c) ≃+* (Fin c → Base k) :=
    (Ideal.quotEquivOfEq hker.symm).trans (f.quotientKerEquivOfSurjective hsurj)
  refine ⟨hfac, hprod, hrad, hnzd, hpair, σ, e, hσ, ?_⟩
  intro z b
  change (f.quotientKerEquivOfSurjective hsurj
    (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk _ z))) b = σ b z
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

end ArithmeticThetaAnnularTorsionPrereqR0053
