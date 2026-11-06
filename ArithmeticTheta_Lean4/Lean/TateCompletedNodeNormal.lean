import TateAlgebraicNodeRegular
import TateAnnularGeometryDefinitions

/-! Regularity and normality of the actual parameter-adic completed node.
Domainhood is proved from the two prime branches and Krull intersection.
Local surface arguments prove normality and regularity at every prime. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace ArithmeticThetaAnnularGeometry
namespace CompletedNodeSupport

section QuotientExtension
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (I : Ideal R) (f : R →+* S) (hI : I ≤ RingHom.ker f)

/-- Extend a map killing the completion ideal by reduction modulo that ideal. -/
def residueExtension : AdicCompletion I R →+* S :=
  (Ideal.Quotient.lift I f hI).comp (AdicCompletion.evalOneₐ I).toRingHom

@[simp] theorem residueExtension_of (a : R) :
    residueExtension I f hI (algebraMap R (AdicCompletion I R) a) = f a := by
  change Ideal.Quotient.lift I f hI ((AdicCompletion.evalOneₐ I)
    (algebraMap R (AdicCompletion I R) a)) = _
  rfl

theorem residueExtension_surjective (hf : Function.Surjective f) :
    Function.Surjective (residueExtension I f hI) := by
  intro s
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨algebraMap R _ r, residueExtension_of I f hI r⟩

theorem residueExtension_ker (hfg : I.FG) :
    RingHom.ker (residueExtension I f hI) =
      (RingHom.ker f).map (algebraMap R (AdicCompletion I R)) := by
  let e := (AdicCompletion.evalOneₐ I).toRingHom
  have he : e.comp (algebraMap R (AdicCompletion I R)) = Ideal.Quotient.mk I :=
    AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I
  rw [residueExtension, ← RingHom.comap_ker, Ideal.ker_quotient_lift,
    ← he, ← Ideal.map_map]
  change Ideal.comap e (Ideal.map e _) = _
  rw [Ideal.comap_map_of_surjective e (AdicCompletion.evalOneₐ_surjective I),
    ← RingHom.ker_eq_comap_bot]
  apply sup_eq_left.mpr
  change RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤ _
  rw [AdicCompletion.ker_evalOneₐ_eq_map I hfg]
  exact Ideal.map_mono hI

end QuotientExtension

section CrossingDomain
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A regular prime coordinate forces arbitrarily high divisibility of an
annihilated element when the annihilator is nonzero on the branch. -/
lemma pow_dvd_of_mul_eq_zero {z c a : A}
    (hz : (Ideal.span {z} : Ideal A).IsPrime)
    (hreg : Function.Injective (fun b : A => z * b))
    (hc : c ∉ (Ideal.span {z} : Ideal A)) (ha : c * a = 0) :
    ∀ n : ℕ, z ^ n ∣ a := by
  intro n
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hamem : a ∈ (Ideal.span {z} : Ideal A) :=
      (hz.mem_or_mem (ha ▸ Ideal.zero_mem _)).resolve_left hc
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hamem
    have hcb : c * b = 0 := hreg (by simpa only [mul_zero, mul_left_comm] using ha)
    obtain ⟨d, hd⟩ := ih hcb
    exact ⟨d, by rw [hd, pow_succ]; ring⟩

lemma exists_multiplier_of_all_pow_dvd (z a : A) (ha : ∀ n : ℕ, z ^ n ∣ a) :
    ∃ r : A, r ∈ (Ideal.span {z} : Ideal A) ∧ r * a = a := by
  have hm : a ∈ (⨅ n : ℕ, (Ideal.span {z} : Ideal A) ^ n • ⊤ : Ideal A) := by
    rw [Submodule.mem_iInf]
    intro n
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using ha n
  obtain ⟨r, hr⟩ := ((Ideal.span {z} : Ideal A).mem_iInf_smul_pow_eq_bot_iff a).mp hm
  exact ⟨r, r.property, hr⟩

/-- Separatedness for one branch follows from the other branch and the actual
product in the Jacobson radical. No domain assumption is used. -/
lemma eq_zero_of_all_pow_dvd_crossing {x y : A}
    (hy : (Ideal.span {y} : Ideal A).IsPrime)
    (hyreg : Function.Injective (fun b : A => y * b))
    (hproper : (Ideal.span {x} : Ideal A) ⊔ Ideal.span {y} ≠ ⊤)
    (hjac : x * y ∈ (⊥ : Ideal A).jacobson)
    (a : A) (ha : ∀ n : ℕ, x ^ n ∣ a) : a = 0 := by
  obtain ⟨r, hr, hra⟩ := exists_multiplier_of_all_pow_dvd x a ha
  have hrnot : 1 - r ∉ (Ideal.span {y} : Ideal A) := by
    intro h
    apply hproper
    apply Ideal.eq_top_of_isUnit_mem _ (x := (1 : A))
    · simpa using (Submodule.add_mem_sup hr h)
    · exact isUnit_one
  have hz : (1 - r) * a = 0 := by rw [sub_mul, one_mul, hra, sub_self]
  obtain ⟨s, hs, hsa⟩ := exists_multiplier_of_all_pow_dvd y a
    (pow_dvd_of_mul_eq_zero hy hyreg hrnot hz)
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.mp hr
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton.mp hs
  have hrs : r * s ∈ (⊥ : Ideal A).jacobson := by
    rw [hr', hs']
    convert (⊥ : Ideal A).jacobson.mul_mem_right (r' * s') hjac using 1 <;> ring
  have hpow : ∀ n : ℕ, (r * s) ^ n ∣ a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨b, ?_⟩
      rw [pow_succ, mul_assoc, mul_comm (r*s) b, ← mul_assoc, ← hb,
        mul_comm a (r*s), mul_assoc, hsa, hra]
  have hmem : a ∈ (⨅ n : ℕ, (Ideal.span {r*s} : Ideal A) ^ n • ⊤ : Ideal A) := by
    rw [Submodule.mem_iInf]
    intro n
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using hpow n
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
    ((Ideal.span_singleton_le_iff_mem _).mpr hrs), Ideal.mem_bot] at hmem
  exact hmem

/-- A separated regular prime coordinate implies that the ring is a domain. -/
lemma isDomain_of_regular_prime_separated [Nontrivial A] {x : A}
    (hx : (Ideal.span {x} : Ideal A).IsPrime)
    (hreg : Function.Injective (fun b : A => x * b))
    (hsep : ∀ a : A, (∀ n : ℕ, x ^ n ∣ a) → a = 0) : IsDomain A := by
  have key : ∀ n : ℕ, ∀ a b : A, ¬x ^ n ∣ a → a * b = 0 → b = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro a b hna hab
      by_cases hxa : x ∣ a
      · obtain ⟨c, rfl⟩ := hxa
        apply ih c b
        · intro hd
          exact hna (by simpa [pow_succ, mul_comm] using mul_dvd_mul_left x hd)
        · apply hreg
          simpa only [mul_assoc, mul_zero] using hab
      · apply hsep b
        exact pow_dvd_of_mul_eq_zero hx hreg
          (by simpa only [Ideal.mem_span_singleton] using hxa) hab
  have hnzd : NoZeroDivisors A := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have hn : ∃ n : ℕ, ¬x ^ n ∣ a := by
        by_contra! h
        exact ha (hsep a h)
      obtain ⟨n, hn⟩ := hn
      exact key n a b hn hab⟩
  exact { }

end CrossingDomain


namespace LocalSurface
-- Source-adapted local algebra; see FormalizationMapping.md for provenance.


open IsLocalRing RingTheory
open scoped Pointwise

namespace W2RLR



theorem maximalIdeal_ne_bot_of_ringKrullDim_pos (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

namespace No4PatchingCore

section FromABFreeness
variable {R : Type u} [CommRing R]

theorem isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)))
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem exists_ringKrullDim_eq_natCast (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have h1 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  have h2 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  cases hd : ringKrullDim R with
  | bot => exact absurd hd h2
  | coe d =>
    cases d with
    | top => exact absurd hd (by simpa using h1)
    | coe d => exact ⟨d, rfl⟩

end FromABFreeness

section Exchange0
variable (R : Type u) [CommRing R]

theorem exists_finite_span_eq_maximalIdeal_mem [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ S : Set R, x ∈ S ∧ S.Finite ∧ S.ncard ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span S = maximalIdeal R := by
  classical

  set ξ : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hξdef
  have hξ0 : ξ ≠ 0 := by
    rw [hξdef, ne_eq, Ideal.toCotangent_eq_zero]
    exact hx2

  have hli : LinearIndepOn (ResidueField R) id ({ξ} : Set (CotangentSpace R)) := by
    refine LinearIndepOn.singleton' ?_
    intro r hr
    rcases smul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hξ0

  obtain ⟨B, hξB, hBfin, hBcard, hBspan⟩ :
      ∃ B : Set (CotangentSpace R), ξ ∈ B ∧ B.Finite ∧
        B.ncard = (maximalIdeal R).spanFinrank ∧
        Submodule.span (ResidueField R) B = ⊤ := by
    refine ⟨hli.extend (Set.subset_univ _),
      hli.subset_extend _ (Set.mem_singleton ξ), ?_, ?_, ?_⟩
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      exact Set.toFinite _
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      haveI : Fintype (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Fintype.ofFinite _
      rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R,
        Module.finrank_eq_card_basis (Module.Basis.extend hli),
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    · have h1 := (Module.Basis.extend hli).span_eq
      rwa [Module.Basis.range_extend] at h1

  choose lift hlift using (maximalIdeal R).toCotangent_surjective
  set S₀ : Set ↥(maximalIdeal R) := insert ⟨x, hx⟩ (lift '' (B \ {ξ})) with hS₀def

  have himg : (maximalIdeal R).toCotangent '' S₀ = B := by
    rw [hS₀def, Set.image_insert_eq, ← hξdef, ← Set.image_comp]
    have hcomp : ((maximalIdeal R).toCotangent ∘ lift) '' (B \ {ξ}) = B \ {ξ} := by
      have : ∀ v ∈ B \ {ξ}, ((maximalIdeal R).toCotangent ∘ lift) v = id v :=
        fun v _ => hlift v
      rw [Set.image_congr this, Set.image_id]
    rw [hcomp, Set.insert_diff_singleton, Set.insert_eq_self.mpr hξB]

  have hspanR : Submodule.span R S₀ = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [himg, hBspan]
  have hspan : Ideal.span ((↑) '' S₀ : Set R) = maximalIdeal R := by
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap

  refine ⟨(↑) '' S₀, ⟨⟨x, hx⟩, by rw [hS₀def]; exact Set.mem_insert _ _, rfl⟩, ?_, ?_, hspan⟩
  · rw [hS₀def]
    exact (((hBfin.diff).image _).insert _).image _
  ·
    have hfin₁ : (lift '' (B \ {ξ})).Finite := (hBfin.diff).image _
    have h1 : ((↑) '' S₀ : Set R).ncard ≤ S₀.ncard := by
      apply Set.ncard_image_le
      rw [hS₀def]; exact hfin₁.insert _
    have h2 : S₀.ncard ≤ (lift '' (B \ {ξ})).ncard + 1 := by
      rw [hS₀def]; exact Set.ncard_insert_le _ _
    have h3 : (lift '' (B \ {ξ})).ncard ≤ (B \ {ξ}).ncard :=
      Set.ncard_image_le hBfin.diff
    have h4 : (B \ {ξ}).ncard + 1 = B.ncard :=
      Set.ncard_diff_singleton_add_one hξB hBfin
    omega

end Exchange0

section PrimeAvoidance

theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem

  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  haveI : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    haveI : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    letI : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

theorem exists_parameter_notMem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hbot : maximalIdeal R ≠ ⊥ :=
    W2RLR.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim

  have hfin : (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)).Finite :=
    Set.Finite.insert _ (minimalPrimes.finite_of_isNoetherianRing R)

  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    ·
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    ·
      have hp_prime : I.IsPrime := Ideal.minimalPrimes_isPrime hI
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal hp_prime.ne_top).antisymm hle
      rw [heq] at hI
      exact maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos R hdim hI

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · exact absurd rfl hI₁
    · exact Ideal.minimalPrimes_isPrime hI

  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_⟩
  ·
    intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  ·
    intro p hp hxp
    exact hxout (Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp)

end PrimeAvoidance

section DimensionDrop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem annihilator_self_eq_bot (R : Type u) [CommRing R] : Module.annihilator R R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  simpa using Module.mem_annihilator.mp hr 1

theorem ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    ?_ hx
  intro p hp
  refine hxmin p ?_
  rwa [annihilator_self_eq_bot] at hp

theorem ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hkey : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
    ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact hkey

end DimensionDrop

section QuotientRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

theorem isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by

  obtain ⟨S, hxS, hSfin, hScard, hSspan⟩ :=
    exists_finite_span_eq_maximalIdeal_mem R hx hx2

  have hmax' : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmkx : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (S \ {x})) := by
    rw [← hSspan, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        rw [SetLike.mem_coe, hmkx]
        exact Submodule.zero_mem _
      · exact Ideal.subset_span ⟨y, ⟨hy, hyx⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono Set.diff_subset)

  have hsf_le : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
    have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ (S \ {x}).ncard := by
      rw [← hmax', hmap]
      exact le_trans
        (Submodule.spanFinrank_span_le_ncard_of_finite ((hSfin.diff).image _))
        (Set.ncard_image_le hSfin.diff)
    have h2 : (S \ {x}).ncard + 1 = S.ncard :=
      Set.ncard_diff_singleton_add_one hxS hSfin
    omega

  have hkrull : ringKrullDim (R ⧸ Ideal.span {x}) ≤
      ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have hdrop : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hregR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)

  have hsqueeze : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcalc : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hregR, ← hdrop]
      calc ringKrullDim (R ⧸ Ideal.span {x}) + 1
          ≤ ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 :=
            add_le_add hkrull le_rfl
        _ = (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
            push_cast
            ring
    exact_mod_cast hcalc
  have hkey : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
      (maximalIdeal R).spanFinrank := by omega

  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
  have hd1 : (d : ℕ) + 1 = (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) =
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      have h5 : ringKrullDim (R ⧸ Ideal.span {x}) + 1 =
          (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdrop, ← hregR]
        exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ∞) hkey.symm
      rw [hd] at h5
      rw [← h5]
      push_cast
      ring
    exact_mod_cast hcast
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, hkey⟩
  rw [hd]
  have : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = d := by omega
  exact_mod_cast this.le

end QuotientRegularity

section MatsumuraDomain

theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>

    intro R _ _ hn
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        ((maximalIdeal R).fg_of_isNoetherianRing)).mp hn
    haveI hprime : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n IH =>
    intro R _ _ hn

    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
    have hdim_pos : 0 < ringKrullDim R := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos n

    obtain ⟨x, hx_mem, hx_sq, hx_min⟩ := exists_parameter_notMem_minimalPrimes R hdim_pos

    haveI hloc : IsLocalRing (R ⧸ Ideal.span {x}) :=
      isLocalRing_quotient_span_singleton hx_mem
    obtain ⟨hreg', hsf'⟩ :=
      isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes R
        hx_mem hx_sq hx_min
    haveI := hreg'
    have hsf'n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      rw [hn] at hsf'
      omega

    have hdom' : IsDomain (R ⧸ Ideal.span {x}) := IH (R ⧸ Ideal.span {x}) hsf'n
    have hprime : (Ideal.span {x}).IsPrime := by
      rw [← Ideal.Quotient.isDomain_iff_prime]
      exact hdom'

    haveI := hprime
    obtain ⟨p, hp_min, hp_le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Ideal.span {x}) bot_le
    have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp_min
    have hxp : x ∉ p := hx_min p hp_min

    have hple : p ≤ (maximalIdeal R) • p := by
      intro a ha
      obtain ⟨r, hrx⟩ := Ideal.mem_span_singleton'.mp (hp_le ha)
      have hrp : r ∈ p := by
        have hmem : r * x ∈ p := by rw [hrx]; exact ha
        rcases hp_prime.mem_or_mem hmem with h | h
        · exact h
        · exact absurd h hxp
      rw [Ideal.smul_eq_mul, ← hrx, mul_comm r x]
      exact Ideal.mul_mem_mul hx_mem hrp

    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) hple (IsLocalRing.maximalIdeal_le_jacobson _)

    haveI : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    exact IsDomain.of_bot_isPrime R

theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux ((maximalIdeal R).spanFinrank) R rfl

end MatsumuraDomain

end No4PatchingCore

end W2RLR

open IsLocalRing

theorem regular_local_domain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing R

theorem factorial_of_pid_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    UniqueFactorizationMonoid A := by
  classical

  have hspan_ne_top : Ideal.span {t} ≠ ⊤ := fun h =>
    zero_ne_one ((Ideal.Quotient.zero_eq_one_iff (I := Ideal.span {t})).mpr h)
  have htm : t ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal hspan_ne_top (Ideal.subset_span (Set.mem_singleton t))
  have hprime_span : (Ideal.span {t}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {t})).mp inferInstance
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
  by_cases hA : t ∈ I ∧ t ≠ 0
  ·
    exact ⟨t, hA.1, (Ideal.span_singleton_prime hA.2).mp hprime_span⟩

  set π := Ideal.Quotient.mk (Ideal.span {t}) with hπ
  obtain ⟨gbar, hgbar⟩ := (IsPrincipalIdealRing.principal (I.map π)).principal
  have hgmem : gbar ∈ I.map π := by rw [hgbar]; exact Ideal.mem_span_singleton_self _
  obtain ⟨f, hfI, hfg⟩ := (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).mp hgmem
  have hle : I ≤ Ideal.span {f} ⊔ Ideal.span {t} • I := by
    intro g hg
    have hπg : π g ∈ I.map π := Ideal.mem_map_of_mem _ hg
    rw [hgbar, ← hfg, Ideal.mem_span_singleton] at hπg
    obtain ⟨cbar, hc⟩ := hπg
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cbar
    have hdiff : g - f * c ∈ Ideal.span {t} := Ideal.Quotient.eq.mp (by rw [map_mul]; exact hc)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hdiff
    have hfc : f * c ∈ Ideal.span {f} := Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c f⟩
    rcases not_and_or.mp hA with htI | ht0
    ·
      have hdI : d ∈ I := by
        have hdt : d * t ∈ I := by rw [hd]; exact I.sub_mem hg (I.mul_mem_right _ hfI)
        exact (hIp.mem_or_mem hdt).resolve_right htI
      have hg' : g = f * c + t * d := by rw [mul_comm t d, hd]; ring
      rw [hg']
      exact Submodule.add_mem_sup hfc (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hdI)
    ·
      rw [not_ne_iff] at ht0
      have hg' : g = f * c := by rw [← sub_eq_zero, ← hd, ht0, mul_zero]
      rw [hg']
      exact Submodule.mem_sup_left hfc
  have hjac : Ideal.span {t} ≤ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr htm
  have hIf : I ≤ Ideal.span {f} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hjac hle
  have hIeq : I = Ideal.span {f} := le_antisymm hIf ((Ideal.span_singleton_le_iff_mem _).mpr hfI)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hI (by rw [hIeq, Ideal.span_singleton_eq_bot])
  exact ⟨f, hfI, (Ideal.span_singleton_prime hf0).mp (hIeq ▸ hIp)⟩


open IsLocalRing

namespace AB2UFD

theorem isPrincipalIdealRing_of_spanFinrank_eq_one (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (h : Submodule.spanFinrank (maximalIdeal S) = 1) : IsPrincipalIdealRing S := by
  haveI : IsDomain S := W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace S]
    exact h
  haveI : IsDiscreteValuationRing S := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hcot
  infer_instance

theorem isPrincipalIdealRing_of_maximalIdeal_eq_bot (S : Type*) [CommRing S] [IsLocalRing S]
    (h : maximalIdeal S = ⊥) : IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊤
  · exact ⟨⟨1, by simp [hI]⟩⟩
  · have hIbot : I = ⊥ := le_bot_iff.mp (h ▸ IsLocalRing.le_maximalIdeal hI)
    exact ⟨⟨0, by simp [hIbot]⟩⟩

end AB2UFD

open AB2UFD in
theorem factorial_dim_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2) :
    UniqueFactorizationMonoid R := by
  have hdR : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd2 : Submodule.spanFinrank (maximalIdeal R) ≤ 2 := by
    have : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 2 := hdR ▸ hdim
    exact_mod_cast this
  rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 1 with h0 | h1
    ·
      have h0' : Submodule.spanFinrank (maximalIdeal R) = 0 := by omega
      have hm : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0'
      haveI := isPrincipalIdealRing_of_maximalIdeal_eq_bot R hm
      infer_instance
    ·
      have h1' : Submodule.spanFinrank (maximalIdeal R) = 1 := by omega
      haveI := isPrincipalIdealRing_of_spanFinrank_eq_one R h1'
      infer_instance
  ·
    have h2 : Submodule.spanFinrank (maximalIdeal R) = 2 := le_antisymm hd2 hge
    have hpos : 0 < ringKrullDim R := by
      rw [← hdR, h2]
      exact_mod_cast Nat.zero_lt_two
    obtain ⟨x, hx, hx2, hxmin⟩ :=
      W2RLR.No4PatchingCore.exists_parameter_notMem_minimalPrimes R hpos
    have hxtop : Ideal.span {x} ≠ ⊤ := by
      intro htop
      have hle : Ideal.span {x} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hx
      exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
    haveI : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
    haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hsf⟩ :=
      W2RLR.No4PatchingCore.isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes R hx hx2 hxmin
    haveI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hreg
    have h1 : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span {x})) = 1 := by omega
    haveI : IsPrincipalIdealRing (R ⧸ Ideal.span {x}) :=
      isPrincipalIdealRing_of_spanFinrank_eq_one (R ⧸ Ideal.span {x}) h1
    haveI : IsDomain (R ⧸ Ideal.span {x}) := W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing _
    exact factorial_of_pid_quotient x


theorem regular_localization_nonmax
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (𝔯 : Ideal R₀) [𝔯.IsPrime] (h𝔯 : 𝔯 ≠ IsLocalRing.maximalIdeal R₀) :
    IsRegularLocalRing (Localization.AtPrime 𝔯) := by
  classical
  set A := Localization.AtPrime 𝔯

  have hlt : 𝔯 < IsLocalRing.maximalIdeal R₀ :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h𝔯
  have h1 : 𝔯.height + 1 ≤ (IsLocalRing.maximalIdeal R₀).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm : (IsLocalRing.maximalIdeal R₀).height ≤ 2 := by
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀)
    rw [← h2] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hrh : 𝔯.height ≤ 1 := by
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans hm
    have hne : 𝔯.height ≠ ⊤ := by
      intro htop; rw [htop] at h3; exact absurd h3 (by decide)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h3 ⊢
    have : (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    rw [this] at h3
    have h4 : n + 1 ≤ 2 := by exact_mod_cast h3
    exact_mod_cast (by omega : n ≤ 1)
  have hdimA : ringKrullDim A ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 A]
    exact_mod_cast hrh
  haveI hic : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A 𝔯.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔯)
  by_cases hF : IsField A
  · letI : Field A := hF.toField
    infer_instance
  ·
    haveI : Ring.DimensionLEOne A := by
      refine ⟨fun {p} hp0 hp => ?_⟩
      haveI : p.IsPrime := hp
      have hb : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
      have hh : (⊥ : Ideal A).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hb
      rw [Ideal.height_bot, zero_add] at hh
      have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
      have hge : (1 : WithBot ℕ∞) ≤ p.height := by exact_mod_cast hh
      exact Ideal.isMaximal_of_height_eq_ringKrullDim (le_antisymm hle (hdimA.trans hge))
    haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔯.primeCompl A inferInstance
    have hded : IsDedekindDomain A := { }
    haveI : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hF).out 0 2).mpr hded
    infer_instance


theorem regular_ring_dim_two (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (hdim : ringKrullDim R ≤ 2) : IsRegularRing R := by
  let : UniqueFactorizationMonoid R := factorial_dim_two R hdim
  let : IsIntegrallyClosed R := inferInstance
  rw [isRegularRing_iff]
  intro p hp
  by_cases h : p = IsLocalRing.maximalIdeal R
  · subst h
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
        (fun x => by simpa using! fun a => a)).toRingEquiv
  · exact regular_localization_nonmax hdim p h

end LocalSurface

open ArithmeticThetaNodeCharts
open AlgebraicNodeSupport.CrossingResolutionR1

variable (k : Type u) [Field k] [CharZero k]

lemma completed_xy : cx k * cy k = ct k := by
  simp only [cx, cy, ct, ← map_mul, node_xy]

lemma completed_parameter_regular : Function.Injective (fun a : CompletedNode k => ct k * a) :=
  (node_completion_embedding_flat k).2.2.2.2

lemma completed_x_regular : Function.Injective (fun a : CompletedNode k => cx k * a) := by
  intro a b h
  apply completed_parameter_regular k
  simpa only [← completed_xy k, mul_assoc, mul_left_comm (cx k) (cy k)] using
    congrArg (fun z => cy k * z) h

lemma completed_y_regular : Function.Injective (fun a : CompletedNode k => cy k * a) := by
  intro a b h
  apply completed_parameter_regular k
  simpa only [← completed_xy k, mul_assoc] using congrArg (fun z => cx k * z) h

lemma completedIdeal_eq_map : completedIdeal k = (nodeIdeal k).map (toCompleted k) := by
  simp [completedIdeal, nodeIdeal, Ideal.map_span, Set.image_singleton]

lemma completed_parameter_jacobson : ct k ∈ (⊥ : Ideal (CompletedNode k)).jacobson := by
  have : IsAdicComplete ((nodeIdeal k).map (algebraMap (Node k) (CompletedNode k)))
      (CompletedNode k) := AdicCompletion.isAdicComplete_self _ (Submodule.fg_span_singleton _)
  apply IsAdicComplete.le_jacobson_bot ((nodeIdeal k).map (algebraMap _ _))
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)

lemma maximal_contains_coordinate (M : Ideal (CompletedNode k)) [M.IsMaximal] :
    cx k ∈ M ∨ cy k ∈ M := by
  apply (show M.IsPrime from inferInstance).mem_or_mem
  rw [completed_xy]
  exact (show (⊥ : Ideal (CompletedNode k)).jacobson ≤ M from
    sInf_le ⟨bot_le, inferInstance⟩) (completed_parameter_jacobson k)

lemma nodeIdeal_le_branchY : nodeIdeal k ≤ RingHom.ker (branchY (parameter k)) := by
  rw [show RingHom.ker (branchY (parameter k)) = Ideal.span {x k} from ker_branchY _]
  rw [nodeIdeal, Ideal.span_singleton_le_iff_mem, ← node_xy]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma nodeIdeal_le_branchX : nodeIdeal k ≤ RingHom.ker (branchX (parameter k)) := by
  rw [show RingHom.ker (branchX (parameter k)) = Ideal.span {y k} from ker_branchX _]
  rw [nodeIdeal, Ideal.span_singleton_le_iff_mem, ← node_xy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def completedBranchY : CompletedNode k →+* Polynomial (Resid (parameter k)) :=
  residueExtension (nodeIdeal k) (branchY (parameter k)).toRingHom (nodeIdeal_le_branchY k)

def completedBranchX : CompletedNode k →+* Polynomial (Resid (parameter k)) :=
  residueExtension (nodeIdeal k) (branchX (parameter k)).toRingHom (nodeIdeal_le_branchX k)

lemma completedBranchY_surjective : Function.Surjective (completedBranchY k) :=
  residueExtension_surjective _ _ _ (branchY_surjective (parameter k))

lemma completedBranchX_surjective : Function.Surjective (completedBranchX k) :=
  residueExtension_surjective _ _ _ (branchX_surjective (parameter k))

lemma completedBranchY_ker : RingHom.ker (completedBranchY k) = Ideal.span {cx k} := by
  have he := residueExtension_ker (nodeIdeal k) (branchY (parameter k)).toRingHom
    (nodeIdeal_le_branchY k) (show (nodeIdeal k).FG from Submodule.fg_span_singleton _)
  change RingHom.ker (residueExtension _ _ _) = _
  refine he.trans ?_
  change (RingHom.ker (branchY (parameter k))).map (toCompleted k) = _
  rw [ker_branchY, Ideal.map_span, Set.image_singleton]
  rfl

lemma completedBranchX_ker : RingHom.ker (completedBranchX k) = Ideal.span {cy k} := by
  have he := residueExtension_ker (nodeIdeal k) (branchX (parameter k)).toRingHom
    (nodeIdeal_le_branchX k) (show (nodeIdeal k).FG from Submodule.fg_span_singleton _)
  change RingHom.ker (residueExtension _ _ _) = _
  refine he.trans ?_
  change (RingHom.ker (branchX (parameter k))).map (toCompleted k) = _
  rw [ker_branchX, Ideal.map_span, Set.image_singleton]
  rfl


lemma residue_parameter_isMaximal :
    (Ideal.span ({parameter k} : Set (Base k))).IsMaximal := by
  have heq := (IsDiscreteValuationRing.irreducible_iff_uniformizer (parameter k)).mp
    (show Irreducible (parameter k) from PowerSeries.X_irreducible)
  rw [← heq]
  infer_instance

lemma completed_branches_prime :
    (Ideal.span {cx k} : Ideal (CompletedNode k)).IsPrime ∧
    (Ideal.span {cy k} : Ideal (CompletedNode k)).IsPrime := by
  let := residue_parameter_isMaximal k
  let : Field (Resid (parameter k)) := Ideal.Quotient.field _
  constructor
  · rw [← completedBranchY_ker]
    exact RingHom.ker_isPrime _
  · rw [← completedBranchX_ker]
    exact RingHom.ker_isPrime _

@[simp] lemma completedBranchX_x : completedBranchX k (cx k) = Polynomial.X := by
  change residueExtension _ _ _ (algebraMap (Node k) _ (x k)) = _
  rw [residueExtension_of]
  exact branchX_x (parameter k)

@[simp] lemma completedBranchX_y : completedBranchX k (cy k) = 0 := by
  change residueExtension _ _ _ (algebraMap (Node k) _ (y k)) = _
  rw [residueExtension_of]
  exact branchX_y (parameter k)

@[simp] lemma completedBranchY_x : completedBranchY k (cx k) = 0 := by
  change residueExtension _ _ _ (algebraMap (Node k) _ (x k)) = _
  rw [residueExtension_of]
  exact branchY_x (parameter k)

@[simp] lemma completedBranchY_y : completedBranchY k (cy k) = Polynomial.X := by
  change residueExtension _ _ _ (algebraMap (Node k) _ (y k)) = _
  rw [residueExtension_of]
  exact branchY_y (parameter k)

lemma completed_crossing_proper :
    (Ideal.span {cx k} : Ideal (CompletedNode k)) ⊔ Ideal.span {cy k} ≠ ⊤ := by
  let := residue_parameter_isMaximal k
  let : Field (Resid (parameter k)) := Ideal.Quotient.field _
  let o : CompletedNode k →+* Resid (parameter k) :=
    Polynomial.constantCoeff.comp (completedBranchX k)
  have hle : (Ideal.span {cx k} : Ideal (CompletedNode k)) ⊔ Ideal.span {cy k} ≤
      RingHom.ker o := by
    rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
    constructor <;> simp [RingHom.mem_ker, o]
  intro h
  have : (1 : CompletedNode k) ∈ RingHom.ker o := hle (by rw [h]; trivial)
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using this)

/-- The completed node is a domain, proved using its two actual branch maps. -/
theorem completed_node_domain : IsDomain (CompletedNode k) := by
  let : IsNoetherianRing (Node k) :=
    (algebraic_node_regular_normal k).1.toIsNoetherian
  let : IsNoetherianRing (CompletedNode k) :=
    ArithmeticThetaFractionalCharts.noetherian_adic_completion (Node k) (nodeIdeal k)
  let : IsDomain (Node k) := (node_flat_domain_parameter k).1
  let : Nontrivial (CompletedNode k) :=
    (node_completion_embedding_flat k).1.nontrivial
  obtain ⟨hx, hy⟩ := completed_branches_prime k
  exact isDomain_of_regular_prime_separated hx (completed_x_regular k)
    (eq_zero_of_all_pow_dvd_crossing hy (completed_y_regular k)
      (completed_crossing_proper k) (by rw [completed_xy]; exact completed_parameter_jacobson k))

lemma completed_coordinates_ne_zero : cx k ≠ 0 ∧ cy k ≠ 0 := by
  let := completed_node_domain k
  constructor
  · intro h
    exact (node_completion_embedding_flat k).2.2.2.1
      (by change ct k = 0; rw [← completed_xy, h, zero_mul])
  · intro h
    exact (node_completion_embedding_flat k).2.2.2.1
      (by change ct k = 0; rw [← completed_xy, h, mul_zero])

/-- Every prime containing a completed coordinate has a regular local ring. -/
lemma completed_branch_local_regular (P : Ideal (CompletedNode k)) [P.IsPrime]
    (hP : cx k ∈ P ∨ cy k ∈ P) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  let := completed_node_domain k
  let : IsNoetherianRing (CompletedNode k) := (node_completion_embedding_flat k).2.1
  let := residue_parameter_isMaximal k
  let : Field (Resid (parameter k)) := Ideal.Quotient.field _
  rcases hP with hx | hy
  · exact isRegularLocalRing_of_mem_of_ker_eq_span (completedBranchY k)
      (completedBranchY_surjective k) (completed_coordinates_ne_zero k).1
      (completedBranchY_ker k) P hx
  · exact isRegularLocalRing_of_mem_of_ker_eq_span (completedBranchX k)
      (completedBranchX_surjective k) (completed_coordinates_ne_zero k).2
      (completedBranchX_ker k) P hy

lemma completed_maximal_local_regular (M : Ideal (CompletedNode k)) [M.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime M) :=
  completed_branch_local_regular k M (maximal_contains_coordinate k M)


section BranchDimension
variable {A : Type u} {D : Type v} [CommRing A] [IsNoetherianRing A]
    [CommRing D] [IsPrincipalIdealRing D]

lemma branch_local_dimension_le_two (f : A →+* D) (hf : Function.Surjective f)
    {z : A} (hk : RingHom.ker f = Ideal.span {z})
    (P : Ideal A) [P.IsPrime] (hz : z ∈ P) :
    ringKrullDim (Localization.AtPrime P) ≤ 2 := by
  have hkerP : RingHom.ker f ≤ P := by
    rw [hk, Ideal.span_singleton_le_iff_mem]; exact hz
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.map f)).principal
  obtain ⟨G, rfl⟩ := hf g
  have hPeq : P = Ideal.span {z, G} := by
    have h1 : P = (P.map f).comap f := by
      rw [Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot,
        left_eq_sup]; exact hkerP
    have h2 : P.map f = (Ideal.span {G}).map f := by
      rw [hg, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]
    rw [h1, h2, Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot,
      hk, ← Ideal.span_union, Set.union_singleton]
  have hsf : P.spanFinrank ≤ 2 := by
    rw [hPeq]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      (by classical
        by_cases h : z = G
        · simp [h]
        · exact le_of_eq (Set.ncard_pair h))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  have hh := (P.height_le_spanFinrank (show P ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)).trans
    (show (P.spanFinrank : ℕ∞) ≤ 2 by exact_mod_cast hsf)
  exact WithBot.coe_le_coe.mpr hh

end BranchDimension

lemma completed_maximal_dimension_le_two (M : Ideal (CompletedNode k)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) ≤ 2 := by
  let : IsNoetherianRing (CompletedNode k) := (node_completion_embedding_flat k).2.1
  let := residue_parameter_isMaximal k
  let : Field (Resid (parameter k)) := Ideal.Quotient.field _
  rcases maximal_contains_coordinate k M with hx | hy
  · exact branch_local_dimension_le_two (completedBranchY k)
      (completedBranchY_surjective k) (completedBranchY_ker k) M hx
  · exact branch_local_dimension_le_two (completedBranchX k)
      (completedBranchX_surjective k) (completedBranchX_ker k) M hy

lemma completed_node_integrally_closed : IsIntegrallyClosed (CompletedNode k) := by
  let := completed_node_domain k
  apply IsIntegrallyClosed.of_localization_maximal
  intro M _ hM
  let := completed_maximal_local_regular k M
  let : UniqueFactorizationMonoid (Localization.AtPrime M) :=
    LocalSurface.factorial_dim_two (Localization.AtPrime M)
      (completed_maximal_dimension_le_two k M)
  let : Nonempty (GCDMonoid (Localization.AtPrime M)) :=
    ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  infer_instance

lemma completed_node_regular : IsRegularRing (CompletedNode k) := by
  let := completed_node_domain k
  let : IsNoetherianRing (CompletedNode k) := (node_completion_embedding_flat k).2.1
  rw [isRegularRing_iff]
  intro P hP
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  let := hM
  let := completed_maximal_local_regular k M
  let : IsRegularRing (Localization.AtPrime M) :=
    LocalSurface.regular_ring_dim_two _ (completed_maximal_dimension_le_two k M)
  apply isRegularLocalRing_atPrime_of_disjoint M.primeCompl P
  rw [Set.disjoint_left]
  intro a ha hp
  exact ha (hPM hp)

end CompletedNodeSupport

/-- Regularity, domainhood and normality of the parameter-adic completed node
and domainhood and normality of its actual generic localization. -/
theorem completed_node_normal_domain :
    ∀ (k : Type u) [Field k] [CharZero k],
      IsRegularRing (ArithmeticThetaNodeCharts.CompletedNode k) ∧
      IsDomain (ArithmeticThetaNodeCharts.CompletedNode k) ∧
      IsIntegrallyClosed (ArithmeticThetaNodeCharts.CompletedNode k) ∧
      IsDomain (Localization.Away (ArithmeticThetaAnnularGeometry.ct k)) ∧
      IsIntegrallyClosed (Localization.Away (ArithmeticThetaAnnularGeometry.ct k)) := by
  intro k _ _
  let := CompletedNodeSupport.completed_node_domain k
  let := CompletedNodeSupport.completed_node_integrally_closed k
  have ht : ct k ≠ 0 := (ArithmeticThetaNodeCharts.node_completion_embedding_flat k).2.2.2.1
  let : IsDomain (Localization.Away (ct k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  exact ⟨CompletedNodeSupport.completed_node_regular k, inferInstance, inferInstance,
    inferInstance, isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (ct k))
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht)⟩


end ArithmeticThetaAnnularGeometry
