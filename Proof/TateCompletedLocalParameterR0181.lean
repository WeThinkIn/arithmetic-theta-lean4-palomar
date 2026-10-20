module

public import TateCuspDiskExtensionR0181
public import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
public import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow

@[expose] public section

/-! Local-ring constructions for the actual Tate disk. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
namespace CompletedLocalParameter
open CategoryTheory AlgebraicGeometry ArithmeticThetaLevelCompactificationR0179

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)

/-- The canonical disk germ is the inverse of the local-spectrum stalk
isomorphism; this identifies the map, not just its domain and codomain. -/
lemma diskGerm_eq :
    diskGerm k = (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).inv.hom := by
  have h := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of (PowerSeries k))
  rw [← Iso.eq_inv_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma diskGerm_bijective : Function.Bijective (diskGerm k) := by
  rw [diskGerm_eq]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The actual stalk map, expressed in the power-series ring by its canonical
closed-point identification. -/
def localMap (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) : CuspStalk k L D X d →+* PowerSeries k :=
  (Scheme.stalkClosedPointTo d).hom

instance localMap_isLocalHom (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) : IsLocalHom (localMap k L D X d) :=
  inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo d).hom)

lemma diskGerm_localMap (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) :
    (diskGerm k).comp (localMap k L D X d) = (d.stalkMap (closedPoint k)).hom := by
  rw [diskGerm_eq]
  change ((d.stalkMap (closedPoint k) ≫
    (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).hom) ≫
    (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).inv).hom = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma localMap_unique (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) (f : CuspStalk k L D X d →+* PowerSeries k)
    (hf : (diskGerm k).comp f = (d.stalkMap (closedPoint k)).hom) :
    f = localMap k L D X d := by
  apply RingHom.ext
  intro a
  apply (diskGerm_bijective k).1
  exact RingHom.congr_fun (hf.trans (diskGerm_localMap k L D X d).symm) a

/-- The completion target has a unique possible restriction to the stalk. -/
lemma isCompletedParameter_iff (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) :
    IsCompletedParameter k L D X d ↔
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
          (CuspStalk k L D X d) ≃+* PowerSeries k,
        ∀ a, e (AdicCompletion.of (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
          (CuspStalk k L D X d) a) = localMap k L D X d a := by
  constructor
  · rintro ⟨f, hf, e, he⟩
    obtain rfl := localMap_unique k L D X d f hf
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨localMap k L D X d, diskGerm_localMap k L D X d, e, he⟩

/-- The source of the required completed map is the DVR at the actual center. -/
lemma cuspStalk_dvr (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) :
    ∃ hdom : IsDomain (CuspStalk k L D X d),
      @IsDiscreteValuationRing (CuspStalk k L D X d) inferInstance hdom := by
  letI := X.smooth
  exact BoundaryGeometry.dvr_of_closed X.projection (d (closedPoint k))
    (BoundaryGeometry.boundary_point_closed k L D X _ hd.2.2)

/-- Localness gives continuity for the specific maximal-ideal filtrations. -/
lemma localMap_filtered (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) (n : ℕ) :
    (IsLocalRing.maximalIdeal (CuspStalk k L D X d)) ^ n ≤
      ((IsLocalRing.maximalIdeal (PowerSeries k)) ^ n).comap (localMap k L D X d) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le (localMap k L D X d)) n

/-- Constants enter the cusp stalk through the specified structural morphism. -/
def scalarToStalk (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) : k →+* CuspStalk k L D X d :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec (CommRingCat.of k)).presheaf.germ ⊤
      (X.projection (d (closedPoint k))) trivial ≫
    X.projection.stalkMap (d (closedPoint k))).hom

lemma localMap_scalarToStalk (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) (hd : d ≫ X.projection = diskStructure k) :
    (localMap k L D X d).comp (scalarToStalk k L D X d) =
      algebraMap k (PowerSeries k) := by
  have h : (Spec (CommRingCat.of k)).presheaf.germ ⊤
      ((d ≫ X.projection) (closedPoint k)) trivial ≫
      Scheme.stalkClosedPointTo (d ≫ X.projection) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
          CommRingCat.ofHom (algebraMap k (PowerSeries k)) := by
    rw [hd]
    exact Scheme.germ_stalkClosedPointTo_Spec _
  rw [Scheme.stalkClosedPointTo_comp] at h
  change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ _ ≫ _) ≫
    Scheme.stalkClosedPointTo d).hom = _
  erw [Category.assoc, Category.assoc, h, Iso.inv_hom_id_assoc]
  rfl

/-- The actual local map is surjective on residues: every power series is
congruent to the image of its constant coefficient. -/
lemma localMap_residue_surjective (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) (hd : d ≫ X.projection = diskStructure k)
    (w : PowerSeries k) :
    ∃ a : CuspStalk k L D X d,
      w - localMap k L D X d a ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
  refine ⟨scalarToStalk k L D X d (PowerSeries.constantCoeff w), ?_⟩
  have h := RingHom.congr_fun (localMap_scalarToStalk k L D X d hd)
    (PowerSeries.constantCoeff w)
  rw [RingHom.comp_apply] at h
  rw [h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- A continuous extension to the completion exists before any ramification
assertion. Its bijectivity remains a separate geometric question. -/
lemma completedMap_exists (D : LevelData k L) (X : Compactification k L D)
    (d : Disk k ⟶ X.space) :
    ∃ F : AdicCompletion (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
        (CuspStalk k L D X d) →+* PowerSeries k,
      ∀ a, F (AdicCompletion.of (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
        (CuspStalk k L D X d) a) = localMap k L D X d a := by
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  obtain ⟨F, hF⟩ :=
    AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
      (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
      (IsLocalRing.maximalIdeal (PowerSeries k)) (localMap k L D X d)
      (fun n => ⟨n, localMap_filtered k L D X d n⟩)
  exact ⟨F, fun a => RingHom.congr_fun hF a⟩

/-- A sufficient finite-quotient criterion keeps the actual stalk map fixed.
The two hypotheses must still be supplied by the full-level geometry. -/
lemma isCompletedParameter_of_quotients
    (D : LevelData k L) (X : Compactification k L D) (d : Disk k ⟶ X.space)
    (hsurj : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (PowerSeries k)) ^ n)).comp
        (localMap k L D X d)))
    (hker : ∀ n : ℕ, RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (PowerSeries k)) ^ n)).comp
        (localMap k L D X d)) =
      (IsLocalRing.maximalIdeal (CuspStalk k L D X d)) ^ n) :
    IsCompletedParameter k L D X d := by
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  obtain ⟨e, he⟩ :=
    AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
      (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
      (IsLocalRing.maximalIdeal (PowerSeries k)) (localMap k L D X d) hsurj hker
  apply (isCompletedParameter_iff k L D X d).2
  refine ⟨e.trans (AdicCompletion.ofAlgEquiv
    (IsLocalRing.maximalIdeal (PowerSeries k))).symm.toRingEquiv, ?_⟩
  intro a
  change (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal (PowerSeries k))).symm
    (e (algebraMap _ _ a)) = _
  rw [he]
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

section UniformizerCriterion

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsDomain B] (σ : A →+* B) (π : A)
  (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
  (hσ : IsLocalRing.maximalIdeal B = Ideal.span {σ π}) (hσ0 : σ π ≠ 0)

include hπ hσ hσ0 in
lemma mem_pow_of_map_mem_pow (n : ℕ) (a : A)
    (ha : σ a ∈ (IsLocalRing.maximalIdeal B) ^ n) :
    a ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have haI : a ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal _).mp
        (Ideal.pow_le_self (Nat.succ_ne_zero n) ha)) (hu.map σ)
    rw [hπ, Ideal.mem_span_singleton'] at haI
    obtain ⟨a', rfl⟩ := haI
    rw [hσ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have he : σ a' = c * σ π ^ n := by
      apply (mul_right_cancel₀ hσ0)
      calc
        σ a' * σ π = σ (a' * π) := (map_mul σ _ _).symm
        _ = c * σ π ^ (n + 1) := hc.symm
        _ = (c * σ π ^ n) * σ π := by ring
    have ha' : a' ∈ (IsLocalRing.maximalIdeal A) ^ n := by
      apply ih
      rw [hσ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      exact ⟨c, he.symm⟩
    rw [pow_succ]
    exact Ideal.mul_mem_mul ha' (by rw [hπ]; exact Ideal.mem_span_singleton_self π)

include hσ in
lemma approximate_mod_pow
    (hres : ∀ w : B, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal B)
    (n : ℕ) (w : B) : ∃ a : A, w - σ a ∈ (IsLocalRing.maximalIdeal B) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    rw [hσ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨z, hz⟩ := ha
    obtain ⟨c, hc⟩ := hres z
    refine ⟨a + c * π ^ n, ?_⟩
    have he : w - σ (a + c * π ^ n) = (z - σ c) * σ π ^ n := by
      rw [map_add, map_mul, map_pow]
      linear_combination -hz
    rw [he, pow_succ']
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow
      (by rw [hσ]; exact Ideal.mem_span_singleton_self (σ π)) n)

end UniformizerCriterion

/-- Once the actual local map sends a cusp uniformizer to a uniformizer,
all finite quotients agree and the required completion isomorphism follows.
This lemma does not assume a completion equivalence. -/
lemma isCompletedParameter_of_uniformizer
    (D : LevelData k L) (X : Compactification k L D) (d : Disk k ⟶ X.space)
    (hd : d ≫ X.projection = diskStructure k)
    (π : CuspStalk k L D X d)
    (hπ : IsLocalRing.maximalIdeal (CuspStalk k L D X d) = Ideal.span {π})
    (hσ : IsLocalRing.maximalIdeal (PowerSeries k) =
      Ideal.span {localMap k L D X d π}) : IsCompletedParameter k L D X d := by
  have hσ0 : localMap k L D X d π ≠ 0 := by
    intro hz
    have h := hσ
    rw [hz, Ideal.span_singleton_zero] at h
    exact IsDiscreteValuationRing.not_a_field (PowerSeries k) h
  apply isCompletedParameter_of_quotients k L D X d
  · intro n w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨a, ha⟩ := approximate_mod_pow (localMap k L D X d) π hσ
      (localMap_residue_surjective k L D X d hd) n w
    refine ⟨a, ?_⟩
    exact (Ideal.Quotient.eq.mpr ha).symm
  · intro n
    ext a
    change (Ideal.Quotient.mk _ (localMap k L D X d a) = 0) ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨mem_pow_of_map_mem_pow (localMap k L D X d) π hπ hσ hσ0 n a,
      fun ha => localMap_filtered k L D X d n ha⟩

/-- For this disk the ramification-one condition is exactly the remaining
completion obligation, rather than merely a sufficient strengthening. -/
lemma isCompletedParameter_iff_uniformizer
    (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) :
    IsCompletedParameter k L D X d ↔
      ∃ π : CuspStalk k L D X d,
        IsLocalRing.maximalIdeal (CuspStalk k L D X d) = Ideal.span {π} ∧
        IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {localMap k L D X d π} := by
  constructor
  · intro h
    obtain ⟨hdom, hdvr⟩ := cuspStalk_dvr k L D X b d hd
    letI := hdom
    letI := hdvr
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (CuspStalk k L D X d)
    obtain ⟨e, he⟩ := (isCompletedParameter_iff k L D X d).1 h
    refine ⟨π, hπ.maximalIdeal_eq, ?_⟩
    have hI : IsLocalRing.maximalIdeal
        (AdicCompletion (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
          (CuspStalk k L D X d)) =
        Ideal.span {(AdicCompletion.of (IsLocalRing.maximalIdeal (CuspStalk k L D X d))
          (CuspStalk k L D X d) π)} := by
      rw [AdicCompletion.maximalIdeal_eq_map_of_fg
        (IsLocalRing.maximalIdeal (CuspStalk k L D X d)).fg_of_isNoetherianRing,
        hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
      rfl
    have hm := IsLocalRing.map_ringEquiv_maximalIdeal e
    rw [hI, Ideal.map_span, Set.image_singleton, he] at hm
    exact hm.symm
  · rintro ⟨π, hπ, hσ⟩
    exact isCompletedParameter_of_uniformizer k L D X d hd.1 π hπ hσ

lemma irreducible_of_order_one (f : PowerSeries k) (hf : f.order = 1) : Irreducible f := by
  have hf0 : f ≠ 0 := by
    intro hz
    simpa [hz] using hf
  have hassoc : Associated (PowerSeries.X : PowerSeries k) f := by
    refine ⟨PowerSeries.Unit_of_divided_by_X_pow_order f, ?_⟩
    rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hf0]
    simpa only [hf, ENat.toNat_one, pow_one] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
  exact hassoc.irreducible PowerSeries.X_irreducible

/-- It suffices to exhibit any stalk element with an order-one image. The
localness of the actual disk map then proves that element is a uniformizer. -/
lemma isCompletedParameter_of_order_one
    (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) (a : CuspStalk k L D X d)
    (ha : (localMap k L D X d a).order = 1) :
    IsCompletedParameter k L D X d := by
  obtain ⟨hdom, hdvr⟩ := cuspStalk_dvr k L D X b d hd
  letI := hdom
  letI := hdvr
  have hfa := irreducible_of_order_one k (localMap k L D X d a) ha
  have hia : Irreducible a := hfa.of_map
  exact isCompletedParameter_of_uniformizer k L D X d hd.1 a
    hia.maximalIdeal_eq hfa.maximalIdeal_eq

section LiteralCandidate
open ArithmeticThetaTateSeries ArithmeticThetaTateIdentities
open ArithmeticThetaCubicModelR0144

private lemma xTerm_coeff_below (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (xTerm (monomial a r)) = 0 := by
  rw [ArithmeticThetaTateBridges.x_term_coeff a r n (by omega)]
  split_ifs with hd
  · have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt hd h
    simp [hn]
  · rfl

/-- The literal point z=t has x-coordinate starting with t whenever L≥3. -/
lemma tateX_first_coeff (hL : 3 ≤ L) :
    PowerSeries.coeff 1 (tateX L 1 (1 : k)) = 1 := by
  have hx : PowerSeries.coeff 1
      (∑ j ∈ Finset.range 2,
        (xTerm (monomial (1 : k) (L*(j+1)+1)) +
         xTerm (monomial (1 : k)⁻¹ (L*(j+1)-1)))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hLj : L ≤ L * (j + 1) := by nlinarith
    rw [map_add, xTerm_coeff_below k 1 (by omega),
      xTerm_coeff_below k (1 : k)⁻¹ (by omega), add_zero]
  have hc : PowerSeries.coeff 1
      (∑ j ∈ Finset.range 2,
        PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (L*(j+1)) *
          (1-monomial 1 (L*(j+1)))⁻¹) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [monomial, map_one, one_mul]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp [show ¬ L*(j+1) ≤ 1 by nlinarith]
  simp only [tateX, PowerSeries.coeff_mk, partialX]
  rw [map_sub, map_add, hx, two_mul, map_add, hc]
  rw [ArithmeticThetaTateBridges.x_term_coeff 1 1 1 (by omega)]
  norm_num

/-- This normalized coordinate difference uses the literal z=t point, the
half-period point, and the toric two-torsion point of the same Tate cubic. -/
def parameterCandidate : PowerSeries k :=
  (tateX L 1 1 - rootSeries k L 1) * (rootSeries k L 1 - rootSeries k L 0)⁻¹

lemma parameterCandidate_order (hL : 3 ≤ L) (heven : Even L) :
    (parameterCandidate k L).order = 1 := by
  obtain ⟨m, hm⟩ := heven
  have hLm : L = 2*m := by omega
  have hm2 : 2 ≤ m := by omega
  clear hm
  subst L
  have hroot : rootSeries k (2*m) 1 = tateX (2*m) m (1 : k) := by
    simp [rootSeries, show 2*m/2 = m by omega]
  have hr0 : PowerSeries.coeff 0 (rootSeries k (2*m) 1) = 0 := by
    rw [hroot]
    exact tateX_interior_constant _ _ _ (by omega) (by omega)
  have hr1 : PowerSeries.coeff 1 (rootSeries k (2*m) 1) = 0 := by
    rw [hroot]
    exact PowerSeries.X_pow_dvd_iff.mp (JPole.midpoint_divisible m (1 : k)) 1 hm2
  have hnum : (tateX (2*m) 1 (1 : k) - rootSeries k (2*m) 1).order = 1 := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · rw [map_sub, tateX_first_coeff k (2*m) hL, hr1]
      simpa using (one_ne_zero : (1 : k) ≠ 0)
    · intro i hi
      have : i = 0 := by omega
      subst i
      rw [map_sub, tateX_interior_constant _ _ _ (by omega) (by omega), hr0, sub_self]
  have hden : PowerSeries.constantCoeff (rootSeries k (2*m) 1 - rootSeries k (2*m) 0) =
      (1/4 : k) := by
    obtain ⟨h0, h1, _⟩ := JPole.root_constants (k := k) m (by omega)
    rw [map_sub, h0, h1]
    ring
  have hinv : IsUnit ((rootSeries k (2*m) 1 - rootSeries k (2*m) 0)⁻¹) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_inv, hden]
    norm_num
  rw [parameterCandidate, PowerSeries.order_mul, hnum,
    PowerSeries.order_zero_of_unit hinv, add_zero]

end LiteralCandidate

/-- A rational expression with an order-one image is already regular at the
center. Divisibility in the source DVR excludes the opposite fraction. -/
lemma isCompletedParameter_of_fraction
    (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) (f : PowerSeries k) (hf : f.order = 1)
    (a c : CuspStalk k L D X d) (hc : localMap k L D X d c ≠ 0)
    (heq : localMap k L D X d a = localMap k L D X d c * f) :
    IsCompletedParameter k L D X d := by
  obtain ⟨hdom, hdvr⟩ := cuspStalk_dvr k L D X b d hd
  letI := hdom
  letI := hdvr
  let σ := localMap k L D X d
  have hirr := irreducible_of_order_one k f hf
  have ha0 : σ a ≠ 0 := by
    rw [heq]
    exact mul_ne_zero hc hirr.ne_zero
  rcases ValuationRing.dvd_total a c with ⟨z, hz⟩ | ⟨z, hz⟩
  · exfalso
    have he : σ a * 1 = σ a * (σ z * f) := by
      simpa only [mul_one, hz, map_mul, mul_assoc] using heq
    have hu : IsUnit f := isUnit_iff_dvd_one.mpr
      ⟨σ z, by simpa [mul_comm] using (mul_left_cancel₀ ha0 he)⟩
    exact hirr.not_isUnit hu
  · have hzmap : σ z = f := by
      apply mul_left_cancel₀ hc
      simpa only [hz, map_mul] using heq
    apply isCompletedParameter_of_order_one k L D X b d hd z
    change (σ z).order = 1
    rw [hzmap, hf]

/-- The literal order-one candidate reduces the remaining geometry to a
specific fraction in the actual cusp stalk, with its denominator nonzero. -/
lemma isCompletedParameter_of_candidate_fraction (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d)
    (a c : CuspStalk k L D X d) (hc : localMap k L D X d c ≠ 0)
    (heq : localMap k L D X d a =
      localMap k L D X d c * parameterCandidate k L) :
    IsCompletedParameter k L D X d :=
  isCompletedParameter_of_fraction k L D X b d hd (parameterCandidate k L)
    (parameterCandidate_order k L hL heven) a c hc heq

section CoordinateDescent
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177 WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual projective inverse fixes the structural scalars on its affine chart. -/
lemma negChart_scalar :
    (ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W)).comp (chartScalar R W) =
      chartScalar R W := by
  suffices h : CommRingCat.ofHom
      ((ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W)).comp (chartScalar R W)) =
      CommRingCat.ofHom (chartScalar R W) by
    exact congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [chartScalar, CommRingCat.ofHom_hom, Spec.map_preimage]
  change Spec.map _ ≫ (zChartι W.toProjective ≫ _) = _
  rw [← Category.assoc, ← ProjectiveNeg.chart_factor W, Category.assoc]
  change zChartι W.toProjective ≫ WeierstrassProjModel.kw_lrAddNegDiag_negMor W ≫
    WeierstrassProjModel.projModelStrCR W.toProjective = _
  rw [WeierstrassProjModel.negMor_over]
  rfl

/-- The affine x-coordinate as a morphism to the relative affine line. -/
def chartXHom : Polynomial R →+* ChartRing R W :=
  Polynomial.eval₂RingHom (chartScalar R W) (xOverZ W.toProjective)

lemma negChart_chartXHom :
    (ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W)).comp (chartXHom W) =
      chartXHom W := by
  apply Polynomial.ringHom_ext
  · intro r
    change (ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W))
      (Polynomial.eval₂ (chartScalar R W) (xOverZ W.toProjective) (Polynomial.C r)) =
      Polynomial.eval₂ (chartScalar R W) (xOverZ W.toProjective) (Polynomial.C r)
    rw [Polynomial.eval₂_C]
    exact RingHom.congr_fun (negChart_scalar W) r
  · change (ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W))
      (Polynomial.eval₂ (chartScalar R W) (xOverZ W.toProjective) Polynomial.X) =
      Polynomial.eval₂ (chartScalar R W) (xOverZ W.toProjective) Polynomial.X
    rw [Polynomial.eval₂_X]
    exact ProjectiveNeg.chart_x W

/-- A section disjoint from the identity factors through the actual affine
Weierstrass chart, on an arbitrary test scheme. -/
lemma chartFactor_exists {T : Scheme.{u}} (P : T ⟶ Curve R W)
    (hP : Disjoint (Set.range P) (Set.range (origin R W))) :
    ∃ q : T ⟶ Spec (CommRingCat.of (ChartRing R W)), q ≫ chartInclusion R W = P := by
  have hrange : Set.range P ⊆ Set.range (zChartι W.toProjective) := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    by_contra h
    exact Set.disjoint_left.mp hP ⟨z, rfl⟩
      ((TwoTorsionAffineCoordinates.not_mem_basicOpen_iff_mem_range_kwZeroSect W (P z)).mp h)
  exact ⟨IsOpenImmersion.lift (zChartι W.toProjective) P hrange,
    IsOpenImmersion.lift_fac _ _ hrange⟩

/-- Inverting a marked point leaves this genuine x-coordinate morphism fixed. -/
lemma chartX_invariant {T : Scheme.{u}} (σ : T ⟶ T)
    (P : T ⟶ Curve R W) (q : T ⟶ Spec (CommRingCat.of (ChartRing R W)))
    (hq : q ≫ chartInclusion R W = P)
    (hσ : σ ≫ P = P ≫ WeierstrassProjModel.kw_lrAddNegDiag_negMor W) :
    σ ≫ (q ≫ Spec.map (CommRingCat.ofHom (chartXHom W))) =
      q ≫ Spec.map (CommRingCat.ofHom (chartXHom W)) := by
  have hqσ : σ ≫ q = q ≫ Spec.map (CommRingCat.ofHom
      (ProjectiveNeg.negChart W 2 (ProjectiveNeg.hfix2 W))) := by
    apply (cancel_mono (chartInclusion R W)).mp
    rw [Category.assoc, hq, Category.assoc]
    change σ ≫ P = q ≫ Spec.map _ ≫ zChartι W.toProjective
    rw [← ProjectiveNeg.chart_factor W, ← Category.assoc]
    exact hσ.trans (congrArg (fun f => f ≫ WeierstrassProjModel.kw_lrAddNegDiag_negMor W) hq.symm)
  rw [← Category.assoc, hqσ, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, negChart_chartXHom W]

end CoordinateDescent

section MarkedCoordinateDescent
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176 WeierstrassProjModel NeronModelInfra
open WeierstrassCurve.DrinfeldGlobal

lemma sign_combination {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    {T : Scheme.{u}} (t : T ⟶ Base R) (σ : T ⟶ T) (hσ : σ ≫ t = t)
    (x y : SchemeHomOver t (structureMap R W))
    (hx : σ ≫ x.val = (G.inv t x).val) (hy : σ ≫ y.val = (G.inv t y).val)
    (i j : ℕ) :
    σ ≫ (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val =
      (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val ≫ kw_lrAddNegDiag_negMor W := by
  have hx' : schemeHomOverComp σ hσ x = G.inv t x := Subtype.ext hx
  have hy' : schemeHomOverComp σ hσ y = G.inv t y := Subtype.ext hy
  have hp : schemeHomOverComp σ hσ (G.mul t (G.nsmul t i x) (G.nsmul t j y)) =
      G.inv t (G.mul t (G.nsmul t i x) (G.nsmul t j y)) := by
    rw [G.mul_natural, G.nsmul_natural, G.nsmul_natural, hx', hy']
    letI := G.pointGroup t
    simp only [FullLevelTorsionSplittingR0175.nsmul_pow]
    change x⁻¹ ^ i * y⁻¹ ^ j = (x ^ i * y ^ j)⁻¹
    rw [inv_pow, inv_pow, mul_inv_rev]
    exact hG.2 t _ _
  calc
    σ ≫ (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val =
      (G.inv t (G.mul t (G.nsmul t i x) (G.nsmul t j y))).val :=
        congrArg Subtype.val hp
    _ = _ := RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect W G hG.1 t _

/-- Every nonidentity residue combination has a genuine affine x-coordinate
on the same compatible sign quotient. Both original marking labels are used. -/
lemma marked_coordinate_descends (D : LevelData k L) (i j : Fin L)
    (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
    ∃ q : D.cover.space ⟶ Spec (CommRingCat.of (ChartRing (LegendreRing k) (legendre k))),
      q ≫ chartInclusion (LegendreRing k) (legendre k) =
        D.cover.inclusion ≫
          (D.atlas.law.mul D.atlas.level.projection
            (D.atlas.law.nsmul D.atlas.level.projection i.val D.atlas.level.level.x)
            (D.atlas.law.nsmul D.atlas.level.projection j.val D.atlas.level.level.y)).val ∧
      ∃! g : OpenBase k L D ⟶ Spec (CommRingCat.of (Polynomial (LegendreRing k))),
        D.quotient.quotient.q ≫ g = q ≫ Spec.map (CommRingCat.ofHom (chartXHom (legendre k))) := by
  let P := (D.atlas.law.mul D.atlas.level.projection
    (D.atlas.law.nsmul D.atlas.level.projection i.val D.atlas.level.level.x)
    (D.atlas.law.nsmul D.atlas.level.projection j.val D.atlas.level.level.y)).val
  have havoid : Disjoint (Set.range (D.cover.inclusion ≫ P))
      (Set.range (origin (LegendreRing k) (legendre k))) := by
    apply (D.atlas.level.level.avoids i j hij).mono_left
    rintro _ ⟨z, rfl⟩
    exact ⟨D.cover.inclusion z, rfl⟩
  obtain ⟨q, hq⟩ := chartFactor_exists (legendre k) (D.cover.inclusion ≫ P) havoid
  refine ⟨q, hq, ?_⟩
  apply D.quotient.quotient.universal
  apply chartX_invariant (legendre k) D.quotient.sign (D.cover.inclusion ≫ P) q hq
  rw [← Category.assoc, D.quotient.sign_eq, Category.assoc]
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  letI : IsDomain (LegendreRing k) := (legendre_family_geometry k).1
  letI : IsNoetherianRing (LegendreRing k) := (legendre_family_geometry k).2.1
  have hP := sign_combination (legendre k) D.atlas.law D.atlas.originLaw
    D.atlas.level.projection D.atlas.sign.map D.atlas.sign.over_eq
    D.atlas.level.level.x D.atlas.level.level.y D.atlas.sign.x_eq D.atlas.sign.y_eq i.val j.val
  change D.cover.inclusion ≫ D.atlas.sign.map ≫ P = _
  rw [hP, Category.assoc]

/-- The descended coordinate is an element of the actual compatible quotient
ring. Its evaluation is fixed by the marked point, independently of the chart
factorization used to represent that point. -/
lemma marked_x_function (D : LevelData k L) (i j : Fin L)
    (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
    ∃ x : D.quotient.quotient.ring,
      ∀ (S : Type u) [CommRing S] (a : Base S ⟶ D.cover.space)
        (χ : ChartRing (LegendreRing k) (legendre k) →+* S),
        a ≫ D.cover.inclusion ≫
            (D.atlas.law.mul D.atlas.level.projection
              (D.atlas.law.nsmul D.atlas.level.projection i.val D.atlas.level.level.x)
              (D.atlas.law.nsmul D.atlas.level.projection j.val D.atlas.level.level.y)).val =
          Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion (LegendreRing k) (legendre k) →
        (Spec.preimage (a ≫ D.quotient.quotient.q)).hom x =
          χ (xOverZ (legendre k).toProjective) := by
  obtain ⟨q, hq, g, hg, _⟩ := marked_coordinate_descends k L D i j hij
  refine ⟨(Spec.preimage g).hom Polynomial.X, ?_⟩
  intro S _ a χ hχ
  have haq : a ≫ q = Spec.map (CommRingCat.ofHom χ) := by
    apply (cancel_mono (chartInclusion (LegendreRing k) (legendre k))).mp
    rw [Category.assoc, hq]
    exact hχ
  have he : (a ≫ D.quotient.quotient.q) ≫ g =
      Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartXHom (legendre k))) := by
    rw [Category.assoc, hg, ← Category.assoc, haq]
  have hr : (Spec.preimage g ≫ Spec.preimage (a ≫ D.quotient.quotient.q)).hom =
      (χ.comp (chartXHom (legendre k))) := by
    have hh : Spec.preimage g ≫ Spec.preimage (a ≫ D.quotient.quotient.q) =
        CommRingCat.ofHom (chartXHom (legendre k)) ≫ CommRingCat.ofHom χ := by
      apply Spec.map_injective
      simpa only [Spec.map_comp, Spec.map_preimage] using he
    exact congrArg CommRingCat.Hom.hom hh
  have hx := RingHom.congr_fun hr Polynomial.X
  simpa [chartXHom] using hx

end MarkedCoordinateDescent

section CoordinateRatios
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177
open OrderedLegendreParameterRigidity
open WeierstrassCurve.DrinfeldGlobal

/-- Ratios of differences of three actual x-coordinates are preserved by
pointed isomorphisms. The chart equivalence and its affine transformation come
from the accepted polar-filtration theorem. -/
lemma coordinate_ratio_of_pointed_iso
    (K : Type u) [Field K] [CharZero K] (W V : WeierstrassCurve K)
    (hw : W.a₁ = 0) (hv : V.a₁ = 0)
    (e : Curve K W ≅ Curve K V)
    (he : e.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K V)
    (p : Fin 3 → (Base K ⟶ Curve K W))
    (v : Fin 3 → (Base K ⟶ Curve K V))
    (x y z w : Fin 3 → K)
    (hp : ∀ i, HasCoordinates K W (p i) (x i) (y i))
    (hv' : ∀ i, HasCoordinates K V (v i) (z i) (w i))
    (hmap : ∀ i, p i ≫ e.hom = v i) :
    (x 0 - x 1) / (x 1 - x 2) = (z 0 - z 1) / (z 1 - z 2) := by
  obtain ⟨c, a, r, hc, hx, _⟩ :=
    TateLevelClassifyingParameter.affine_x_transform K W V hw hv e he ho
  have hz (i : Fin 3) : z i = (a : K) * x i + r := by
    obtain ⟨hpo, χ, hχ, hχx, hχy⟩ := hp i
    obtain ⟨hvo, ψ, hψ, hψx, hψy⟩ := hv' i
    have hs := evaluation_scalar W χ (hχ.symm ▸ hpo)
    have hf := evaluation_comp W V e.hom c.toRingHom hc χ ψ
      (by rw [← hχ, ← hψ]; exact hmap i)
    have hi := RingHom.congr_fun hf (xOverZ V.toProjective)
    change χ (c (xOverZ V.toProjective)) = ψ (xOverZ V.toProjective) at hi
    rw [hx, map_add, map_mul, hs, hs, hχx, hψx] at hi
    exact hi.symm
  rw [hz 0, hz 1, hz 2]
  rw [show (a : K) * x 0 + r - ((a : K) * x 1 + r) = (a : K) * (x 0 - x 1) by ring,
    show (a : K) * x 1 + r - ((a : K) * x 2 + r) = (a : K) * (x 1 - x 2) by ring]
  exact (mul_div_mul_left _ _ (Units.ne_zero a)).symm

end CoordinateRatios

section CombinationTransport
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra WeierstrassProjModel

/-- A Cartesian pointed comparison transports every residue combination of
the two given labels, with the original coefficient and base maps retained. -/
lemma combination_transport
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} [V.IsElliptic]
    (G : Law R W) (H : Law S V)
    (hG : IsOriginLaw R W G) (hH : IsOriginLaw S V H)
    (σ : R →+* S) (f : Curve S V ⟶ Curve R W)
    (hf : IsBaseChange R W G S V H σ f)
    {T : Scheme.{u}} (t : T ⟶ Base R) (a : Base S ⟶ T)
    (ha : a ≫ t = baseMap R S σ)
    (x y : SchemeHomOver t (structureMap R W))
    (xs ys : SchemeHomOver (𝟙 (Base S)) (structureMap S V))
    (hx : xs.val ≫ f = a ≫ x.val) (hy : ys.val ≫ f = a ≫ y.val)
    (i j : ℕ) :
    (H.mul (𝟙 _) (H.nsmul (𝟙 _) i xs) (H.nsmul (𝟙 _) j ys)).val ≫ f =
      a ≫ (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val := by
  have ha' : a ≫ t = (𝟙 (Base S)) ≫ baseMap R S σ :=
    ha.trans (Category.id_comp _).symm
  have hx' : BaseChange.point hf (𝟙 _) xs = schemeHomOverComp a ha' x := Subtype.ext hx
  have hy' : BaseChange.point hf (𝟙 _) ys = schemeHomOverComp a ha' y := Subtype.ext hy
  have hh : BaseChange.point hf (𝟙 _)
      (H.mul (𝟙 _) (H.nsmul (𝟙 _) i xs) (H.nsmul (𝟙 _) j ys)) =
      schemeHomOverComp a ha' (G.mul t (G.nsmul t i x) (G.nsmul t j y)) := by
    rw [BaseChange.point_mul hf hG hH, BaseChange.point_nsmul, BaseChange.point_nsmul,
      hx', hy', G.mul_natural, G.nsmul_natural, G.nsmul_natural]
  exact congrArg Subtype.val hh

end CombinationTransport

section PresentedCoordinates
open CategoryTheory.Limits
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaCompatibleLevelR0178
open CompatibleClassifyingUniqueness WeierstrassCurve.DrinfeldGlobal

/-- A selected descended function, in the same ring as the classifying base. -/
def markedX (D : LevelData k L) (i j : Fin L) (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
    D.quotient.quotient.ring := (marked_x_function k L D i j hij).choose

/-- Evaluation of the descended function on a coefficient presentation is the
literal affine coordinate of that presentation's marked combination. -/
lemma markedX_presentation (D : LevelData k L) (i j : Fin L)
    (hij : i.val ≠ 0 ∨ j.val ≠ 0)
    (K : Type u) [Field K] (α : LegendreRing k →+* K)
    (a : Base K ⟶ D.cover.space)
    (ha : (a ≫ D.cover.inclusion) ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α))
    (P : Presentation k L D.atlas K α (a ≫ D.cover.inclusion))
    (x y : K)
    (hxy : HasCoordinates K ((legendre k).map α)
      (coordinatePoint K ((legendre k).map α) P.law P.marking i j) x y) :
    (Spec.preimage (a ≫ D.quotient.quotient.q)).hom (markedX k L D i j hij) = x := by
  letI : IsDomain (LegendreRing k) := (legendre_family_geometry k).1
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  obtain ⟨hp, χ, hχ, hχx, hχy⟩ := hxy
  let h := WeierstrassProjModel.exists_isCoefficientHom (legendre k).toProjective α
  obtain ⟨c, hc, hcx, hcy⟩ := OrderedLegendreParameterRigidity.coefficient_chart
    (legendre k) α h.choose h.choose_spec.choose h.choose_spec.choose_spec
  have hcoeff : P.coeff = AlgebraicGeometry.Proj.map h.choose h.choose_spec.choose := P.coeff_eq
  have ht := combination_transport D.atlas.law P.law D.atlas.originLaw P.originLaw
    α P.coeff P.coefficient D.atlas.level.projection (a ≫ D.cover.inclusion) ha
    D.atlas.level.level.x D.atlas.level.level.y P.marking.x P.marking.y
    P.x_coeff P.y_coeff i.val j.val
  have he := (marked_x_function k L D i j hij).choose_spec K a (χ.comp c) (by
    rw [← Category.assoc]
    rw [← ht]
    change coordinatePoint K ((legendre k).map α) P.law P.marking i j ≫ P.coeff = _
    rw [hχ, Category.assoc, hcoeff, hc, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  exact he.trans (by rw [RingHom.comp_apply, hcx, hχx])

/-- Retain the lift to the compatible cover when unpacking the accepted
classifying comparison. This keeps evaluation tied to the given base map. -/
lemma classified_presentation (D : LevelData k L) (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (K : Type u) [Field K] [IsAlgClosed K] (σ : LaurentSeries k →+* K) :
    ∃ (α : LegendreRing k →+* K) (a : Base K ⟶ D.cover.space)
      (P : Presentation k L D.atlas K α (a ≫ D.cover.inclusion))
      (g : Curve K ((legendre k).map α) ⟶ Curve (LaurentSeries k) (TateCurve k L)),
      (a ≫ D.cover.inclusion) ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α) ∧
      a ≫ D.quotient.quotient.q = Spec.map (CommRingCat.ofHom σ) ≫ b ∧
      IsPullback g (structureMap K ((legendre k).map α))
        (structureMap (LaurentSeries k) (TateCurve k L)) (Spec.map (CommRingCat.ofHom σ)) ∧
      origin K ((legendre k).map α) ≫ g =
        Spec.map (CommRingCat.ofHom σ) ≫ origin (LaurentSeries k) (TateCurve k L) ∧
      P.marking.x.val ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ E.marking.x.val ∧
      P.marking.y.val ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ E.marking.y.val := by
  obtain ⟨f, hf⟩ := hb
  let s := Spec.map (CommRingCat.ofHom σ)
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨a, ha⟩ := lift_geometric_point D.quotient.quotient.q (s ≫ b)
  let α := (Spec.preimage ((a ≫ D.cover.inclusion) ≫ D.atlas.level.projection)).hom
  have hα : (a ≫ D.cover.inclusion) ≫ D.atlas.level.projection =
      Spec.map (CommRingCat.ofHom α) := (Spec.map_preimage _).symm
  obtain ⟨P⟩ := presentation_exists k L D.atlas K α (a ≫ D.cover.inclusion) hα
  have haq : (a ≫ D.cover.inclusion) ≫ D.atlas.quotient.q =
      s ≫ (b ≫ D.quotient.inclusion) := by
    rw [Category.assoc, D.quotient.cartesian.w, ← Category.assoc, ha, Category.assoc]
  obtain ⟨g, hg, hgo, hgx, hgy⟩ := comparison_to_source P E.marking s
    (b ≫ D.quotient.inclusion) f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 haq
  exact ⟨α, a, P, g, hα, ha, hg, hgo, hgx, hgy⟩

/-- Every nonidentity label has actual affine coordinates. -/
lemma combination_hasCoordinates {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R))) (i j : Fin L)
    (hij : i.val ≠ 0 ∨ j.val ≠ 0) :
    ∃ x y : R, HasCoordinates R W (coordinatePoint R W G M i j) x y := by
  obtain ⟨χ, hχ⟩ := TwoTorsionAffineCoordinates.exists_chart_factorization W
    (coordinatePoint R W G M i j) (M.avoids i j hij)
  exact ⟨χ (xOverZ W.toProjective), χ (yOverZ W.toProjective),
    FullLevelTorsionSplittingR0175.coordinate_over G M i j, χ, hχ, rfl, rfl⟩

/-- The ratio of three descended marked coordinates pulls back to the ratio
of the actual Tate coordinates, for the given arbitrary full marking. -/
lemma classified_coordinate_ratio (D : LevelData k L) (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (i j : Fin 3 → Fin L) (hij : ∀ n, (i n).val ≠ 0 ∨ (j n).val ≠ 0)
    (x y : Fin 3 → LaurentSeries k)
    (hxy : ∀ n, HasCoordinates (LaurentSeries k) (TateCurve k L)
      (coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking (i n) (j n)) (x n) (y n)) :
    let z := fun n => (Spec.preimage b).hom (markedX k L D (i n) (j n) (hij n))
    (z 0 - z 1) / (z 1 - z 2) = (x 0 - x 1) / (x 1 - x 2) := by
  let K := AlgebraicClosure (LaurentSeries k)
  let σ := algebraMap (LaurentSeries k) K
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  letI : CharZero K := charZero_of_injective_ringHom σ.injective
  letI := E.elliptic
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  obtain ⟨α, a, P, g, ha, haq, hg, hgo, hgx, hgy⟩ :=
    classified_presentation k L D E b hb K σ
  have hbase := MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    E.law P.law E.originLaw P.originLaw σ g hg hgo
  let p := fun n => coordinatePoint K ((legendre k).map α) P.law P.marking (i n) (j n)
  have hcoords : ∀ n, ∃ xp yp, HasCoordinates K ((legendre k).map α) (p n) xp yp :=
    fun n => combination_hasCoordinates L _ _ P.marking (i n) (j n) (hij n)
  choose xp yp hcoords using hcoords
  have hx (n : Fin 3) : xp n = σ ((Spec.preimage b).hom
      (markedX k L D (i n) (j n) (hij n))) := by
    have hv := markedX_presentation k L D (i n) (j n) (hij n) K α a ha P
      (xp n) (yp n) (hcoords n)
    rw [haq] at hv
    have he : (Spec.preimage (Spec.map (CommRingCat.ofHom σ) ≫ b)).hom =
        σ.comp (Spec.preimage b).hom := by
      have hh : Spec.preimage (Spec.map (CommRingCat.ofHom σ) ≫ b) =
          Spec.preimage b ≫ CommRingCat.ofHom σ := by
        apply Spec.map_injective
        rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      exact congrArg CommRingCat.Hom.hom hh
    rw [he] at hv
    exact hv.symm
  obtain ⟨c, _, hc, hco, _, _, _, hlift⟩ :=
    NormalFormConstruction.coefficient_comparison (TateCurve k L) σ
  have hl : ∀ n, ∃ q : Base K ⟶ Curve K ((TateCurve k L).map σ),
      HasCoordinates K ((TateCurve k L).map σ) q (σ (x n)) (σ (y n)) ∧
      q ≫ c = Spec.map (CommRingCat.ofHom σ) ≫
        coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking (i n) (j n) :=
    fun n => hlift _ _ _ (hxy n)
  choose q hq hqc using hl
  obtain ⟨e, hep, hec⟩ := OrderedLegendreParameterRigidity.cartesian_iso
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap K ((legendre k).map α)) (structureMap K ((TateCurve k L).map σ))
    (Spec.map (CommRingCat.ofHom σ)) g c hg hc (Iso.refl _) (Category.id_comp _)
  simp only [Iso.refl_hom, Category.comp_id] at hec
  have heo : origin K ((legendre k).map α) ≫ e.hom = origin K ((TateCurve k L).map σ) := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hgo, hco]
    · rw [Category.assoc, hep, BaseChange.origin_over, BaseChange.origin_over]
  have hpq (n : Fin 3) : p n ≫ e.hom = q n := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hqc]
      exact combination_transport E.law P.law E.originLaw P.originLaw σ g hbase
        (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (Category.comp_id _)
        E.marking.x E.marking.y P.marking.x P.marking.y hgx hgy (i n).val (j n).val
    · rw [Category.assoc, hep, (hcoords n).1, (hq n).1]
  have hr := coordinate_ratio_of_pointed_iso K ((legendre k).map α) ((TateCurve k L).map σ)
    (by simp [legendre]) (by simp [TateCurve, ArithmeticThetaCompactifiedDifferentialR0145.curve])
    e hep heo p q xp yp (fun n => σ (x n)) (fun n => σ (y n)) hcoords hq hpq
  simp only [hx] at hr
  apply σ.injective
  simpa only [map_div₀, map_sub] using hr

end PresentedCoordinates

section LocalFractions

/-- The disk germ is injective: a nonzero kernel in the cusp DVR would send
the generic point to the same boundary point as the closed point, contradicting
the prescribed restriction to the open level curve. -/
lemma localMap_injective (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) : Function.Injective (localMap k L D X d) := by
  obtain ⟨hdom, hdvr⟩ := cuspStalk_dvr k L D X b d hd
  letI := hdom
  letI := hdvr
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  by_contra hker
  have hmax : RingHom.ker (localMap k L D X d) =
      IsLocalRing.maximalIdeal (CuspStalk k L D X d) :=
    IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime (localMap k L D X d)).isMaximal hker)
  have hpoint : Spec.map (CommRingCat.ofHom (localMap k L D X d))
      (⊥ : PrimeSpectrum (PowerSeries k)) =
      IsLocalRing.closedPoint (CuspStalk k L D X d) := by
    apply PrimeSpectrum.ext
    exact hmax
  have hgen : genericInclusion k (⊥ : PrimeSpectrum (LaurentSeries k)) =
      (⊥ : PrimeSpectrum (PowerSeries k)) := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
  have heq : d (⊥ : PrimeSpectrum (PowerSeries k)) = d (closedPoint k) := by
    calc
      _ = (Spec.map (Scheme.stalkClosedPointTo d) ≫
          X.space.fromSpecStalk (d (closedPoint k))) (⊥ : PrimeSpectrum (PowerSeries k)) :=
        congrArg (fun f : Disk k ⟶ X.space => f (⊥ : PrimeSpectrum (PowerSeries k)))
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk d).symm
      _ = _ := by
        rw [Scheme.Hom.comp_apply]
        change X.space.fromSpecStalk (d (closedPoint k))
          (Spec.map (CommRingCat.ofHom (localMap k L D X d)) (⊥ : PrimeSpectrum (PowerSeries k))) = _
        rw [hpoint, Scheme.fromSpecStalk_closedPoint]
  have ht := congrArg (fun f : Puncture k ⟶ X.space =>
    f (⊥ : PrimeSpectrum (LaurentSeries k))) hd.2.1
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hgen, heq] at ht
  exact hd.2.2 ⟨b (⊥ : PrimeSpectrum (LaurentSeries k)), ht.symm⟩

/-- Every ratio from the actual open quotient is a fraction of the cusp
stalk whose denominator has nonzero disk image. Only the local DVR is used;
the compactification need not be connected or integral. -/
lemma open_ratio_fraction (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) (r s : D.quotient.quotient.ring) :
    ∃ a c : CuspStalk k L D X d, localMap k L D X d c ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) (localMap k L D X d a) =
        algebraMap (PowerSeries k) (LaurentSeries k) (localMap k L D X d c) *
          ((Spec.preimage b).hom r / (Spec.preimage b).hom s) := by
  obtain ⟨hdom, hdvr⟩ := cuspStalk_dvr k L D X b d hd
  letI := hdom
  letI := hdvr
  letI := X.openImmersion
  let A := CuspStalk k L D X d
  let F := FractionRing A
  let f : A →+* LaurentSeries k :=
    (algebraMap (PowerSeries k) (LaurentSeries k)).comp (localMap k L D X d)
  have hf : Function.Injective f :=
    (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
      (localMap_injective k L D X b d hd)
  let θ : F →+* LaurentSeries k := IsFractionRing.lift hf
  have hθ : θ.comp (algebraMap A F) = f := by
    apply RingHom.ext
    intro x
    exact IsFractionRing.lift_algebraMap (K := F) hf x
  let η : Spec (CommRingCat.of F) ⟶ X.space :=
    Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ X.space.fromSpecStalk (d (closedPoint k))
  have hη : Spec.map (CommRingCat.ofHom θ) ≫ η = b ≫ X.inclusion := by
    rw [show η = Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫
      X.space.fromSpecStalk (d (closedPoint k)) from rfl,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ]
    change Spec.map (CommRingCat.ofHom
      ((algebraMap (PowerSeries k) (LaurentSeries k)).comp (localMap k L D X d))) ≫ _ = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    change genericInclusion k ≫ (Spec.map (Scheme.stalkClosedPointTo d) ≫
      X.space.fromSpecStalk (d (closedPoint k))) = _
    have hfac : Spec.map (Scheme.stalkClosedPointTo d) ≫
        X.space.fromSpecStalk (d (closedPoint k)) = d :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk d
    exact (congrArg (fun v => genericInclusion k ≫ v) hfac).trans hd.2.1
  have hrange : Set.range η ⊆ Set.range X.inclusion := by
    rintro _ ⟨z, rfl⟩
    let w : Puncture k := (⊥ : PrimeSpectrum (LaurentSeries k))
    have hz : Spec.map (CommRingCat.ofHom θ) w = z := Subsingleton.elim _ _
    refine ⟨b w, ?_⟩
    have hh := congrArg (fun g : Puncture k ⟶ X.space => g w) hη
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hh
    exact hh.symm
  let β := IsOpenImmersion.lift X.inclusion η hrange
  have hβ : β ≫ X.inclusion = η := IsOpenImmersion.lift_fac _ _ _
  have hβb : Spec.map (CommRingCat.ofHom θ) ≫ β = b := by
    apply (cancel_mono X.inclusion).mp
    rw [Category.assoc, hβ, hη]
  let φ := (Spec.preimage β).hom
  have hφ : θ.comp φ = (Spec.preimage b).hom := by
    have hh : Spec.preimage β ≫ CommRingCat.ofHom θ = Spec.preimage b := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
      exact hβb
    exact congrArg CommRingCat.Hom.hom hh
  obtain ⟨a, c, hc, he⟩ := IsFractionRing.div_surjective A (φ r / φ s)
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have hfc : f c ≠ 0 := fun h => hc0 (hf (h.trans (map_zero f).symm))
  refine ⟨a, c, fun h => hfc (by
    change algebraMap (PowerSeries k) (LaurentSeries k) (localMap k L D X d c) = 0
    rw [h, map_zero]), ?_⟩
  have hv := congrArg θ he
  rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap (K := F) hf,
    IsFractionRing.lift_algebraMap (K := F) hf] at hv
  have hv' : f a / f c = (Spec.preimage b).hom r / (Spec.preimage b).hom s := by
    simpa only [← RingHom.comp_apply, hφ] using hv
  exact ((div_eq_iff hfc).mp hv').trans (mul_comm _ _)

/-- An order-one coordinate ratio on the open base proves the completion
statement for the specific disk stalk map. -/
lemma isCompletedParameter_of_open_ratio (D : LevelData k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hd : Extends k L D X b d) (r s : D.quotient.quotient.ring)
    (f : PowerSeries k) (hf : f.order = 1)
    (he : (Spec.preimage b).hom r / (Spec.preimage b).hom s =
      algebraMap (PowerSeries k) (LaurentSeries k) f) :
    IsCompletedParameter k L D X d := by
  obtain ⟨a, c, hc, hac⟩ := open_ratio_fraction k L D X b d hd r s
  apply isCompletedParameter_of_fraction k L D X b d hd f hf a c hc
  apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  rw [map_mul]
  exact hac.trans (congrArg (fun z =>
    algebraMap (PowerSeries k) (LaurentSeries k) (localMap k L D X d c) * z) he)

end LocalFractions

section TorsionGeneration
open CategoryTheory.Limits
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra

/-- Over a field, the accepted scheme-theoretic full-torsion splitting says
that every killed point is one of the residue combinations of the given labels. -/
lemma full_level_generates (K : Type u) [Field K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W)
    (hG : IsOriginLaw K W G) (hL : 0 < L)
    (M : FullLevel K W G L (𝟙 (Base K)))
    (P : SchemeHomOver (𝟙 (Base K)) (structureMap K W))
    (hP : G.nsmul (𝟙 _) L P = G.one (𝟙 _)) :
    ∃ i j : Fin L, P.val = coordinatePoint K W G M i j := by
  letI : IsProper (structureMap K W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin K W) := by
    have h : IsClosedImmersion (origin K W ≫ structureMap K W) := by
      rw [BaseChange.origin_over]
      infer_instance
    exact IsClosedImmersion.of_comp (origin K W) (structureMap K W)
  have hk : P.val ≫ G.schemeNsmul L = (𝟙 (Base K)) ≫ origin K W := by
    rw [← FullLevelTorsionSplittingR0175.nsmul_val G, hP]
    exact hG.1 _
  let T := pullback (G.schemeNsmul L) (origin K W)
  let t : Base K ⟶ T := pullback.lift P.val (𝟙 _) hk
  let I := torsionIdeal K W G L
  have hI : I.subschemeι.ker = (pullback.fst (G.schemeNsmul L) (origin K W)).ker := by
    rw [I.ker_subschemeι]
    exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (origin K W) (G.schemeNsmul L)).symm
  have hker : I.subschemeι.ker ≤ P.val.ker := by
    rw [hI, show P.val = t ≫ pullback.fst (G.schemeNsmul L) (origin K W) from
      (pullback.lift_fst _ _ _).symm]
    exact Scheme.Hom.le_ker_comp _ _
  let l := IsClosedImmersion.lift I.subschemeι P.val hker
  have hl : l ≫ I.subschemeι = P.val := IsClosedImmersion.lift_fac _ _ _
  obtain ⟨e, he, hem⟩ := full_level_torsion_splitting K W G hG L hL M
  let q := l ≫ e.hom
  have hq : q ≫ torsionStructure K L = 𝟙 _ := by
    rw [show q = l ≫ e.hom from rfl, Category.assoc, he, ← Category.assoc, hl]
    exact P.property
  obtain ⟨⟨ij, z⟩, hz⟩ := (PrimeSpectrum.sigmaToPi_bijective
    (fun _ : Fin L × Fin L => K)).surjective (q (⊥ : PrimeSpectrum K))
  have hcomp : torsionComponent K L ij.1 ij.2 ≫ torsionStructure K L = 𝟙 _ := by
    rw [torsionComponent, torsionStructure, ← Spec.map_comp]
    exact Spec.map_id _
  have hqcomp : q = torsionComponent K L ij.1 ij.2 := by
    apply ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.section_eq_of_range_subset
      (torsionStructure K L) q _ hq hcomp
    rintro _ ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    change PrimeSpectrum.sigmaToPi (fun _ : Fin L × Fin L => K) ⟨ij, z⟩ = q w
    rw [hz, Subsingleton.elim (⊥ : PrimeSpectrum K) w]
  refine ⟨ij.1, ij.2, ?_⟩
  calc
    P.val = l ≫ I.subschemeι := hl.symm
    _ = q ≫ e.inv ≫ I.subschemeι := by simp [q]
    _ = _ := by rw [hqcomp]; exact hem ij.1 ij.2

end TorsionGeneration

section LiteralTorsion
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open NeronModelInfra

/-- The accepted transport of group laws preserves all natural multiples. -/
lemma transported_nsmul {R : Type u} [CommRing R] {A B : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ B) (he : e.hom ≫ g = f)
    (G : WeierstrassProjModel.RelativeGroupLaw R g)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t f) (n : ℕ) :
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he t
      ((ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport e he G).nsmul t n P) =
      G.nsmul t n (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he t P) := by
  induction n with
  | zero => exact Equiv.apply_symm_apply _ _
  | succ n ih =>
    simp only [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ]
    change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he t)
      ((ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he t).symm
      (G.mul t _ _)) = _
    rw [Equiv.apply_symm_apply, ih]

/-- A literal nonidentity marked point with a^L=1 is killed by L on the
specified Tate cubic and the specified origin law. This transports the
accepted marked-point addition and coordinate realization from the actual
algebraized polygon model. -/
lemma literal_torsion_point (hL : 3 ≤ L) (heven : Even L) (E : TateLevel k L)
    (i : Fin L) (a : kˣ) (ha : a ^ L = 1) (hne : i.val ≠ 0 ∨ (a : k) ≠ 1) :
    ∃ P : SchemeHomOver (𝟙 (Puncture k))
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)),
      E.law.nsmul (𝟙 _) L P = E.law.one (𝟙 _) ∧
      ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k L) P.val
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L i.val (a : k)))
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L i.val (a : k))) := by
  have hpos : 0 < L := by omega
  obtain ⟨T, _⟩ := proper_flat_polygon_tower k L hpos hL
  obtain ⟨basis, hb, hbr, _⟩ := ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis
    k L hpos hL T (fun _ => 1) 3 (by omega)
  have hbas : CompatibleBases k T (fun _ => 1) basis := ⟨hb, hbr⟩
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k L hpos hL T (fun _ => 1) basis hbas
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k L hpos hL T (fun _ => 1) basis hbas j hj
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k L hpos hL T M hM (zeroIndex L hpos) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs true
  obtain ⟨cubic, hcubic, _⟩ := generic_affine_cubic_isomorphism
    k L hpos hL T heven M hM s hs X Y hX hY
  obtain ⟨chart, hchart, _⟩ := projective_cubic_chart k L
  obtain ⟨e, he, _⟩ := compactified_coordinate_isomorphism
    k L hpos hL T heven M hM s hs X Y hX hY cubic hcubic chart hchart
  let G := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport e he.1 E.law
  have hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G := by
    constructor
    · intro V t
      apply Subtype.ext
      change (E.law.one t).val ≫ e.inv = t ≫ genericPoint k M s hs.1
      rw [E.originLaw.1]
      change (t ≫ origin k L) ≫ e.inv = _
      rw [← he.2.2, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro V t x y
      apply (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 t).injective
      change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 t)
        ((ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 t).symm
        (E.law.mul t _ _)) =
        (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 t)
        ((ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 t).symm
        (E.law.mul t _ _))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, E.originLaw.2]
  obtain ⟨p, hp, _⟩ := marked_section_algebraization k L hpos hL T M hM i a
  let Q := ArithmeticThetaMarkedGroupLawR0146.pointOver k M (𝟙 _) p hp.1
  let P := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 (𝟙 _) Q
  have hk : G.nsmul (𝟙 _) L Q = G.one (𝟙 _) :=
    (ArithmeticThetaMarkedGroupLawR0146.marked_exact_torsion
      k L hpos hL T heven M hM s hs G hG i a p hp L).mpr ⟨dvd_mul_right L i.val, ha⟩
  have hkill : E.law.nsmul (𝟙 _) L P = E.law.one (𝟙 _) := by
    have ht := transported_nsmul e he.1 E.law (𝟙 _) Q L
    change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv e he.1 (𝟙 _))
      (G.nsmul (𝟙 _) L Q) = _ at ht
    rw [hk] at ht
    exact ht.symm.trans (Equiv.apply_symm_apply _ _)
  obtain ⟨χ, hχ, hx, hy⟩ := ArithmeticThetaHodgeFourTorsionR0147.marked_coordinate_chart
    k L hpos hL T heven M hM s hs X Y hX hY cubic hcubic chart hchart e he i a p hp hne
  exact ⟨P, hkill, P.property, χ, hχ, hx, hy⟩

end LiteralTorsion

section FinalAssembly
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaTateSeries ArithmeticThetaCubicModelR0144

/-- Literal nonidentity torsion points occur among the nonzero combinations
of every given full marking. No primitive root is chosen. -/
lemma literal_marking_indices (hL : 3 ≤ L) (heven : Even L) (E : TateLevel k L)
    (i : Fin L) (a : kˣ) (ha : a ^ L = 1) (hne : i.val ≠ 0 ∨ (a : k) ≠ 1) :
    ∃ m n : Fin L, (m.val ≠ 0 ∨ n.val ≠ 0) ∧
      HasCoordinates (LaurentSeries k) (TateCurve k L)
        (coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking m n)
        (algebraMap (PowerSeries k) (LaurentSeries k) (tateX L i.val (a : k)))
        (algebraMap (PowerSeries k) (LaurentSeries k) (tateY L i.val (a : k))) := by
  letI := E.elliptic
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  obtain ⟨P, hk, hcoords⟩ := literal_torsion_point k L hL heven E i a ha hne
  obtain ⟨m, n, hmn⟩ := full_level_generates L (LaurentSeries k) (TateCurve k L)
    E.law E.originLaw (by omega) E.marking P hk
  have hnz : m.val ≠ 0 ∨ n.val ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : P.val = origin (LaurentSeries k) (TateCurve k L) := by
      rw [hmn, coordinatePoint, h.1, h.2, E.law.nsmul_zero, E.law.nsmul_zero, E.law.mul_one, E.originLaw.1,
        Category.id_comp]
    obtain ⟨_, χ, hχ, _, _⟩ := hcoords
    have hz := congrArg (fun f : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k L) =>
      f (⊥ : PrimeSpectrum (LaurentSeries k))) (hzero.symm.trans hχ)
    exact ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.origin_not_chart
      k L (⊥ : PrimeSpectrum (LaurentSeries k))
      ⟨Spec.map (CommRingCat.ofHom χ) (⊥ : PrimeSpectrum (LaurentSeries k)), hz.symm⟩
  exact ⟨m, n, hnz, hmn ▸ hcoords⟩

lemma parameterCandidate_laurent (hL : 3 ≤ L) (heven : Even L) :
    algebraMap (PowerSeries k) (LaurentSeries k) (parameterCandidate k L) =
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX L 1 1) -
        algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k L 1)) /
      (algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k L 1) -
        algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k L 0)) := by
  let δ := rootSeries k L 1 - rootSeries k L 0
  have hδ : PowerSeries.constantCoeff δ ≠ 0 := by
    obtain ⟨m, hm⟩ := heven
    have hLm : L = 2*m := by omega
    obtain ⟨h0, h1, _⟩ := JPole.root_constants (k := k) m (by omega)
    dsimp [δ]
    rw [hLm, map_sub, h0, h1]
    norm_num
  have hi : algebraMap (PowerSeries k) (LaurentSeries k) δ⁻¹ =
      (algebraMap (PowerSeries k) (LaurentSeries k) δ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, PowerSeries.inv_mul_cancel δ hδ, map_one]
  rw [parameterCandidate, map_mul, hi, map_sub, div_eq_mul_inv]
  rw [show δ = rootSeries k L 1 - rootSeries k L 0 from rfl, map_sub]

/-- The required order-one series is the pullback of a ratio of functions on
the same compatible full-level quotient. -/
lemma candidate_open_ratio (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    ∃ r s : D.quotient.quotient.ring,
      (Spec.preimage b).hom r / (Spec.preimage b).hom s =
        algebraMap (PowerSeries k) (LaurentSeries k) (parameterCandidate k L) := by
  obtain ⟨i0, j0, hn0, h0⟩ := literal_marking_indices k L hL heven E
    ⟨1, by omega⟩ 1 (by simp) (Or.inl (by norm_num))
  obtain ⟨i1, j1, hn1, h1⟩ := literal_marking_indices k L hL heven E
    ⟨L/2, by omega⟩ 1 (by simp) (Or.inl (by dsimp; omega))
  obtain ⟨i2, j2, hn2, h2⟩ := literal_marking_indices k L hL heven E
    ⟨0, by omega⟩ (-1) heven.neg_one_pow (Or.inr (by norm_num))
  let i : Fin 3 → Fin L := ![i0, i1, i2]
  let j : Fin 3 → Fin L := ![j0, j1, j2]
  have hn : ∀ n, (i n).val ≠ 0 ∨ (j n).val ≠ 0 := by
    intro n
    fin_cases n <;> assumption
  let x : Fin 3 → LaurentSeries k := ![
    algebraMap (PowerSeries k) (LaurentSeries k) (tateX L 1 1),
    algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k L 1),
    algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k L 0)]
  let y : Fin 3 → LaurentSeries k := ![
    algebraMap (PowerSeries k) (LaurentSeries k) (tateY L 1 1),
    algebraMap (PowerSeries k) (LaurentSeries k) (tateY L (L/2) 1),
    algebraMap (PowerSeries k) (LaurentSeries k) (tateY L 0 (-1))]
  have hxy : ∀ n, HasCoordinates (LaurentSeries k) (TateCurve k L)
      (coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking (i n) (j n))
      (x n) (y n) := by
    intro n
    fin_cases n
    · exact h0
    · simpa [x, y, i, j, rootSeries] using h1
    · simpa [x, y, i, j, rootSeries] using h2
  let z := fun n => markedX k L D (i n) (j n) (hn n)
  refine ⟨z 0 - z 1, z 1 - z 2, ?_⟩
  rw [map_sub, map_sub]
  exact (classified_coordinate_ratio k L D E b hb i j hn x y hxy).trans
    (parameterCandidate_laurent k L hL heven).symm

end FinalAssembly

#print axioms completedMap_exists
#print axioms localMap_residue_surjective
#print axioms isCompletedParameter_of_uniformizer
#print axioms isCompletedParameter_iff_uniformizer
#print axioms isCompletedParameter_of_order_one
#print axioms parameterCandidate_order
#print axioms isCompletedParameter_of_candidate_fraction
#print axioms chartX_invariant
#print axioms marked_coordinate_descends
#print axioms marked_x_function
#print axioms coordinate_ratio_of_pointed_iso
#print axioms combination_transport
#print axioms markedX_presentation
#print axioms classified_coordinate_ratio
#print axioms localMap_injective
#print axioms open_ratio_fraction
#print axioms isCompletedParameter_of_open_ratio
#print axioms full_level_generates
#print axioms literal_torsion_point
#print axioms candidate_open_ratio

end CompletedLocalParameter

/-- Every actual full-level Tate disk induces the prescribed completed local
parameter isomorphism, over its original characteristic-zero coefficient field. -/
theorem tate_completed_local_parameter :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L),
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : TateLevel k L)
      (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D)
      (b : Quiver.Hom (Puncture k)
        (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)),
      ClassifiesTate k L D E b → ∀ (d : Quiver.Hom (Disk k) X.space),
      Extends k L D X b d → IsCompletedParameter k L D X d := by
  intro k _ _ L hL heven D E X b hb d hd
  obtain ⟨r, s, hrs⟩ := CompletedLocalParameter.candidate_open_ratio k L hL heven D E b hb
  exact CompletedLocalParameter.isCompletedParameter_of_open_ratio k L D X b d hd r s
    (CompletedLocalParameter.parameterCandidate k L)
    (CompletedLocalParameter.parameterCandidate_order k L hL heven) hrs

#print axioms tate_completed_local_parameter
end ArithmeticThetaTateCuspsR0181
