module

public import GenericRestrictionProvidersR0065
public import GenericAdjacentProvidersR0065

@[expose] public section
set_option synthInstance.maxHeartbeats 200000
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Literal powered products on interior generic overlaps. Coordinate support
is reproduced from the accepted ordinary-gamma overlap proof; the integer
powers, bounded denominators, and localized limit argument are new. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
universe u
namespace ArithmeticThetaGenericOverlapR0065
namespace PoweredSupport
open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaCorrectedGammaR0061 (restrict overlap)
variable (k : Type u) [Field k] [CharZero k]

private theorem restriction_spec (j : ℕ) (side : Bool) :
    IsRestriction k j side (restrict k j side) :=
  (Classical.choose_spec (completed_coordinate_restrictions k j side).exists)

private theorem overlap_spec (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    IsCompletedAdjacent k r j (overlap k r j hr hj) :=
  (Classical.choose_spec (completed_indexed_adjacent k r j hr hj).exists)

omit [CharZero k] in
private theorem node_equiv_coord (i : Fin 2) :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.X i)) = ArithmeticThetaNodeCharts.quotientMap k
        (MvPolynomial.X i) := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private theorem restrict_tau (j : ℕ) (side : Bool) :
    restrict k j side (tau k) = completeOpen k j side (ot k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, ot, openBase,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase] using h

private theorem restrict_cx (j : ℕ) (side : Bool) :
    restrict k j side (cx k) = completeOpen k j side (ox k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)
  simpa [cx, ArithmeticThetaScaledAnnularR0050.cx,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, openMap,
    ArithmeticThetaScaledTateBridgeR0046.x, ArithmeticThetaNodeCharts.x,
    node_equiv_coord, ox] using h

private theorem restrict_cy (j : ℕ) (side : Bool) :
    restrict k j side (cy k) = completeOpen k j side (oy k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)
  simpa [cy, ArithmeticThetaScaledAnnularR0050.cy,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, openMap,
    ArithmeticThetaScaledTateBridgeR0046.y, ArithmeticThetaNodeCharts.y,
    node_equiv_coord, oy] using h

omit [CharZero k] in
private theorem open_xy (j : ℕ) :
    ox k j true * oy k j true = ot k j true := by
  have hnode : ArithmeticThetaNodeCharts.x k * ArithmeticThetaNodeCharts.y k =
      ArithmeticThetaNodeCharts.t k := by
    apply sub_eq_zero.mp
    change ArithmeticThetaNodeCharts.quotientMap k
      (ArithmeticThetaNodeCharts.relation k) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h := congrArg (algebraMap (ArithmeticThetaNodeCharts.Node k)
    (Open k j true)) hnode
  have ht : nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X) =
        ArithmeticThetaNodeCharts.t k := by
    have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
        ArithmeticThetaNodeCharts.relationIdeal k := by
      simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
        ArithmeticThetaScaledTateBridgeR0046.relation,
        ArithmeticThetaScaledTateBridgeR0046.parameter,
        ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
        ArithmeticThetaNodeCharts.parameter]
    unfold nodeEquiv ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase
      ArithmeticThetaNodeCharts.t
    change (Ideal.quotientEquivAlgOfEq _ hrel)
      (Ideal.Quotient.mk _ (MvPolynomial.C PowerSeries.X)) =
        Ideal.Quotient.mk _ (MvPolynomial.C PowerSeries.X)
    rw [Ideal.quotientEquivAlgOfEq_mk]
  change ox k j true * oy k j true =
    algebraMap (Node k j) _ (nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X))
  rw [ht]
  exact (map_mul _ _ _).symm.trans h

private theorem transported_coordinates (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    let F := (overlap k r j hr hj).toRingHom.comp (restrict k j false)
    let G := restrict k (next r j) true
    F (tau k) = G (tau k) ∧
      F (cx k) = G (tau k) * G (cx k) ∧
      G (tau k) * F (cy k) = G (cy k) := by
  dsimp
  have hcomm (a : Open k j false) :=
    RingHom.congr_fun (overlap_spec k r j hr hj).1 a
  have ht := DFunLike.congr_fun (indexed_adjacent_coordinates k r j hr hj).1
    PowerSeries.X
  change adjacent k r j (ot k j false) = ot k (next r j) true at ht
  have hx := (indexed_adjacent_coordinates k r j hr hj).2.2.1
  have hy := (indexed_adjacent_coordinates k r j hr hj).2.1
  have hu : (ArithmeticThetaIndexedOverlapsR0058.xUnit k (next r j) :
      Open k (next r j) true) = ox k (next r j) true := IsUnit.unit_spec _
  have hty : ot k (next r j) true *
      adjacent k r j (oy k j false) = oy k (next r j) true := by
    rw [hy, ← open_xy k (next r j), ← hu]
    simp [mul_assoc, mul_comm]
  simp only [restrict_tau, restrict_cx, restrict_cy]
  refine ⟨?_, ?_, ?_⟩
  · have h := hcomm (ot k j false)
    change overlap k r j hr hj (completeOpen k j false (ot k j false)) =
      completeOpen k (next r j) true (adjacent k r j (ot k j false)) at h
    rwa [ht] at h
  · have h := hcomm (ox k j false)
    change overlap k r j hr hj (completeOpen k j false (ox k j false)) =
      completeOpen k (next r j) true (adjacent k r j (ox k j false)) at h
    rwa [hx, map_mul] at h
  · rw [show overlap k r j hr hj (completeOpen k j false (oy k j false)) =
        completeOpen k (next r j) true (adjacent k r j (oy k j false)) from
          hcomm (oy k j false)]
    rw [← map_mul, hty]


private theorem include_injective (j : ℕ) :
    Function.Injective (includeOpen k j true) := by
  letI : IsDomain (ArithmeticThetaIndexedOverlapsR0058.Open k j true) :=
    (torusEquiv k j true).toMulEquiv.isDomain _
  letI : IsNoetherianRing (ArithmeticThetaNodeCharts.Node k) :=
    (ArithmeticThetaNodeCharts.node_noetherian_finite_type k).1
  letI : IsNoetherianRing (ArithmeticThetaIndexedOverlapsR0058.Open k j true) :=
    inferInstance
  have ht : ot k j true ≠ 0 := by
    have he := (Classical.choose_spec
      (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1).1
    have h := congrArg (fun f => f (MvPolynomial.C (PowerSeries.X : PowerSeries k))) he
    have hh : torusEquiv k j true (ot k j true) = LaurentPolynomial.C PowerSeries.X := by
      change (Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1)
        ((ArithmeticThetaNodeCharts.toXChart k)
          (ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.C PowerSeries.X))) = _
      simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using h
    intro hz
    rw [hz, map_zero] at hh
    have hn := congrArg (fun f : LaurentPolynomial (PowerSeries k) => f.coeff 0) hh
    exact (show (PowerSeries.X : PowerSeries k) ≠ 0 from PowerSeries.X_ne_zero)
      (by simpa using hn.symm)
  have hreg : Function.Injective (fun a : OpenHat k j true => openParameter k j true * a) := by
    simpa only [Algebra.smul_def, openParameter, completeOpen] using
      (smul_right_injective (M := OpenHat k j true) ht)
  apply IsLocalization.injective (M := Submonoid.powers (openParameter k j true))
    (GenericOpen k j true)
  apply Submonoid.powers_le.mpr
  apply mem_nonZeroDivisors_iff.mpr
  constructor <;> intro a ha <;> apply hreg <;> simpa [mul_comm] using ha

private theorem hat_separated (j : ℕ) (a : OpenHat k j true)
    (ha : ∀ n, a ∈ hatPower k j true n) : a = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro n
  have hker : hatPower k j true n =
      RingHom.ker (AdicCompletion.evalₐ (openIdeal k j true) n).toRingHom := by
    rw [ArithmeticThetaNodeCharts.completion_eval_kernel
      (openIdeal k j true) (Submodule.fg_span_singleton _) n]
    unfold hatPower openIdeal
    congr 1
    rw [Ideal.map_span]
    simp [completeOpen]
    rfl
  have h := ha n
  rw [hker] at h
  simpa using h

/-- The image of the completed lattice is separated even in the t-localization.
This does not assert that the ideal (t) in the generic ring is proper. -/
private theorem image_separated (j : ℕ) (z : GenericOpen k j true)
    (hz : ∀ n, ∃ a : OpenHat k j true, a ∈ hatPower k j true n ∧
      z = includeOpen k j true a) : z = 0 := by
  obtain ⟨a, _, ha⟩ := hz 0
  have hzero : a = 0 := by
    apply hat_separated k j
    intro n
    obtain ⟨b, hb, heq⟩ := hz n
    have hab := include_injective k j (ha.symm.trans heq)
    exact hab ▸ hb
  simpa [hzero] using ha

/-- Two fixed generic coefficients have one common denominator. -/
private theorem common_denominator (j : ℕ) (a b : GenericOpen k j true) :
    ∃ (d : ℕ) (A B : OpenHat k j true),
      openT k j true ^ d * a = includeOpen k j true A ∧
      openT k j true ^ d * b = includeOpen k j true B := by
  obtain ⟨A, B, s, ha, hb⟩ :=
    IsLocalization.surj₂ (Submonoid.powers (openParameter k j true))
      (GenericOpen k j true) a b
  obtain ⟨d, hd⟩ := s.property
  refine ⟨d, A, B, ?_, ?_⟩
  · simpa only [← hd, map_pow, mul_comm, openT, includeOpen] using ha
  · simpa only [← hd, map_pow, mul_comm, openT, includeOpen] using hb

/-- Equality of limits with bounded clearing denominators, proved in the
completed lattice and then transported back to its localization. -/
private theorem bounded_limit_unique (j : ℕ) (a b C D : GenericOpen k j true)
    (h : ∀ n, ∃ f g : OpenHat k j true,
      f ∈ hatPower k j true n ∧ g ∈ hatPower k j true n ∧
      a - b = C * includeOpen k j true f - D * includeOpen k j true g) : a = b := by
  obtain ⟨d, A, B, hA, hB⟩ := common_denominator k j C D
  have hz : openT k j true ^ d * (a - b) = 0 := by
    apply image_separated k j
    intro n
    obtain ⟨f, g, hf, hg, heq⟩ := h n
    refine ⟨A * f - B * g,
      (hatPower k j true n).sub_mem
        ((hatPower k j true n).mul_mem_left A hf)
        ((hatPower k j true n).mul_mem_left B hg), ?_⟩
    rw [heq, mul_sub, ← mul_assoc, hA, ← mul_assoc, hB]
    simp only [map_sub, map_mul]
  have hu : IsUnit (openT k j true ^ d) :=
    (IsLocalization.Away.algebraMap_isUnit (openParameter k j true)).pow d
  exact sub_eq_zero.mp (hu.mul_left_cancel (by simpa using hz))

private theorem tp_nat (n : ℕ) :
    tpower k (n : ℤ) = toGeneric k (tau k) ^ n := by
  simp only [tpower, zpow_natCast, Units.val_pow_eq_pow_val]
  congr 1

private theorem tp_add (a b : ℤ) :
    tpower k (a + b) = tpower k a * tpower k b := by
  simp [tpower, zpow_add]

private theorem generic_coordinates (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (RX : GenericChart k →+* GenericOpen k (next r j) true)
    (RY : GenericChart k →+* GenericOpen k j false)
    (E : GenericOpen k j false ≃+* GenericOpen k (next r j) true)
    (hX : IsGenericRestriction k (next r j) true RX)
    (hY : IsGenericRestriction k j false RY)
    (hE : IsGenericAdjacent k r j hr hj E) :
    let F := E.toRingHom.comp RY
    F (toGeneric k (tau k)) = RX (toGeneric k (tau k)) ∧
    F (toGeneric k (cx k)) = RX (toGeneric k (tau k)) * RX (toGeneric k (cx k)) ∧
    RX (toGeneric k (tau k)) * F (toGeneric k (cy k)) = RX (toGeneric k (cy k)) := by
  let ι := includeOpen k (next r j) true
  have hF (a : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :
      E (RY (toGeneric k a)) = ι (overlap k r j hr hj (restrict k j false a)) := by
    rw [show RY (toGeneric k a) = includeOpen k j false (restrict k j false a) from
      RingHom.congr_fun hY a]
    exact RingHom.congr_fun hE _
  have hG (a : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :
      RX (toGeneric k a) = ι (restrict k (next r j) true a) := RingHom.congr_fun hX a
  obtain ⟨ht, hx, hy⟩ := transported_coordinates k r j hr hj
  dsimp at ht hx hy ⊢
  simp only [hF, hG]
  exact ⟨congrArg ι ht, (congrArg ι hx).trans (map_mul ι _ _),
    (map_mul ι _ _).symm.trans (congrArg ι hy)⟩

private theorem literal_overlap (r c j : ℕ) (hr : 0 < r) (hj : j < r)
    (hi : j + 1 < r)
    (RX : GenericChart k →+* GenericOpen k (next r j) true)
    (RY : GenericChart k →+* GenericOpen k j false)
    (E : GenericOpen k j false ≃+* GenericOpen k (next r j) true)
    (hX : IsGenericRestriction k (next r j) true RX)
    (hY : IsGenericRestriction k j false RY)
    (hE : IsGenericAdjacent k r j hr hj E) (N : ℕ) :
    E (RY (literalPartial k r c j N)) = RX (literalPartial k r c (next r j) N) := by
  let F := E.toRingHom.comp RY
  obtain ⟨ht, hx, hy⟩ := generic_coordinates k r j hr hj RX RY E hX hY hE
  change F (toGeneric k (tau k)) = RX (toGeneric k (tau k)) at ht
  change F (toGeneric k (cx k)) = RX (toGeneric k (tau k)) * RX (toGeneric k (cx k)) at hx
  change RX (toGeneric k (tau k)) * F (toGeneric k (cy k)) = RX (toGeneric k (cy k)) at hy
  have hp (e : ℤ) : F (tpower k e) = RX (tpower k e) := by
    have hu : Units.map F.toMonoidHom (parameterUnit k) =
        Units.map RX.toMonoidHom (parameterUnit k) := by
      apply Units.ext
      change F (↑(parameterUnit k)) = RX (↑(parameterUnit k))
      rw [show (↑(parameterUnit k) : GenericChart k) = toGeneric k (tau k) from
        IsUnit.unit_spec _]
      exact ht
    change ↑(Units.map F.toMonoidHom (parameterUnit k ^ e)) =
      (↑(Units.map RX.toMonoidHom (parameterUnit k ^ e)) : GenericOpen k (next r j) true)
    rw [map_zpow, map_zpow, hu]
  have hn : next r j = j + 1 := Nat.mod_eq_of_lt hi
  have hleft (l : ℕ) :
      F (tpower k (leftExponent r c j l : ℤ) * toGeneric k (cx k) ^ c) =
      RX (tpower k (leftExponent r c (next r j) l : ℤ) * toGeneric k (cx k) ^ c) := by
    have he : leftExponent r c (next r j) l = leftExponent r c j l + c := by
      simp only [leftExponent, hn]; ring
    simp only [map_mul, map_pow, hx, tp_nat, ht, he, pow_add, mul_pow]
    ring
  have hright (l : ℕ) :
      F (tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c) =
      RX (tpower k (rightExponent r c (next r j) l) * toGeneric k (cy k) ^ c) := by
    have he : rightExponent r c j l = rightExponent r c (next r j) l + (c : ℤ) := by
      simp only [rightExponent, hn, Nat.cast_add, Nat.cast_one]; ring
    rw [map_mul, he, tp_add, map_mul, hp, tp_nat, map_pow, ht, map_pow]
    rw [mul_assoc, ← mul_pow, hy, ← map_pow, ← map_mul]
  change F (literalPartial k r c j N) = RX (literalPartial k r c (next r j) N)
  simp only [literalPartial, map_prod]
  apply Finset.prod_congr rfl
  intro l _
  simp only [map_mul, map_sub, map_one] at hleft hright ⊢
  rw [hleft, hright]

end PoweredSupport

open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaCorrectedGammaR0061 (restrict overlap)
open PoweredSupport

/-- The accepted powered limits agree on every interior overlap for the
specified generic restriction maps and adjacent equivalence. -/
theorem powered_interior_overlap :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hr : 0 < 2*c) (hj : j < 2*c) (hn :
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) < 2*c), j + 1 < 2*c → ∀ (RX :
    ArithmeticThetaGenericOverlapR0065.GenericChart k →+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c)
    j) true) (RY : ArithmeticThetaGenericOverlapR0065.GenericChart k →+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k j false) (E :
    ArithmeticThetaGenericOverlapR0065.GenericOpen k j false ≃+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c)
    j) true), ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true RX →
    ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k j false RY →
    ArithmeticThetaGenericOverlapR0065.IsGenericAdjacent k (2*c) j hr hj E →  E (RY
    (ArithmeticThetaGenericOverlapR0065.powered k c j ζ hc hcop hζ hj)) = RX
    (ArithmeticThetaGenericOverlapR0065.powered k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c)
    j) ζ hc hcop hζ hn) := by
  intro k _ _ c j ζ hc hcop hζ hr hj hn hi RX RY E hX hY hE
  let C := clearingPartial k (2*c) c j (cutoff c j 0)
  let D := clearingPartial k (2*c) c (next (2*c) j) (cutoff c (next (2*c) j) 0)
  apply bounded_limit_unique k (next (2*c) j)
    (E (RY (powered k c j ζ hc hcop hζ hj)))
    (RX (powered k c (next (2*c) j) ζ hc hcop hζ hn)) (E (RY C)) (RX D)
  intro n
  let N := max (cutoff c j n) (cutoff c (next (2*c) j) n)
  have hjN : cutoff c j n ≤ N := Nat.le_max_left _ _
  have hnN : cutoff c (next (2*c) j) n ≤ N := Nat.le_max_right _ _
  have happrox (i : ℕ) (hi' : i < 2*c) :
      ∀ n N : ℕ, cutoff c i n ≤ N → ∃ f : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k,
        f ∈ filtration k n ∧ powered k c i ζ hc hcop hζ hi' - literalPartial k (2*c) c i N =
          clearingPartial k (2*c) c i N * toGeneric k f :=
    (Classical.choose_spec (powered_gamma_local_divisor k (2*c) c i ζ hr hc
      (by simp) hcop hζ hi')).1.1
  obtain ⟨f, hf, heqf⟩ := happrox j hj n N hjN
  obtain ⟨g, hg, heqg⟩ := happrox (next (2*c) j) hn n N hnN
  have hjC : clearingPartial k (2*c) c j N = C := by
    apply (powered_gamma_clearing k (2*c) c j hr hc (by simp) hcop hj).2.2
    · dsimp [cutoff] at hjN ⊢; omega
    · exact le_refl _
  have hnD : clearingPartial k (2*c) c (next (2*c) j) N = D := by
    apply (powered_gamma_clearing k (2*c) c (next (2*c) j) hr hc
      (by simp) hcop hn).2.2
    · dsimp [cutoff] at hnN ⊢; omega
    · exact le_refl _
  rw [hjC] at heqf
  rw [hnD] at heqg
  let f' := overlap k (2*c) j hr hj (restrict k j false f)
  let g' := restrict k (next (2*c) j) true g
  refine ⟨f', g', ?_, ?_, ?_⟩
  · exact (overlap_spec k (2*c) j hr hj).2.1 n _
      ((restriction_spec k j false).2 n f hf)
  · exact (restriction_spec k (next (2*c) j) true).2 n g hg
  · have hff : E (RY (toGeneric k f)) = includeOpen k (next (2*c) j) true f' := by
      rw [show RY (toGeneric k f) = includeOpen k j false (restrict k j false f) from
        RingHom.congr_fun hY f]
      exact RingHom.congr_fun hE _
    have hgg : RX (toGeneric k g) = includeOpen k (next (2*c) j) true g' :=
      RingHom.congr_fun hX g
    have hfa := congrArg (fun a => E (RY a)) heqf
    have hga := congrArg RX heqg
    simp only [map_sub, map_mul] at hfa hga
    rw [hff, literal_overlap k (2*c) c j hr hj hi RX RY E hX hY hE N] at hfa
    rw [hgg] at hga
    linear_combination hfa - hga

end ArithmeticThetaGenericOverlapR0065
