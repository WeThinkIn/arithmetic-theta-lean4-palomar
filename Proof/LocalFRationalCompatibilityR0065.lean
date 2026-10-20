module

public import GenericOpenFaithfulnessR0065
public import LocalGammaProviderBridgeR0065
public import PoweredInteriorOverlapR0065
public import PoweredPeriodBoundaryR0065

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Rational compatibility of the literal local Tate norm expressions. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
universe u
namespace ArithmeticThetaGenericOverlapR0065
namespace RationalSupport
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


private theorem tp_nat (n : ℕ) :
    tpower k (n : ℤ) = toGeneric k (tau k) ^ n := by
  simp only [tpower, zpow_natCast, Units.val_pow_eq_pow_val]
  congr 1

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


private theorem denominator_regular (c j : ℕ) (ζ : k)
    (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
    (hj : j < 2*c) (side : Bool)
    (R : GenericChart k →+* GenericOpen k j side)
    (hR : IsGenericRestriction k j side R) :
    R (denominator k c j ζ hc hcop hζ hj) ∈ nonZeroDivisors (GenericOpen k j side) := by
  letI := (generic_open_faithfulness k j side).1
  have hi := (generic_open_faithfulness k j side).2
  letI : IsDomain (ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  have hcoord (s : Bool) : horizontalEquation k s c ≠ 0 := by
    have h := (horizontal_split_reduced k s c ζ hc hcop hζ).2.2.2.1
    exact nonZeroDivisors.ne_zero h
  have hh : ArithmeticThetaAnnularTorsionPrereqR0053.horizontal k (2*c) c j ≠ 0 := by
    unfold ArithmeticThetaAnnularTorsionPrereqR0053.horizontal
    exact mul_ne_zero (by split_ifs <;> simp_all) (by split_ifs <;> simp_all)
  have hmap : R (toGeneric k (ArithmeticThetaAnnularTorsionPrereqR0053.horizontal k (2*c) c j)) ≠ 0 := by
    intro hz
    apply hh
    apply hi
    change includeOpen k j side (restrict k j side _) = _
    have he : R (toGeneric k (ArithmeticThetaAnnularTorsionPrereqR0053.horizontal k (2*c) c j)) =
        includeOpen k j side (restrict k j side _) := RingHom.congr_fun hR _
    simpa only [map_zero] using he.symm.trans hz
  have hass := (ArithmeticThetaLocalNormR0054.local_norm_factorization
    k c j ζ hc hcop hζ hj).2.map R
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (hass.ne_zero_iff.mpr hmap)


private theorem gamma_spec (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ArithmeticThetaCorrectedGammaR0061.IsGammaData k r j
      (Classical.choose (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))
      (correctedGamma k r j hr hj) :=
  Classical.choose_spec (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))

variable {k} {r j : ℕ} {hr : 0 < r} {hj : j < r}
    {RX : GenericChart k →+* GenericOpen k (next r j) true}
    {RY : GenericChart k →+* GenericOpen k j false}
    {E : GenericOpen k j false ≃+* GenericOpen k (next r j) true}

private theorem map_completed
    (hY : IsGenericRestriction k j false RY)
    (hE : IsGenericAdjacent k r j hr hj E) (a : Chart k) :
    E (RY (toGeneric k a)) = includeOpen k (next r j) true
      (overlap k r j hr hj (restrict k j false a)) := by
  rw [show RY (toGeneric k a) = includeOpen k j false (restrict k j false a) from
    RingHom.congr_fun hY a]
  exact RingHom.congr_fun hE _

private theorem gamma_interior (hn : next r j < r) (hi : j+1 < r)
    (hX : IsGenericRestriction k (next r j) true RX)
    (hY : IsGenericRestriction k j false RY)
    (hE : IsGenericAdjacent k r j hr hj E) :
    E (RY (ArithmeticThetaLocalNormR0054.gammaLocal k r j hr hj)) =
      RX (ArithmeticThetaLocalNormR0054.gammaLocal k r (next r j) hr hn) := by
  rw [local_gamma_provider_bridge k r j hr hj,
    local_gamma_provider_bridge k r (next r j) hr hn, map_completed hY hE,
    show RX (toGeneric k (correctedGamma k r (next r j) hr hn)) =
      includeOpen k (next r j) true (restrict k (next r j) true _) from RingHom.congr_fun hX _]
  exact congrArg (includeOpen k (next r j) true)
    (ArithmeticThetaCorrectedGammaR0061.gamma_interior_overlap k r j hr hj hi
      _ _ _ _ (gamma_spec k r j hr hj) (gamma_spec k r (next r j) hr hn))

private theorem gamma_boundary (hn : next r j < r) (hb : j+1 = r)
    (hX : IsGenericRestriction k (next r j) true RX)
    (hY : IsGenericRestriction k j false RY)
    (hE : IsGenericAdjacent k r j hr hj E) :
    E (RY (ArithmeticThetaLocalNormR0054.gammaLocal k r j hr hj)) *
      openX k (next r j) true =
      -RX (ArithmeticThetaLocalNormR0054.gammaLocal k r (next r j) hr hn) := by
  rw [local_gamma_provider_bridge k r j hr hj,
    local_gamma_provider_bridge k r (next r j) hr hn, map_completed hY hE,
    show RX (toGeneric k (correctedGamma k r (next r j) hr hn)) =
      includeOpen k (next r j) true (restrict k (next r j) true _) from RingHom.congr_fun hX _]
  rw [ArithmeticThetaCorrectedGammaR0061.gamma_period_boundary k r j hr hj hb
    _ _ _ _ (gamma_spec k r j hr hj) (gamma_spec k r (next r j) hr hn)]
  let U := ArithmeticThetaIndexedOverlapsR0058.xUnit k (next r j)
  have hu : (U : Open k (next r j) true) = ox k (next r j) true := IsUnit.unit_spec _
  have hmul : includeOpen k (next r j) true
      (completeOpen k (next r j) true (↑U⁻¹)) * openX k (next r j) true = 1 := by
    simp only [openX, ← map_mul, ← hu]
    simp
  change includeOpen k (next r j) true
    (-completeOpen k (next r j) true (↑U⁻¹) * _) * _ = _
  simp only [map_mul, map_neg]
  calc
    _ = -(includeOpen k (next r j) true
      (completeOpen k (next r j) true (↑U⁻¹)) * openX k (next r j) true) *
      includeOpen k (next r j) true (restrict k (next r j) true _) := by ring
    _ = _ := by rw [hmul]; ring


private theorem boundary_algebra {A : Type*} [CommRing A]
    (t x g g' p p' s : A) (a m h r : ℕ) (hx : IsUnit x)
    (hg : g*x = -g') (hp : p*x^m*t^(r*h) = s*p')
    (hs : (-1 : A)^m = s) :
    (t^a*g^m) * ((-x)^h*p') = (t^a*g'^m) * ((-(t^r*x))^h*p) := by
  have hN : (t^a*g^m)*x^m = s*(t^a*g'^m) := by
    calc
      _ = t^a*(g*x)^m := by rw [mul_pow]; ring
      _ = t^a*((-1)^m*g'^m) := by rw [hg, neg_pow]
      _ = _ := by rw [hs]; ring
  have hD : ((-(t^r*x))^h*p)*x^m = s*((-x)^h*p') := by
    calc
      _ = (-x)^h*(p*x^m*t^(r*h)) := by
        rw [show -(t^r*x) = t^r*(-x) by ring, mul_pow, pow_mul]; ring
      _ = _ := by rw [hp]; ring
  apply (hx.pow m).mul_right_cancel
  calc
    _ = ((t^a*g^m)*x^m)*((-x)^h*p') := by ring
    _ = (t^a*g'^m)*(s*((-x)^h*p')) := by rw [hN]; ring
    _ = _ := by rw [← hD]; ring

end RationalSupport


open RationalSupport
open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaLocalNormR0054 (gammaLocal localZ)

/-- Literal local fractions agree on every adjacent generic overlap, with
regular denominators and the specified geometric localization maps. -/
theorem local_f_rational_compatibility :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hr : 0 < 2*c) (hj : j < 2*c) (hn :
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) < 2*c), ∃ (RX :
    ArithmeticThetaGenericOverlapR0065.GenericChart k →+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c)
    j) true) (RY : ArithmeticThetaGenericOverlapR0065.GenericChart k →+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k j false) (E :
    ArithmeticThetaGenericOverlapR0065.GenericOpen k j false ≃+*
    ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c)
    j) true), ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true RX ∧
    ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k j false RY ∧
    ArithmeticThetaGenericOverlapR0065.IsGenericAdjacent k (2*c) j hr hj E ∧ RX
    (ArithmeticThetaGenericOverlapR0065.denominator k c (ArithmeticThetaIndexedOverlapsR0058.next
    (2*c) j) ζ hc hcop hζ hn) ∈ nonZeroDivisors (ArithmeticThetaGenericOverlapR0065.GenericOpen k
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true) ∧ E (RY
    (ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj)) ∈ nonZeroDivisors
    (ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next
    (2*c) j) true) ∧ E (RY (ArithmeticThetaGenericOverlapR0065.numerator k c j ζ hc hcop hζ hj)) *
    RX (ArithmeticThetaGenericOverlapR0065.denominator k c (ArithmeticThetaIndexedOverlapsR0058.next
    (2*c) j) ζ hc hcop hζ hn) = RX (ArithmeticThetaGenericOverlapR0065.numerator k c
    (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) ζ hc hcop hζ hn) * E (RY
    (ArithmeticThetaGenericOverlapR0065.denominator k c j ζ hc hcop hζ hj)) := by
  intro k _ _ c j ζ hc hcop hζ hr hj hn
  obtain ⟨RX, hX, _⟩ := generic_restriction_providers k (next (2*c) j) true
  obtain ⟨RY, hY, _⟩ := generic_restriction_providers k j false
  obtain ⟨E, hE, _⟩ := generic_adjacent_providers k (2*c) j hr hj
  refine ⟨RX, RY, E, hX, hY, hE, denominator_regular k c _ ζ hc hcop hζ hn true RX hX, ?_, ?_⟩
  · letI := (generic_open_faithfulness k j false).1
    letI := (generic_open_faithfulness k (next (2*c) j) true).1
    have h := denominator_regular k c j ζ hc hcop hζ hj false RY hY
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp h) (E.injective (hz.trans E.map_zero.symm)))
  let F := E.toRingHom.comp RY
  let T := RX (toGeneric k (tau k))
  let X := RX (toGeneric k (cx k))
  have hRX (a : Chart k) : RX (toGeneric k a) =
      includeOpen k (next (2*c) j) true (ArithmeticThetaCorrectedGammaR0061.restrict k (next (2*c) j) true a) :=
    RingHom.congr_fun hX a
  have hT : T = openT k (next (2*c) j) true := by
    rw [show T = RX (toGeneric k (tau k)) from rfl, hRX, restriction_parameter]
    rfl
  have hXX : X = openX k (next (2*c) j) true := by
    rw [show X = RX (toGeneric k (cx k)) from rfl, hRX, restrict_cx]
    rfl
  obtain ⟨ht, hx, _⟩ := generic_coordinates k (2*c) j hr hj RX RY E hX hY hE
  change F (toGeneric k (tau k)) = T at ht
  change F (toGeneric k (cx k)) = T*X at hx
  have hZ : F (localZ k j) = T^(j+1)*X := by
    simp only [localZ, chartCoordinate, map_mul, map_pow, ht, hx, pow_succ]
    ring
  have hZ' : RX (localZ k (next (2*c) j)) = T^(next (2*c) j)*X := by
    simp only [localZ, chartCoordinate, map_mul, map_pow]; rfl
  have hnormF (n : ℕ) : F (tpower k (n : ℤ)) = T^n := by rw [tp_nat, map_pow, ht]
  have hnormX (n : ℕ) : RX (tpower k (n : ℤ)) = T^n := by rw [tp_nat, map_pow]
  change F (numerator k c j ζ hc hcop hζ hj) * RX (denominator k c _ ζ hc hcop hζ hn) =
    RX (numerator k c _ ζ hc hcop hζ hn) * F (denominator k c j ζ hc hcop hζ hj)
  by_cases hi : j+1 < 2*c
  · have hg := gamma_interior hn hi hX hY hE
    have hp := powered_interior_overlap k c j ζ hc hcop hζ hr hj hn hi RX RY E hX hY hE
    change F (gammaLocal k (2*c) j hr hj) = RX (gammaLocal k (2*c) _ hr hn) at hg
    change F (powered k c j ζ hc hcop hζ hj) = RX (powered k c _ ζ hc hcop hζ hn) at hp
    have hnxt : next (2*c) j = j+1 := Nat.mod_eq_of_lt hi
    have hz : F (localZ k j) = RX (localZ k (next (2*c) j)) := by rw [hZ, hZ', hnxt]
    have hnum : F (numerator k c j ζ hc hcop hζ hj) = RX (numerator k c _ ζ hc hcop hζ hn) := by
      simp only [numerator, ArithmeticThetaLocalNormR0054.localNumerator, map_mul, map_pow,
        hnormF, hnormX, hg]
    have hden : F (denominator k c j ζ hc hcop hζ hj) = RX (denominator k c _ ζ hc hcop hζ hn) := by
      change F ((-localZ k j)^ (c*(c-1)/2) * powered k c j ζ hc hcop hζ hj) =
        RX ((-localZ k (next (2*c) j))^ (c*(c-1)/2) * powered k c _ ζ hc hcop hζ hn)
      simp only [map_mul, map_pow, map_neg, hz, hp]
    rw [hnum, hden]
  · have hb : j+1 = 2*c := by omega
    have hnxt : next (2*c) j = 0 := by simp [next, hb]
    have hg := gamma_boundary hn hb hX hY hE
    have hp := powered_period_boundary k c j ζ hc hcop hζ hr hj hn hb RX RY E hX hY hE
    rw [← hXX] at hg hp
    rw [← hT] at hp
    have hunit : IsUnit X := by
      rw [hXX]
      have hu : (ArithmeticThetaIndexedOverlapsR0058.xUnit k (next (2*c) j) :
          Open k (next (2*c) j) true) = ox k (next (2*c) j) true := IsUnit.unit_spec _
      simpa only [hu, openX] using (((ArithmeticThetaIndexedOverlapsR0058.xUnit k (next (2*c) j)).isUnit.map
        (completeOpen k (next (2*c) j) true)).map (includeOpen k (next (2*c) j) true))
    have hsign : (-1 : GenericOpen k (next (2*c) j) true)^(c^2) = (-1)^c := by
      apply neg_one_pow_congr
      simp [Nat.even_pow]
    have halg := boundary_algebra T X
      (F (gammaLocal k (2*c) j hr hj)) (RX (gammaLocal k (2*c) _ hr hn))
      (F (powered k c j ζ hc hcop hζ hj)) (RX (powered k c _ ζ hc hcop hζ hn))
      ((-1 : GenericOpen k (next (2*c) j) true)^c)
      ((2*c*(c^2-1))/12) (c^2) (c*(c-1)/2) (2*c) hunit hg hp hsign
    have hz0 : RX (localZ k (next (2*c) j)) = X := by
      calc
        _ = T^(next (2*c) j)*X := hZ'
        _ = T^0*X := congrArg (fun n : ℕ => T^n*X) hnxt
        _ = X := by simp
    simpa only [numerator, denominator, ArithmeticThetaLocalNormR0054.localNumerator,
      ArithmeticThetaLocalNormR0054.localDenominator, powered, map_mul, map_pow,
      map_neg, hnormF, hnormX, hZ, hz0, hb] using halg

end ArithmeticThetaGenericOverlapR0065
