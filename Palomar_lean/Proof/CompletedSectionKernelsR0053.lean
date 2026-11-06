module

public import AnnularTorsionPrerequisiteDefinitionsR0053
public import ScaledCompletedNodeNormalDomainR0051
public import ScaledThetaFiniteSpecializationR0050
public import ScaledTateCompletionTargetIdealSeparated
public import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

open ArithmeticThetaScaledAnnularR0050
open ArithmeticThetaScaledTateCompletionExtensionR0048

variable (k : Type u) [Field k]

private lemma section_surjective (side : Bool) (α : k)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    Function.Surjective σ := by
  intro f
  refine ⟨base k f, ?_⟩
  exact DFunLike.congr_fun hσ.1 f

private lemma section_ideal_le_kernel (side : Bool) (α : k)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    sectionIdeal k side α ≤ RingHom.ker σ := by
  apply Ideal.span_le.mpr
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  change σ (sectionEquation k side α) = 0
  simp only [sectionEquation, map_sub]
  rw [hσ.2.1, show σ (base k (PowerSeries.C α)) = PowerSeries.C α from
    DFunLike.congr_fun hσ.1 (PowerSeries.C α)]
  exact sub_self _

private lemma section_kernel_prime (σ : Chart k →+* Base k) :
    (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ

variable [CharZero k]

private lemma section_node_agreement (side : Bool) (α : k)
    (σ ψ : Chart k →+* Base k)
    (hσ : SectionAt k side α σ) (hψ : SectionAt k side α ψ) :
    σ.comp (complete k) = ψ.comp (complete k) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hp : (σ.comp (complete k)).comp
        (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1) =
      (ψ.comp (complete k)).comp
        (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1) := by
    apply MvPolynomial.ringHom_ext
    · intro f
      change σ (base k f) = ψ (base k f)
      exact (DFunLike.congr_fun hσ.1 f).trans
        (DFunLike.congr_fun hψ.1 f).symm
    · intro i
      fin_cases i
      · change σ (cx k) = ψ (cx k)
        cases side with
        | false => simpa [coord] using hσ.2.2.1.trans hψ.2.2.1.symm
        | true => exact hσ.2.1.trans hψ.2.1.symm
      · change σ (cy k) = ψ (cy k)
        cases side with
        | false => exact hσ.2.1.trans hψ.2.1.symm
        | true => exact hσ.2.2.1.trans hψ.2.2.1.symm
  exact DFunLike.congr_fun hp p

private lemma section_unique (side : Bool) (α : k)
    (σ ψ : Chart k →+* Base k)
    (hσ : SectionAt k side α σ) (hψ : SectionAt k side α ψ) :
    σ = ψ := by
  have hnode := section_node_agreement k side α σ ψ hσ hψ
  obtain ⟨_, _, _, _, _, _, happrox⟩ :=
    ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)
  apply RingHom.ext
  intro z
  apply sub_eq_zero.mp
  apply target_ideal_separated k
  intro n
  obtain ⟨p, hp⟩ := happrox n z
  let q := ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 p
  have heq : σ (complete k q) = ψ (complete k q) :=
    DFunLike.congr_fun hnode q
  have hd : σ (z - complete k q) - ψ (z - complete k q) ∈
      (Ideal.span {PowerSeries.X} : Ideal (Base k)) ^ n :=
    ((Ideal.span {PowerSeries.X} : Ideal (Base k)) ^ n).sub_mem
      (hσ.2.2.2 n _ hp) (hψ.2.2.2 n _ hp)
  simpa only [targetIdeal, map_sub, heq, sub_sub_sub_cancel_right] using hd

private lemma section_equation_regular (side : Bool) (α : k)
    (h : sectionEquation k side α ≠ 0) :
    sectionEquation k side α ∈ nonZeroDivisors (Chart k) := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  exact mem_nonZeroDivisors_of_ne_zero h

private def yNodeMap (α : k) (hα : α ≠ 0) : Node k →+* Base k := by
  let f : ArithmeticThetaScaledTateBridgeR0046.PolynomialChart k →+* Base k :=
    MvPolynomial.eval₂Hom (baseMap k)
      (fun i : Fin 2 => if i = 0 then PowerSeries.C α⁻¹ * PowerSeries.X
        else PowerSeries.C α)
  apply Ideal.Quotient.lift
    (ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1) f
  intro p hp
  have hrel : f (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 := by
    dsimp [f]
    unfold ArithmeticThetaScaledTateBridgeR0046.relation
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul]
    simp only [MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, baseMap, RingHom.id_apply,
      if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0),
      ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one]
    change (PowerSeries.C α⁻¹ * PowerSeries.X) * PowerSeries.C α -
      PowerSeries.X = 0
    have hu : PowerSeries.C α⁻¹ * PowerSeries.C α = (1 : Base k) := by
      rw [← map_mul, inv_mul_cancel₀ hα, map_one]
    calc
      (PowerSeries.C α⁻¹ * PowerSeries.X) * PowerSeries.C α -
          PowerSeries.X =
          (PowerSeries.C α⁻¹ * PowerSeries.C α) * PowerSeries.X -
            PowerSeries.X := by ring
      _ = 0 := by rw [hu]; ring
  exact (Ideal.span_le.mpr (by
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact hrel) : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 ≤
      RingHom.ker f) hp

private lemma yNodeMap_base (α : k) (hα : α ≠ 0) (b : Base k) :
    yNodeMap k α hα (nodeBase k b) = b := by
  change yNodeMap k α hα
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.C b)) = b
  simp [yNodeMap, ArithmeticThetaScaledTateBridgeR0046.quotientMap, baseMap]

private lemma yNodeMap_x (α : k) (hα : α ≠ 0) :
    yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
      PowerSeries.C α⁻¹ * PowerSeries.X := by
  simp [yNodeMap, ArithmeticThetaScaledTateBridgeR0046.x,
    ArithmeticThetaScaledTateBridgeR0046.quotientMap, baseMap]

private lemma yNodeMap_y (α : k) (hα : α ≠ 0) :
    yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
      PowerSeries.C α := by
  simp [yNodeMap, ArithmeticThetaScaledTateBridgeR0046.y,
    ArithmeticThetaScaledTateBridgeR0046.quotientMap, baseMap]

private lemma quotient_C (a : Base k) :
    ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.C a) =
      nodeBase k a := rfl

private lemma node_xy :
    ArithmeticThetaScaledTateBridgeR0046.x k 1 *
      ArithmeticThetaScaledTateBridgeR0046.y k 1 = nodeBase k PowerSeries.X := by
  have h : ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  simpa only [ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.x,
    ArithmeticThetaScaledTateBridgeR0046.y,
    ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one,
    quotient_C, map_sub, map_mul, sub_eq_zero] using h

private lemma node_coord_other_mod (side : Bool) (α : k) (hα : α ≠ 0) :
    nodeCoord k (!side) - nodeBase k (PowerSeries.C α⁻¹ * PowerSeries.X) ∈
      Ideal.span {nodeCoord k side - nodeBase k (PowerSeries.C α)} := by
  let X := ArithmeticThetaScaledTateBridgeR0046.x k 1
  let Y := ArithmeticThetaScaledTateBridgeR0046.y k 1
  let A := nodeBase k (PowerSeries.C α)
  let Ainv := nodeBase k (PowerSeries.C α⁻¹)
  have hunit : A * Ainv = 1 := by
    dsimp [A, Ainv]
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hα, map_one, map_one]
  have hxy : X * Y = nodeBase k PowerSeries.X := node_xy k
  cases side with
  | false =>
      change X - nodeBase k (PowerSeries.C α⁻¹ * PowerSeries.X) ∈
        Ideal.span {Y - A}
      have heq : X - nodeBase k (PowerSeries.C α⁻¹ * PowerSeries.X) =
          -(Ainv * X) * (Y - A) := by
        rw [map_mul, ← hxy]
        calc
          X - Ainv * (X * Y) = X * (A * Ainv) - Ainv * (X * Y) := by rw [hunit]; ring
          _ = -(Ainv * X) * (Y - A) := by ring
      rw [heq]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  | true =>
      change Y - nodeBase k (PowerSeries.C α⁻¹ * PowerSeries.X) ∈
        Ideal.span {X - A}
      have heq : Y - nodeBase k (PowerSeries.C α⁻¹ * PowerSeries.X) =
          -(Ainv * Y) * (X - A) := by
        rw [map_mul, ← hxy]
        calc
          Y - Ainv * (X * Y) = Y * (A * Ainv) - Ainv * (X * Y) := by rw [hunit]; ring
          _ = -(Ainv * Y) * (X - A) := by ring
      rw [heq]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private lemma section_node_kernel (side : Bool) (α : k) (hα : α ≠ 0)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    RingHom.ker (σ.comp (complete k)) =
      Ideal.span {nodeCoord k side - nodeBase k (PowerSeries.C α)} := by
  let J : Ideal (Node k) :=
    Ideal.span {nodeCoord k side - nodeBase k (PowerSeries.C α)}
  let q : Node k →+* Node k ⧸ J := Ideal.Quotient.mk J
  let f : Node k →+* Base k := σ.comp (complete k)
  have hbase (b : Base k) : f (nodeBase k b) = b := by
    exact DFunLike.congr_fun hσ.1 b
  have hcoord : f (nodeCoord k side) = PowerSeries.C α := by
    cases side <;> simpa [f, complete, nodeCoord, coord, cx, cy,
      ArithmeticThetaScaledAnnularR0050.cx, ArithmeticThetaScaledAnnularR0050.cy] using hσ.2.1
  have hother : f (nodeCoord k (!side)) =
      PowerSeries.C α⁻¹ * PowerSeries.X := by
    cases side <;> simpa [f, complete, nodeCoord, coord, cx, cy,
      ArithmeticThetaScaledAnnularR0050.cx, ArithmeticThetaScaledAnnularR0050.cy] using hσ.2.2.1
  have hq : q = (q.comp (nodeBase k)).comp f := by
    apply RingHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hp : q.comp (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1) =
        ((q.comp (nodeBase k)).comp f).comp
          (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1) := by
      apply MvPolynomial.ringHom_ext
      · intro b
        change q (nodeBase k b) = q (nodeBase k (f (nodeBase k b)))
        rw [hbase]
      · intro i
        fin_cases i
        · cases side with
          | false =>
              change q (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
                q (nodeBase k (f (ArithmeticThetaScaledTateBridgeR0046.x k 1)))
              rw [show f (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
                PowerSeries.C α⁻¹ * PowerSeries.X from hother]
              exact (Ideal.Quotient.eq.mpr
                (by simpa [J, nodeCoord, nodeBase, map_mul] using
                  node_coord_other_mod k false α hα))
          | true =>
              change q (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
                q (nodeBase k (f (ArithmeticThetaScaledTateBridgeR0046.x k 1)))
              rw [show f (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
                PowerSeries.C α from hcoord]
              exact (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _))
        · cases side with
          | false =>
              change q (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
                q (nodeBase k (f (ArithmeticThetaScaledTateBridgeR0046.y k 1)))
              rw [show f (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
                PowerSeries.C α from hcoord]
              exact (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _))
          | true =>
              change q (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
                q (nodeBase k (f (ArithmeticThetaScaledTateBridgeR0046.y k 1)))
              rw [show f (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
                PowerSeries.C α⁻¹ * PowerSeries.X from hother]
              exact (Ideal.Quotient.eq.mpr
                (by simpa [J, nodeCoord, nodeBase, map_mul] using
                  node_coord_other_mod k true α hα))
    exact DFunLike.congr_fun hp p
  apply le_antisymm
  · intro z hz
    have hz0 : f z = 0 := hz
    have hqz := DFunLike.congr_fun hq z
    rw [show ((q.comp (nodeBase k)).comp f) z = q (nodeBase k (f z)) by rfl,
      hz0, map_zero, map_zero] at hqz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hqz
  · apply Ideal.span_le.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change f (nodeCoord k side - nodeBase k (PowerSeries.C α)) = 0
    rw [map_sub, hcoord, hbase, sub_self]

private lemma yNodeMap_continuous (α : k) (hα : α ≠ 0) :
    ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1 ≤
      Ideal.comap (yNodeMap k α hα) (targetIdeal k) := by
  change Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1} ≤
    Ideal.comap (yNodeMap k α hα) (targetIdeal k)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.t k 1) ∈
    targetIdeal k
  have ht : ArithmeticThetaScaledTateBridgeR0046.t k 1 =
      nodeBase k PowerSeries.X := by
    simp [ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter, nodeBase]
  rw [ht, yNodeMap_base]
  exact Ideal.mem_span_singleton_self _

private def yNodeMapMod (α : k) (hα : α ≠ 0) (n : ℕ) :
    Node k ⧸ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) ^ n →+*
      Base k ⧸ (targetIdeal k) ^ n := by
  let g := yNodeMap k α hα
  let q : Node k →+* Base k ⧸ (targetIdeal k) ^ n :=
    (Ideal.Quotient.mk ((targetIdeal k) ^ n)).comp g
  have hpow : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) ^ n ≤
      Ideal.comap g ((targetIdeal k) ^ n) :=
    (pow_le_pow_left' (yNodeMap_continuous k α hα) n).trans
      (Ideal.le_comap_pow g n)
  exact Ideal.Quotient.lift _ q (by
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact hpow hz)

private def yCompFamily (α : k) (hα : α ≠ 0) (n : ℕ) :
    Chart k →+* Base k ⧸ (targetIdeal k) ^ n :=
  (yNodeMapMod k α hα n).comp
    (AdicCompletion.evalₐ
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) n).toRingHom

private lemma yCompFamily_compatible (α : k) (hα : α ≠ 0)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (targetIdeal k) hmn).comp
      (yCompFamily k α hα n) = yCompFamily k α hα m := by
  let I := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1
  let J := targetIdeal k
  have hmod :
      (Ideal.Quotient.factorPow J hmn).comp (yNodeMapMod k α hα n) =
        (yNodeMapMod k α hα m).comp (Ideal.Quotient.factorPow I hmn) := by
    apply RingHom.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [yNodeMapMod, I, J, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk]
  have heval (z : Chart k) :
      Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
        AdicCompletion.evalₐ I m z := by
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I (Node k) z
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    have hs := s.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
    rw [← neg_sub]
    exact neg_mem hs
  apply RingHom.ext
  intro z
  calc
    ((Ideal.Quotient.factorPow J hmn).comp (yCompFamily k α hα n)) z =
        ((Ideal.Quotient.factorPow J hmn).comp (yNodeMapMod k α hα n))
          (AdicCompletion.evalₐ I n z) := rfl
    _ = yNodeMapMod k α hα m
          (Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z)) :=
        congrArg (fun f => f (AdicCompletion.evalₐ I n z)) hmod
    _ = (yCompFamily k α hα m) z := by rw [heval]; rfl

private lemma ySection_exists_and_filtered (α : k) (hα : α ≠ 0) :
    ∃ φ : Chart k →+* Base k,
      φ.comp (complete k) = yNodeMap k α hα ∧
      ∀ (n : ℕ) (z : Chart k), z ∈ filtration k n →
        φ z ∈ (targetIdeal k) ^ n := by
  let J : Ideal (Base k) := targetIdeal k
  letI : IsAdicComplete J (Base k) := by
    change IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries k)
    infer_instance
  let fam : (n : ℕ) → Chart k →+* Base k ⧸ J ^ n :=
    fun n => yCompFamily k α hα n
  have hfam : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (fam n) = fam m := by
    intro m n hmn
    exact yCompFamily_compatible k α hα hmn
  let φ : Chart k →+* Base k := IsAdicComplete.liftRingHom J fam hfam
  have hagree : φ.comp (complete k) = yNodeMap k α hα := by
    apply RingHom.ext
    intro z
    apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk (J ^ n) (φ (complete k z)) =
      Ideal.Quotient.mk (J ^ n) (yNodeMap k α hα z)
    rw [show φ (complete k z) =
        IsAdicComplete.liftRingHom J fam hfam (complete k z) by rfl]
    rw [IsAdicComplete.mk_liftRingHom]
    change (yNodeMapMod k α hα n)
        (AdicCompletion.evalₐ
          (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) n
          (complete k z)) = _
    simp [yNodeMapMod, complete,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted, J]
  refine ⟨φ, hagree, ?_⟩
  intro n z hz
  have hgen : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 ∈
      Ideal.comap φ (J ^ 1) := by
    change φ (complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1)) ∈ J ^ 1
    rw [show φ (complete k (ArithmeticThetaScaledTateBridgeR0046.t k 1)) =
        yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.t k 1) by
      exact DFunLike.congr_fun hagree _]
    have ht : ArithmeticThetaScaledTateBridgeR0046.t k 1 =
        nodeBase k PowerSeries.X := by
      simp [ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter, nodeBase]
    rw [ht, yNodeMap_base]
    change PowerSeries.X ∈ (Ideal.span {PowerSeries.X} : Ideal (Base k)) ^ 1
    rw [pow_one]
    exact Ideal.mem_span_singleton_self _
  have hpow : filtration k n ≤ Ideal.comap φ ((J ^ 1) ^ n) := by
    rw [show filtration k n =
        (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1}) ^ n
      by rfl]
    exact (pow_le_pow_left'
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 hgen)) n).trans
      (Ideal.le_comap_pow φ n)
  have hz' : φ z ∈ (J ^ 1) ^ n := hpow hz
  simpa [J] using hz'

private def ySection (α : k) (hα : α ≠ 0) : Chart k →+* Base k :=
  Classical.choose (ySection_exists_and_filtered k α hα)

private lemma ySection_spec (α : k) (hα : α ≠ 0) :
    SectionAt k false α (ySection k α hα) := by
  have hφ := Classical.choose_spec (ySection_exists_and_filtered k α hα)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro f
    change ySection k α hα (complete k (nodeBase k f)) = f
    rw [show ySection k α hα (complete k (nodeBase k f)) =
      yNodeMap k α hα (nodeBase k f) from DFunLike.congr_fun hφ.1 _]
    exact yNodeMap_base k α hα f
  · change ySection k α hα
        (complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) =
      PowerSeries.C α
    rw [show ySection k α hα
      (complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) =
      yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.y k 1) from
        DFunLike.congr_fun hφ.1 _]
    exact yNodeMap_y k α hα
  · change ySection k α hα
        (complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) =
      PowerSeries.C α⁻¹ * PowerSeries.X
    rw [show ySection k α hα
      (complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) =
      yNodeMap k α hα (ArithmeticThetaScaledTateBridgeR0046.x k 1) from
        DFunLike.congr_fun hφ.1 _]
    exact yNodeMap_x k α hα
  · intro n f hf
    exact hφ.2 n f hf

private def xSection (α : k) (hα : α ≠ 0) : Chart k →+* Base k :=
  specialization k 1 0 (by omega) (by omega) α hα

private lemma xSection_spec (α : k) (hα : α ≠ 0) :
    SectionAt k true α (xSection k α hα) := by
  have hc := specialization_coordinates k 1 0 (by omega) (by omega) α hα
  have hf := (Classical.choose_spec
    (completion_specialization_exists_and_filtered k 1 0
      (by omega) (by omega) α hα)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro f
    exact specialization_base k 1 0 (by omega) (by omega) α hα f
  · simpa only [xSection, coord, if_pos, pow_zero, mul_one, cx] using hc.2.1
  · simpa [xSection, coord, cy] using hc.2.2
  · intro n f hf'
    simpa [xSection, specialization, filtration, targetIdeal] using hf n f hf'

private lemma section_equation_ne_zero (side : Bool) (α : k) (hα : α ≠ 0) :
    sectionEquation k side α ≠ 0 := by
  have htwo : (2 : k) ≠ 0 := by norm_num
  have hβ : (2 * α : k) ≠ 0 := mul_ne_zero htwo hα
  let σ : Chart k →+* Base k := if side then xSection k (2 * α) hβ
    else ySection k (2 * α) hβ
  have hσ : SectionAt k side (2 * α) σ := by
    cases side with
    | false => exact ySection_spec k _ _
    | true => exact xSection_spec k _ _
  intro heq
  have heval := congrArg σ heq
  have hC : PowerSeries.C (2 * α) = PowerSeries.C α := by
    have hc : σ (coord k side) = PowerSeries.C (2 * α) := hσ.2.1
    have hb : σ (base k (PowerSeries.C α)) = PowerSeries.C α :=
      DFunLike.congr_fun hσ.1 _
    simpa [sectionEquation, map_sub, hc, hb, sub_eq_zero] using heval
  have hscalar : (2 * α : k) = α := (PowerSeries.C_injective hC)
  exact hα (by linear_combination hscalar)

private lemma section_kernel (side : Bool) (α : k) (hα : α ≠ 0)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    RingHom.ker σ = sectionIdeal k side α := by
  let I : Ideal (Chart k) := filtration k 1
  let J : Ideal (Chart k) := sectionIdeal k side α
  have hIeq : I = (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (complete k) := by
    simp [I, filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span,
      Set.image_singleton, complete,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter]
  haveI : IsAdicComplete I (Chart k) := by
    rw [hIeq]
    exact AdicCompletion.isAdicComplete_self _ (Submodule.fg_span_singleton _)
  have hIjac : I ≤ (⊥ : Ideal (Chart k)).jacobson :=
    IsAdicComplete.le_jacobson_bot I
  letI : IsNoetherianRing (Chart k) :=
    (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1
  have hsep : (⨅ n : ℕ, I ^ n •
      (⊤ : Submodule (Chart k) (Chart k ⧸ J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hIjac
  have hBX : base k PowerSeries.X =
      ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 := by
    simp [base, ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter]
  have hbaseI : targetIdeal k ≤ Ideal.comap (base k) I := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    change base k PowerSeries.X ∈ I
    rw [hBX]
    simp only [I, filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      pow_one]
    exact Ideal.mem_span_singleton_self _
  have hJmap : (Ideal.span {nodeCoord k side - nodeBase k (PowerSeries.C α)}).map
      (complete k) = J := by
    cases side <;> simp [J, sectionIdeal, sectionEquation, nodeCoord, coord,
      complete, base, cx, cy, ArithmeticThetaScaledAnnularR0050.cx,
      ArithmeticThetaScaledAnnularR0050.cy, nodeBase,
      Ideal.map_span, Set.image_singleton] <;> rfl
  apply le_antisymm
  · intro z hz
    have hz0 : σ z = 0 := hz
    obtain ⟨_, _, _, _, _, _, happrox⟩ :=
      ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)
    have hquot (n : ℕ) : (Ideal.Quotient.mk J z) ∈
        I ^ n • (⊤ : Submodule (Chart k) (Chart k ⧸ J)) := by
      obtain ⟨p, hp⟩ := happrox n z
      let q := ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 p
      let b := σ (complete k q)
      have hpI : z - complete k q ∈ I ^ n := by
        simpa only [I, filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
          pow_one, q, complete] using hp
      have hb : b ∈ (targetIdeal k) ^ n := by
        have hs := hσ.2.2.2 n (z - complete k q) hp
        rw [map_sub, hz0, zero_sub] at hs
        exact neg_mem_iff.mp hs
      have hbI : base k b ∈ I ^ n :=
        ((pow_le_pow_left' hbaseI n).trans (Ideal.le_comap_pow (base k) n)) hb
      have hnode : q - nodeBase k b ∈
          Ideal.span {nodeCoord k side - nodeBase k (PowerSeries.C α)} := by
        rw [← section_node_kernel k side α hα σ hσ]
        change σ (complete k (q - nodeBase k b)) = 0
        simp only [map_sub]
        change σ (complete k q) - σ (base k b) = 0
        rw [show σ (base k b) = b from DFunLike.congr_fun hσ.1 b]
        exact sub_self _
      have hsection : complete k q - base k b ∈ J := by
        rw [← hJmap]
        exact Ideal.mem_map_of_mem (complete k) hnode
      have hdiff : z - (complete k q - base k b) ∈ I ^ n := by
        convert (I ^ n).add_mem hpI hbI using 1 <;> ring
      have hqeq : Ideal.Quotient.mk J z =
          Ideal.Quotient.mk J (z - (complete k q - base k b)) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hsection, sub_zero]
      rw [hqeq, Ideal.smul_top_eq_map]
      exact Ideal.mem_map_of_mem _ hdiff
    have hzinf : Ideal.Quotient.mk J z ∈
        (⨅ n : ℕ, I ^ n • (⊤ : Submodule (Chart k) (Chart k ⧸ J))) := by
      rw [Submodule.mem_iInf]
      exact hquot
    rw [hsep] at hzinf
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzinf
  · exact section_ideal_le_kernel k side α σ hσ

theorem completed_section_kernels :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (α : k), α ≠ 0 →
      (∃! σ : Chart k →+* Base k, SectionAt k side α σ) ∧
      (∀ σ : Chart k →+* Base k, SectionAt k side α σ →
        Function.Surjective σ ∧ RingHom.ker σ = sectionIdeal k side α ∧
        (sectionIdeal k side α).IsPrime ∧
        sectionEquation k side α ∈ nonZeroDivisors (Chart k)) := by
  intro k _ _ side α hα
  constructor
  · cases side with
    | false =>
        refine ⟨ySection k α hα, ySection_spec k α hα, ?_⟩
        intro σ hσ
        exact section_unique k false α σ (ySection k α hα) hσ
          (ySection_spec k α hα)
    | true =>
        refine ⟨xSection k α hα, xSection_spec k α hα, ?_⟩
        intro σ hσ
        exact section_unique k true α σ (xSection k α hα) hσ
          (xSection_spec k α hα)
  · intro σ hσ
    have hker := section_kernel k side α hα σ hσ
    exact ⟨section_surjective k side α σ hσ, hker,
      hker ▸ section_kernel_prime k σ,
      section_equation_regular k side α (section_equation_ne_zero k side α hα)⟩

end ArithmeticThetaAnnularTorsionPrereqR0053
