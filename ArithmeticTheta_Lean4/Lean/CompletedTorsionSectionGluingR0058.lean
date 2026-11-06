import CompletedCoordinateRestrictionsR0058
import CompletedIndexedAdjacentR0058

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaIndexedOverlapsR0058

open ArithmeticThetaAnnularTorsionPrereqR0053

variable (k : Type u) [Field k] [CharZero k]

private abbrev nodeSource := ArithmeticThetaAnnularTorsionPrereqR0053.Node k

private def baseIdeal : Ideal (Base k) := Ideal.span {PowerSeries.X}

private instance base_complete : IsAdicComplete (baseIdeal k) (Base k) := by
  change IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries k)
  infer_instance

private lemma node_equiv_x : nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
    ArithmeticThetaNodeCharts.x k := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  change (Ideal.quotientEquivAlgOfEq (Base k) hrel)
      (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
    Ideal.Quotient.mk _ (MvPolynomial.X 0)
  rw [Ideal.quotientEquivAlgOfEq_mk]

private lemma node_equiv_y : nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
    ArithmeticThetaNodeCharts.y k := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  change (Ideal.quotientEquivAlgOfEq (Base k) hrel)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1)) =
    Ideal.Quotient.mk _ (MvPolynomial.X 1)
  rw [Ideal.quotientEquivAlgOfEq_mk]

private def nodeSection (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    Node k j →+* Base k :=
  (selectedSection k side α hα).comp
    ((ArithmeticThetaAnnularTorsionPrereqR0053.complete k).comp
      (nodeEquiv k).symm.toRingHom)

private lemma nodeSection_comp (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    (nodeSection k j side α hα).comp (nodeEquiv k).toRingHom =
      (selectedSection k side α hα).comp
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
  apply RingHom.ext
  intro z
  simp [nodeSection]

private lemma selected_section_spec (side : Bool) (α : k) (hα : α ≠ 0) :
    SectionAt k side α (selectedSection k side α hα) := by
  exact (Classical.choose_spec
    (completed_section_kernels k side α hα).1).1

private lemma nodeSection_coord (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    nodeSection k j side α hα (nodeCoord k side) =
      PowerSeries.C α := by
  cases side with
  | false =>
      change (selectedSection k false α hα)
        (complete k ((nodeEquiv k).symm (ArithmeticThetaNodeCharts.y k))) = _
      rw [show (nodeEquiv k).symm (ArithmeticThetaNodeCharts.y k) =
          ArithmeticThetaScaledTateBridgeR0046.y k 1 by
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_y]]
      simpa [ArithmeticThetaAnnularTorsionPrereqR0053.complete,
        ArithmeticThetaAnnularTorsionPrereqR0053.coord,
        ArithmeticThetaAnnularTorsionPrereqR0053.cx,
        ArithmeticThetaAnnularTorsionPrereqR0053.cy,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaScaledAnnularR0050.cy] using
        (selected_section_spec k false α hα).2.1
  | true =>
      change (selectedSection k true α hα)
        (complete k ((nodeEquiv k).symm (ArithmeticThetaNodeCharts.x k))) = _
      rw [show (nodeEquiv k).symm (ArithmeticThetaNodeCharts.x k) =
          ArithmeticThetaScaledTateBridgeR0046.x k 1 by
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_x]]
      simpa [ArithmeticThetaAnnularTorsionPrereqR0053.complete,
        ArithmeticThetaAnnularTorsionPrereqR0053.coord,
        ArithmeticThetaAnnularTorsionPrereqR0053.cx,
        ArithmeticThetaAnnularTorsionPrereqR0053.cy,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaScaledAnnularR0050.cy] using
        (selected_section_spec k true α hα).2.1

private def localizedSection (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    Open k j side →+* Base k := by
  let f := nodeSection k j side α hα
  have hv : IsUnit (f (nodeCoord k side)) := by
    cases side with
    | false =>
        rw [nodeSection_coord]
        exact RingHom.isUnit_map (PowerSeries.C : k →+* PowerSeries k)
          (isUnit_iff_ne_zero.mpr hα)
    | true =>
        rw [nodeSection_coord]
        exact RingHom.isUnit_map (PowerSeries.C : k →+* PowerSeries k)
          (isUnit_iff_ne_zero.mpr hα)
  exact IsLocalization.Away.lift
    (R := Node k j) (S := Open k j side) (P := Base k)
    (g := f) (nodeCoord k side) hv

private lemma localizedSection_on_node (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0)
    (z : Node k j) :
    localizedSection k j side α hα (algebraMap _ _ z) =
      nodeSection k j side α hα z := by
  exact IsLocalization.Away.lift_eq
    (R := Node k j) (S := Open k j side) (P := Base k)
    (g := nodeSection k j side α hα) (nodeCoord k side)
    (by
      cases side <;> rw [nodeSection_coord]
      · exact RingHom.isUnit_map (PowerSeries.C : k →+* PowerSeries k)
          (isUnit_iff_ne_zero.mpr hα)
      · exact RingHom.isUnit_map (PowerSeries.C : k →+* PowerSeries k)
          (isUnit_iff_ne_zero.mpr hα)) z

private lemma localizedSection_parameter (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    localizedSection k j side α hα (ot k j side) = PowerSeries.X := by
  rw [show ot k j side = openBase k j side PowerSeries.X by rfl]
  change localizedSection k j side α hα
      (algebraMap (Node k j) _ (nodeEquiv k
        (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X))) = _
  rw [localizedSection_on_node]
  change nodeSection k j side α hα (nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
  rw [nodeSection]
  exact DFunLike.congr_fun (selected_section_spec k side α hα).1 PowerSeries.X

private def stage {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)
    (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f
    ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow _ n))).comp
    (AdicCompletion.evalₐ I n).toRingHom

private lemma stage_compat {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (stage I J f h n) =
      stage I J f h m := by
  apply RingHom.ext
  intro z
  have hc : (Ideal.Quotient.factorPow J hmn).comp
      (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow _ n))) =
      (Ideal.quotientMap (J ^ m) f
        ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow _ m))).comp
        (Ideal.Quotient.factorPow I hmn) := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  have hh := RingHom.congr_fun hc (AdicCompletion.evalₐ I n z)
  simp only [RingHom.comp_apply] at hh
  rw [show Ideal.Quotient.factorPow I hmn
      (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z by
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    have ha := SModEq.sub_mem.mp (a.property hmn)
    simpa only [smul_eq_mul, Ideal.mul_top, neg_sub] using neg_mem ha] at hh
  exact hh

private def sectionLift (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0) :
    OpenHat k j side →+* Base k := by
  let I := openIdeal k j side
  let J := baseIdeal k
  let f := localizedSection k j side α hα
  have hIJ : I ≤ Ideal.comap f J := by
    rw [show I = Ideal.span {ot k j side} by rfl, Ideal.span_le]
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    change f (ot k j side) ∈ J
    rw [localizedSection_parameter k j side α hα]
    exact Ideal.mem_span_singleton_self _
  let fam : ∀ n : ℕ, OpenHat k j side →+* Base k ⧸ J ^ n :=
    fun n => stage I J f hIJ n
  have hfam : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (fam n) = fam m := by
    intro m n hmn
    simpa [fam] using (stage_compat I J f hIJ hmn)
  exact IsAdicComplete.liftRingHom J fam hfam

private lemma sectionLift_on_open (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0)
    (z : Open k j side) :
    sectionLift k j side α hα (completeOpen k j side z) =
      localizedSection k j side α hα z := by
  let I := openIdeal k j side
  let J := baseIdeal k
  let f := localizedSection k j side α hα
  have hIJ' : I ≤ Ideal.comap f J := by
    rw [show I = Ideal.span {ot k j side} by rfl, Ideal.span_le]
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    change f (ot k j side) ∈ J
    rw [localizedSection_parameter k j side α hα]
    exact Ideal.mem_span_singleton_self _
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk (J ^ n)
      (IsAdicComplete.liftRingHom J
        (fun n => stage I J f hIJ' n)
        (fun {m n} (hmn : m ≤ n) => stage_compat I J f hIJ' hmn)
        (completeOpen k j side z)) =
    Ideal.Quotient.mk (J ^ n) (f z)
  rw [IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono hIJ' n).trans (Ideal.le_comap_pow _ n))
      (AdicCompletion.evalₐ I n (completeOpen k j side z)) = _
  rw [show AdicCompletion.evalₐ I n (completeOpen k j side z) =
      Ideal.Quotient.mk (I ^ n) z by
        simp [I, completeOpen, AdicCompletion.evalₐ_of]]
  simp [Ideal.quotientMap_mk]

private lemma sectionLift_filtered (j : ℕ) (side : Bool) (α : k) (hα : α ≠ 0)
    (n : ℕ) (z : OpenHat k j side) (hz : z ∈ hatPower k j side n) :
    sectionLift k j side α hα z ∈ basePower k n := by
  let I := openIdeal k j side
  let J := baseIdeal k
  let f := localizedSection k j side α hα
  have hIJ : I ≤ Ideal.comap f J := by
    rw [show I = Ideal.span {ot k j side} by rfl, Ideal.span_le]
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    change f (ot k j side) ∈ J
    rw [localizedSection_parameter k j side α hα]
    exact Ideal.mem_span_singleton_self _
  have hker : AdicCompletion.evalₐ I n z = 0 := by
    have hI : I.FG := by
      unfold I openIdeal
      exact Submodule.fg_span_singleton _
    have hker' : RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
        (I.map (algebraMap (Open k j side) (OpenHat k j side))) ^ n := by
      ext w
      have hf : Function.Injective (Ideal.Quotient.factor
          (show I ^ n • (⊤ : Ideal (Open k j side)) ≤ I ^ n by simp)) := by
        have he : I ^ n • (⊤ : Ideal (Open k j side)) = I ^ n := by simp
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
          using Ideal.map_mk_eq_bot_of_le (le_of_eq he.symm)
      rw [← Ideal.map_pow]
      change AdicCompletion.evalₐ I n w = 0 ↔
        w ∈ (Ideal.map (algebraMap (Open k j side) (OpenHat k j side))
          (I ^ n)).restrictScalars (Open k j side)
      rw [← Ideal.smul_top_eq_map]
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
      rw [← AdicCompletion.factor_eval_eq_evalₐ I w (by simp)]
      exact map_eq_zero_iff _ hf
    change z ∈ RingHom.ker (AdicCompletion.evalₐ I n).toRingHom
    rw [hker']
    have hid :
        (Ideal.map (algebraMap (Open k j side) (OpenHat k j side)) I) ^ n =
          (Ideal.span {completeOpen k j side (ot k j side)}) ^ n := by
      unfold I openIdeal
      rw [Ideal.map_span]
      simp [completeOpen]
      rfl
    rw [hid]
    exact hz
  have hmk : Ideal.Quotient.mk (J ^ n) (sectionLift k j side α hα z) =
      stage I J f hIJ n z := by
    change Ideal.Quotient.mk (J ^ n)
      (IsAdicComplete.liftRingHom J (fun n => stage I J f hIJ n)
        (fun {m n} (hmn : m ≤ n) => stage_compat I J f hIJ hmn) z) = _
    rw [IsAdicComplete.mk_liftRingHom]
  change sectionLift k j side α hα z ∈ J ^ n
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hmk]
  simp [stage, hker]

theorem completed_section_gluing :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ) (α : k) (hα : α ≠ 0),
      0 < r → j < r →
      ∃ (RX : Chart k (next r j) →+* OpenHat k (next r j) true)
        (RY : Chart k j →+* OpenHat k j false)
        (E : OpenHat k j false ≃+* OpenHat k (next r j) true)
        (sX : OpenHat k (next r j) true →+* Base k)
        (sY : OpenHat k j false →+* Base k),
        CompatibleSections k r j α hα RX RY E sX sY := by
  intro k _ _ r j α hα hr hj
  obtain ⟨RX, hRX, _⟩ := completed_coordinate_restrictions k (next r j) true
  obtain ⟨RY, hRY, _⟩ := completed_coordinate_restrictions k j false
  obtain ⟨E, hE, _⟩ := completed_indexed_adjacent k r j hr hj
  let sX := sectionLift k (next r j) true α hα
  let sY := sX.comp E.toRingHom
  have hsXcont : IsContinuousSection k (next r j) true sX := by
    intro n z hz
    exact sectionLift_filtered k (next r j) true α hα n z hz
  have hsYcont : IsContinuousSection k j false sY := by
    intro n z hz
    exact hsXcont n (E z) (hE.2.1 n z hz)
  have hSX : SectionAt k true α (sX.comp RX) := by
    have heval (z : Node k (next r j)) :
        sX (RX (complete k ((nodeEquiv k).symm z))) =
          nodeSection k (next r j) true α hα z := by
      have hR := DFunLike.congr_fun hRX.1 ((nodeEquiv k).symm z)
      have hR' : RX (complete k ((nodeEquiv k).symm z)) =
          completeOpen k (next r j) true
            (openMap k (next r j) true ((nodeEquiv k).symm z)) := by
        simpa only [RingHom.comp_apply] using hR
      rw [hR']
      rw [show openMap k (next r j) true ((nodeEquiv k).symm z) =
          algebraMap (Node k (next r j)) _ z by simp [openMap]]
      rw [sectionLift_on_open, localizedSection_on_node]
    have hx : complete k ((nodeEquiv k).symm (nodeCoord k true)) =
        coord k true := by
      rw [show (nodeEquiv k).symm (nodeCoord k true) =
          ArithmeticThetaScaledTateBridgeR0046.x k 1 by
        change (nodeEquiv k).symm (ArithmeticThetaNodeCharts.x k) = _
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_x]]
      rfl
    have hy : complete k ((nodeEquiv k).symm (nodeCoord k false)) =
        coord k false := by
      change complete k ((nodeEquiv k).symm (ArithmeticThetaNodeCharts.y k)) = _
      rw [show (nodeEquiv k).symm (ArithmeticThetaNodeCharts.y k) =
          ArithmeticThetaScaledTateBridgeR0046.y k 1 by
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_y]]
      rfl
    have hopen : nodeSection k (next r j) true α hα (nodeCoord k false) =
        PowerSeries.C α⁻¹ * PowerSeries.X := by
      change (selectedSection k true α hα)
          (complete k ((nodeEquiv k).symm (nodeCoord k false))) = _
      rw [hy]
      simpa [coord] using (selected_section_spec k true α hα).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply RingHom.ext
      intro b
      have h := heval ((nodeEquiv k) ((nodeBase k) b))
      change sX (RX (base k b)) = b
      simpa [base, complete, nodeBase, nodeSection_comp,
        ArithmeticThetaScaledTateBridgeR0046.completedBaseMap] using h
        |>.trans (DFunLike.congr_fun (selected_section_spec k true α hα).1 b)
    · have h := heval (nodeCoord k true)
      rw [← hx]
      simpa [nodeSection_coord] using h
    · have h := heval (nodeCoord k false)
      change sX (RX (coord k false)) = _
      rw [← hy]
      simpa [hopen] using h
    · intro n f hf
      exact hsXcont n (RX f) (hRX.2 n f hf)
  have hSY : SectionAt k false α⁻¹ (sY.comp RY) := by
    have hαinv : α⁻¹ ≠ 0 := inv_ne_zero hα
    have hopen (q : Open k j false) :
        E.toRingHom (completeOpen k j false q) =
          completeOpen k (next r j) true ((adjacent k r j).toRingHom q) := by
      have h := DFunLike.congr_fun hE.1 q
      simpa only [RingHom.comp_apply] using h
    have heval_base (b : Base k) :
        sY (RY (base k b)) = b := by
      have hR := DFunLike.congr_fun hRY.1
        (nodeBase k b)
      have hR' : RY (base k b) =
          completeOpen k j false (openBase k j false b) := by
        simpa [base, openBase, complete, nodeBase,
          ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
          RingHom.comp_apply] using hR
      rw [hR', show sY = sX.comp E.toRingHom by rfl, RingHom.comp_apply,
        hopen, sectionLift_on_open]
      change localizedSection k (next r j) true α hα
        (adjacent k r j (openBase k j false b)) = _
      rw [show adjacent k r j (openBase k j false b) =
          openBase k (next r j) true b by
        exact DFunLike.congr_fun
          (indexed_adjacent_coordinates k r j hr hj).1 b]
      rw [show openBase k (next r j) true b =
          algebraMap (Node k (next r j)) _
            ((nodeEquiv k) (nodeBase k b)) by rfl]
      rw [localizedSection_on_node]
      exact DFunLike.congr_fun (selected_section_spec k true α hα).1 b
    have hx : complete k ((nodeEquiv k).symm (nodeCoord k true)) =
        coord k true := by
      rw [show (nodeEquiv k).symm (nodeCoord k true) =
          ArithmeticThetaScaledTateBridgeR0046.x k 1 by
        change (nodeEquiv k).symm (ArithmeticThetaNodeCharts.x k) = _
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_x]]
      rfl
    have hy : complete k ((nodeEquiv k).symm (nodeCoord k false)) =
        coord k false := by
      rw [show (nodeEquiv k).symm (nodeCoord k false) =
          ArithmeticThetaScaledTateBridgeR0046.y k 1 by
        change (nodeEquiv k).symm (ArithmeticThetaNodeCharts.y k) = _
        apply (nodeEquiv k).injective
        rw [RingEquiv.apply_symm_apply, node_equiv_y]]
      rfl
    have heval_y :
        sY (RY (coord k false)) =
          PowerSeries.C α⁻¹ := by
      have hR := DFunLike.congr_fun hRY.1
        ((nodeEquiv k).symm (nodeCoord k false))
      have hR' :
          RY (complete k ((nodeEquiv k).symm (nodeCoord k false))) =
            completeOpen k j false
              (openMap k j false ((nodeEquiv k).symm (nodeCoord k false))) := by
        simpa only [RingHom.comp_apply] using hR
      rw [hy] at hR'
      rw [show openMap k j false ((nodeEquiv k).symm (nodeCoord k false)) =
          oy k j false by simp [openMap, nodeCoord, oy]] at hR'
      rw [hR', show sY = sX.comp E.toRingHom by rfl, RingHom.comp_apply,
        hopen, sectionLift_on_open]
      change localizedSection k (next r j) true α hα
        (adjacent k r j (oy k j false)) = _
      rw [show adjacent k r j (oy k j false) =
          ↑((xUnit k (next r j))⁻¹) by
        exact (indexed_adjacent_coordinates k r j hr hj).2.1]
      have hu : localizedSection k (next r j) true α hα
          (↑((xUnit k (next r j))⁻¹) : Open k (next r j) true) *
            localizedSection k (next r j) true α hα
              (↑(xUnit k (next r j)) : Open k (next r j) true) = 1 := by
        rw [← map_mul]
        simp
      change localizedSection k (next r j) true α hα
          (↑((xUnit k (next r j))⁻¹) : Open k (next r j) true) = _
      have hxu : localizedSection k (next r j) true α hα
          (↑(xUnit k (next r j)) : Open k (next r j) true) =
          PowerSeries.C α := by
        rw [show (↑(xUnit k (next r j)) : Open k (next r j) true) =
            ox k (next r j) true by exact IsUnit.unit_spec _]
        change localizedSection k (next r j) true α hα
          (algebraMap (Node k (next r j)) _
            (ArithmeticThetaNodeCharts.x k)) = _
        rw [localizedSection_on_node]
        simpa [nodeCoord] using
          (nodeSection_coord k (next r j) true α hα)
      have hmul : localizedSection k (next r j) true α hα
          (↑((xUnit k (next r j))⁻¹) : Open k (next r j) true) *
            localizedSection k (next r j) true α hα
              (↑(xUnit k (next r j)) : Open k (next r j) true) = 1 := by
        exact hu
      rw [hxu] at hmul
      apply mul_right_cancel₀ (show (PowerSeries.C α : PowerSeries k) ≠ 0 by
        intro hzero
        apply hα
        apply PowerSeries.C_injective
        simpa using hzero)
      rw [hmul]
      simpa [← map_mul, hα]
    have heval_x :
        sY (RY (coord k true)) =
          PowerSeries.C α * PowerSeries.X := by
      have hR := DFunLike.congr_fun hRY.1
        ((nodeEquiv k).symm (nodeCoord k true))
      have hR' :
          RY (complete k ((nodeEquiv k).symm (nodeCoord k true))) =
            completeOpen k j false
              (openMap k j false ((nodeEquiv k).symm (nodeCoord k true))) := by
        simpa only [RingHom.comp_apply] using hR
      rw [hx] at hR'
      rw [show openMap k j false ((nodeEquiv k).symm (nodeCoord k true)) =
          ox k j false by simp [openMap, nodeCoord, ox]] at hR'
      rw [hR', show sY = sX.comp E.toRingHom by rfl, RingHom.comp_apply,
        hopen, sectionLift_on_open]
      change localizedSection k (next r j) true α hα
        (adjacent k r j (ox k j false)) = _
      rw [show adjacent k r j (ox k j false) =
          ot k (next r j) true * ox k (next r j) true by
        exact (indexed_adjacent_coordinates k r j hr hj).2.2.1]
      rw [map_mul, localizedSection_parameter]
      change PowerSeries.X * localizedSection k (next r j) true α hα
          (algebraMap (Node k (next r j)) _ (ArithmeticThetaNodeCharts.x k)) = _
      change PowerSeries.X * localizedSection k (next r j) true α hα
          (algebraMap (Node k (next r j)) _ (nodeCoord k true)) = _
      rw [localizedSection_on_node, nodeSection_coord] <;> simp [mul_comm]
    have hopenNode : nodeSection k j false α⁻¹ (inv_ne_zero hα) (nodeCoord k true) =
        PowerSeries.C α * PowerSeries.X := by
      change (selectedSection k false α⁻¹ hαinv)
          (complete k ((nodeEquiv k).symm (nodeCoord k true))) = _
      rw [hx]
      simpa [coord] using (selected_section_spec k false α⁻¹ hαinv).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply RingHom.ext
      intro b
      exact heval_base b
    · exact heval_y
    · simpa [RingHom.comp_apply, show (!false : Bool) = true by rfl, inv_inv] using heval_x
    · intro n f hf
      exact hsYcont n (RY f) (hRY.2 n f hf)
  have huniqX := ((completed_section_kernels k true α hα).1).unique
      hSX (selected_section_spec k true α hα)
  have huniqY := ((completed_section_kernels k false α⁻¹ (inv_ne_zero hα)).1).unique
      hSY (selected_section_spec k false α⁻¹ (inv_ne_zero hα))
  refine ⟨RX, RY, E, sX, sY, ?_⟩
  refine ⟨hRX, hRY, hE, hsXcont, hsYcont, huniqX, huniqY, ?_⟩
  rfl

theorem torsion_period_compatible_sections :
    ∀ (k : Type u) [Field k] [CharZero k] (r c : ℕ) (ζ : k),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 → IsPrimitiveRoot ζ c →
      ∀ a b : Fin c, ∃ hα : ζ ^ b.val ≠ 0,
        ∃ (RX : Chart k (next r ((r * a.val / c + r - 1) % r)) →+*
            OpenHat k (next r ((r * a.val / c + r - 1) % r)) true)
          (RY : Chart k ((r * a.val / c + r - 1) % r) →+*
            OpenHat k ((r * a.val / c + r - 1) % r) false)
          (E : OpenHat k ((r * a.val / c + r - 1) % r) false ≃+*
            OpenHat k (next r ((r * a.val / c + r - 1) % r)) true)
          (sX : OpenHat k (next r ((r * a.val / c + r - 1) % r)) true →+* Base k)
          (sY : OpenHat k ((r * a.val / c + r - 1) % r) false →+* Base k),
          CompatibleSections k r ((r * a.val / c + r - 1) % r)
              (ζ ^ b.val) hα RX RY E sX sY ∧
            next r ((r * a.val / c + r - 1) % r) = r * a.val / c ∧
            sX (completeOpen k (next r ((r * a.val / c + r - 1) % r)) true
              (oz k (next r ((r * a.val / c + r - 1) % r)) true)) =
              ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar k r c a.val b.val ζ ∧
            sY (completeOpen k ((r * a.val / c + r - 1) % r) false
              (oz k ((r * a.val / c + r - 1) % r) false)) =
              (if a.val = 0 then (PowerSeries.X : PowerSeries k) ^ r *
                ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar k r c a.val b.val ζ
               else ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar k r c a.val b.val ζ) := by
  intro k _ _ r c ζ hr hc hdiv hcop hζ a b
  have hζb : ζ ^ b.val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  let j := (r * a.val / c + r - 1) % r
  obtain ⟨RX, RY, E, sX, sY, hcompat⟩ :=
    completed_section_gluing k r j (ζ ^ b.val) hζb hr (by
      dsimp [j]
      exact Nat.mod_lt _ hr)
  have hnext : next r j = r * a.val / c := by
    dsimp [j, next]
    have hq : r * a.val / c < r := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < c)).2
      exact Nat.mul_lt_mul_of_pos_left a.isLt hr
    by_cases hq0 : r * a.val / c = 0
    · have hr1 : 1 ≤ r := hr
      have hmod : (r * a.val / c + r - 1) % r = r - 1 := by
        simp [hq0, Nat.mod_eq_of_lt (Nat.sub_lt hr1 hr)]
      rw [hmod]
      rw [Nat.sub_add_cancel hr1, Nat.mod_self]
      exact hq0.symm
    · have hqpos : 0 < r * a.val / c := Nat.pos_of_ne_zero hq0
      have hqsub : r * a.val / c - 1 < r :=
        lt_of_le_of_lt (Nat.sub_le _ _) hq
      have hmod : (r * a.val / c + r - 1) % r = r * a.val / c - 1 := by
        calc
          (r * a.val / c + r - 1) % r =
              ((r * a.val / c - 1) + r) % r := by
                rw [show r * a.val / c + r - 1 =
                    (r * a.val / c - 1) + r by omega]
          _ = r * a.val / c - 1 := by
            simp [Nat.add_mod, Nat.mod_eq_of_lt hqsub]
      rw [hmod]
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq0)]
      exact Nat.mod_eq_of_lt hq
  refine ⟨hζb, RX, RY, E, sX, sY, hcompat, ?_, ?_, ?_⟩
  · exact hnext
  · have hcoordX :
        RX (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k (next r j)) =
          completeOpen k (next r j) true (oz k (next r j) true) := by
      have hR := DFunLike.congr_fun hcompat.1.1
        ((ArithmeticThetaScaledTateBridgeR0046.t k 1) ^ (next r j) *
          ArithmeticThetaScaledTateBridgeR0046.x k 1)
      have ht : ArithmeticThetaScaledTateBridgeR0046.t k 1 =
          ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X := by
        simp [ArithmeticThetaScaledTateBridgeR0046.t,
          ArithmeticThetaScaledTateBridgeR0046.parameter,
          ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase]
      have hnode := ht.symm
      convert hR using 1 <;>
        simp [ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate,
        ArithmeticThetaAnnularTorsionPrereqR0053.tau,
        ArithmeticThetaAnnularTorsionPrereqR0053.cx,
        ArithmeticThetaScaledAnnularR0050.tau,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaAnnularTorsionPrereqR0053.complete,
        ArithmeticThetaScaledTateBridgeR0046.toCompleted,
        ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
        ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter,
        oz, ot, ox, openMap, openBase,
        ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase, hnode,
        node_equiv_x]
    have hchartX (q : ℕ) :
        selectedSection k true (ζ ^ b.val) hζb
            (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k q) =
          PowerSeries.C (ζ ^ b.val) * PowerSeries.X ^ q := by
      have ht : selectedSection k true (ζ ^ b.val) hζb
          (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X := by
        change selectedSection k true (ζ ^ b.val) hζb
            (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) = _
        exact DFunLike.congr_fun
          (selected_section_spec k true (ζ ^ b.val) hζb).1 PowerSeries.X
      rw [ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate, map_mul,
        map_pow, ht]
      have hcx : selectedSection k true (ζ ^ b.val) hζb
          (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
            PowerSeries.C (ζ ^ b.val) := by
        simpa [ArithmeticThetaAnnularTorsionPrereqR0053.coord] using
          (selected_section_spec k true (ζ ^ b.val) hζb).2.1
      rw [hcx]
      ring
    rw [← hcoordX]
    change (sX.comp RX)
      (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k (next r j)) = _
    rw [hcompat.2.2.2.2.2.1, hchartX]
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar,
      ArithmeticThetaAnnularTorsionPrereqR0053.torsionExponent, hnext, hζ0]
  · have hcoordY :
        RY (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k j) =
          completeOpen k j false (oz k j false) := by
      have hR := DFunLike.congr_fun hcompat.2.1.1
        ((ArithmeticThetaScaledTateBridgeR0046.t k 1) ^ j *
          ArithmeticThetaScaledTateBridgeR0046.x k 1)
      have ht : ArithmeticThetaScaledTateBridgeR0046.t k 1 =
          ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X := by
        simp [ArithmeticThetaScaledTateBridgeR0046.t,
          ArithmeticThetaScaledTateBridgeR0046.parameter,
          ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase]
      have hnode := ht.symm
      convert hR using 1 <;>
        simp [ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate,
        ArithmeticThetaAnnularTorsionPrereqR0053.tau,
        ArithmeticThetaAnnularTorsionPrereqR0053.cx,
        ArithmeticThetaScaledAnnularR0050.tau,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaAnnularTorsionPrereqR0053.complete,
        ArithmeticThetaScaledTateBridgeR0046.toCompleted,
        ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
        ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter,
        oz, ot, ox, openMap, openBase,
        ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase, hnode,
        node_equiv_x]
    have hchartY (q : ℕ) :
        selectedSection k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)
            (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k q) =
          PowerSeries.C ((ζ ^ b.val)⁻¹)⁻¹ * PowerSeries.X ^ (q + 1) := by
      have ht : selectedSection k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)
          (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X := by
        change selectedSection k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)
            (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) = _
        exact DFunLike.congr_fun
          (selected_section_spec k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)).1 PowerSeries.X
      rw [ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate, map_mul,
        map_pow, ht]
      have hcx : selectedSection k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)
          (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
            PowerSeries.C ((ζ ^ b.val)⁻¹)⁻¹ * PowerSeries.X := by
        simpa [ArithmeticThetaAnnularTorsionPrereqR0053.coord] using
          (selected_section_spec k false (ζ ^ b.val)⁻¹ (inv_ne_zero hζb)).2.2.1
      rw [hcx, pow_succ]
      ring
    rw [← hcoordY]
    change (sY.comp RY)
      (ArithmeticThetaAnnularTorsionPrereqR0053.chartCoordinate k j) = _
    rw [hcompat.2.2.2.2.2.2.1, hchartY]
    by_cases ha0 : a.val = 0
    · have hq0 : r * a.val / c = 0 := by simp [ha0]
      have hj : j = r - 1 := by
        dsimp [j]
        simp [hq0, Nat.mod_eq_of_lt
          (Nat.sub_lt (Nat.one_le_iff_ne_zero.mpr hr.ne') hr)]
      rw [hj]
      rw [show r - 1 + 1 = r by omega]
      simp [ha0, hζ0, ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar,
        ArithmeticThetaAnnularTorsionPrereqR0053.torsionExponent,
        inv_inv, mul_assoc, mul_left_comm, mul_comm]
    · have hqpos : 0 < r * a.val / c := by
        apply Nat.pos_of_ne_zero
        intro hq0
        have hmul : r * a.val = 0 := by
          have hca : c ∣ r * a.val := dvd_mul_of_dvd_left hdiv a.val
          exact Nat.eq_zero_of_dvd_of_div_eq_zero hca hq0
        rcases Nat.mul_eq_zero.mp hmul with hr0 | ha0'
        · omega
        · exact ha0 ha0'
      have hq_lt : r * a.val / c < r := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < c)).2
        exact Nat.mul_lt_mul_of_pos_left a.isLt hr
      have hj : j = r * a.val / c - 1 := by
        dsimp [j]
        calc
          (r * a.val / c + r - 1) % r =
              ((r * a.val / c - 1) + r) % r := by
                rw [show r * a.val / c + r - 1 =
                    (r * a.val / c - 1) + r by omega]
          _ = r * a.val / c - 1 := by
            simp [Nat.add_mod, Nat.mod_eq_of_lt
              (lt_of_le_of_lt (Nat.sub_le _ _) hq_lt)]
      rw [hj, show r * a.val / c - 1 + 1 = r * a.val / c by omega]
      simp [ha0, hζ0, ArithmeticThetaAnnularTorsionPrereqR0053.torsionScalar,
        ArithmeticThetaAnnularTorsionPrereqR0053.torsionExponent,
        inv_inv, mul_assoc, mul_left_comm, mul_comm]

end ArithmeticThetaIndexedOverlapsR0058
