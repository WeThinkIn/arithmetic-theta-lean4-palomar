import AlgebraicTateCoordinatesR0143

/-! Evaluation of the literal coordinates at the actual marked sections. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaAlgebraicCoordinatesR0143
namespace CoordinateMarkedEvaluationR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaTateSeries
variable (k : Type u) [Field k] [CharZero k]

abbrev q (n : ℕ) := trunc (PowerSeries k) PowerSeries.X n

lemma q_eq (n : ℕ) (f g : PowerSeries k)
    (h : ∀ j, j < n+1 → PowerSeries.coeff j f = PowerSeries.coeff j g) :
    q k n f = q k n g := by
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro j hj
  simp only [map_sub, h j hj, sub_self]

lemma partial_reduction (r n : ℕ) (i : Fin r) (a : kˣ)
    (hr : 0 < r) (ha : i.val = 0 → (a : k) ≠ 1) :
    q k n (partialX r i.val (a : k) (n+1)) = q k n (tateX r i.val (a : k)) ∧
    q k n (partialY r i.val (a : k) (n+1)) = q k n (tateY r i.val (a : k)) := by
  have had : Admissible r i.val (a : k) := ⟨hr, i.isLt, Units.ne_zero a, ha⟩
  constructor
  · apply q_eq
    intro j hj
    simpa [tateX] using (ArithmeticThetaTateBridges.annular_stabilization
      r i.val (a : k) had j (n+1) (by omega)).1
  · apply q_eq
    intro j hj
    simpa [tateY] using (ArithmeticThetaTateBridges.annular_stabilization
      r i.val (a : k) had j (n+1) (by omega)).2

lemma marked_base (n : ℕ) (a : kˣ) (c : R k n) :
    markedPoint k n a (base k n c) = c :=
  RingHom.congr_fun (SmoothMarkedSections.markedPoint_base k n a) c

lemma marked_x (n : ℕ) (a : kˣ) :
    markedPoint k n a (coordX k n) = q k n (PowerSeries.C (a : k)) := mkPoint_x ..

lemma marked_y (n : ℕ) (a : kˣ) :
    markedPoint k n a (coordY k n) = q k n (monomial (a : k)⁻¹ 1) := by
  rw [markedPoint, mkPoint_y]
  simp [markedUnit, monomial, q, parameter, mul_comm]

lemma marked_tau (n : ℕ) (a : kˣ) :
    markedPoint k n a (tau k n) = q k n PowerSeries.X := marked_base k n a _

lemma marked_positive (n e : ℕ) (a : kˣ) :
    markedPoint k n a (tau k n ^ e * coordX k n) = q k n (monomial (a : k) e) := by
  simp only [map_mul, map_pow, marked_tau, marked_x, monomial]
  ring

lemma marked_negative (n e : ℕ) (a : kˣ) :
    markedPoint k n a (tau k n ^ e * coordY k n) = q k n (monomial (a : k)⁻¹ (e+1)) := by
  simp only [map_mul, map_pow, marked_tau, marked_y, monomial, pow_succ]
  ring

lemma inverse_geom (n e : ℕ) (c : k) (he : 0 < e) :
    q k n ((1 - monomial c e)⁻¹) =
      ∑ j ∈ Finset.range (n+1), (q k n (monomial c e))^j := by
  have hz : (q k n (monomial c e))^(n+1) = 0 := by
    simp only [monomial, map_mul, map_pow, mul_pow, ← pow_mul]
    rw [pow_eq_zero_of_le (show n+1 ≤ e*(n+1) by nlinarith) (show (q k n PowerSeries.X)^(n+1) = 0 from parameter_pow k n), mul_zero]
  have hi : (1-q k n (monomial c e)) * q k n ((1-monomial c e)⁻¹) = 1 := by
    rw [← map_one (q k n), ← map_sub, ← map_mul]
    congr 1
    apply PowerSeries.mul_inv_cancel
    simp [monomial, ne_of_gt he]
  have hg : (∑ j ∈ Finset.range (n+1), (q k n (monomial c e))^j) *
      (1-q k n (monomial c e)) = 1 := by
    simpa [hz] using geom_sum_mul_neg (q k n (monomial c e)) (n+1)
  calc
    _ = 1 * q k n ((1-monomial c e)⁻¹) := (one_mul _).symm
    _ = _ := by rw [← hg, mul_assoc, hi, mul_one]

def scalarTerm (odd : Bool) (v : PowerSeries k) : PowerSeries k :=
  v * (if odd then 1+v else 1) * ((1-v)⁻¹)^degree odd

lemma map_term (odd : Bool) (n : ℕ) (f : A k n →+* R k n) (v : A k n)
    (c : k) (e : ℕ) (he : 0 < e) (hv : f v = q k n (monomial c e)) :
    f (term k odd n v) = q k n (scalarTerm k odd (monomial c e)) := by
  cases odd <;>
    simp only [term, scalarTerm, Bool.false_eq_true, ↓reduceIte, geometric,
      map_mul, map_add, map_one, map_pow, map_sum, hv, inverse_geom k n e c he]

lemma scalarTerm_cleared (odd : Bool) (v : PowerSeries k)
    (hv : PowerSeries.constantCoeff (1-v) ≠ 0) :
    (1-v)^degree odd * scalarTerm k odd v = v * (if odd then 1+v else 1) := by
  have hi := PowerSeries.mul_inv_cancel (1-v) hv
  calc
    _ = (v * (if odd then 1+v else 1)) * ((1-v) * (1-v)⁻¹)^degree odd := by
      simp only [scalarTerm, mul_pow]; ring
    _ = _ := by rw [hi, one_pow, mul_one]

def scalarEquation (r : ℕ) (i : Fin r) (a : kˣ) : PowerSeries k :=
  (if i.val = 0 then 1-PowerSeries.C (a : k) else 1) *
    (if i.val+1 = r then 1-monomial (a : k)⁻¹ 1 else 1)

lemma marked_equation (r n : ℕ) (i : Fin r) (a : kˣ) :
    markedPoint k n a (equation k r n i) = q k n (scalarEquation k r i a) := by
  unfold equation scalarEquation
  split_ifs <;> simp only [map_mul, map_sub, map_one, marked_x, marked_y]

lemma scalarEquation_unit (r : ℕ) (i : Fin r) (a : kˣ)
    (ha : i.val = 0 → (a : k) ≠ 1) : IsUnit (scalarEquation k r i a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  unfold scalarEquation
  split_ifs with hi hl hl <;> simp [monomial, sub_ne_zero]
  all_goals exact Ne.symm (ha hi)

lemma marked_first (odd : Bool) (r n : ℕ) (h3 : 3 ≤ r) (i : Fin r) (a : kˣ)
    (ha : i.val = 0 → (a : k) ≠ 1) :
    markedPoint k n a
      (if i.val = 0 then coordX k n * (if odd then 1+coordX k n else 1)
       else equation k r n i ^ degree odd * term k odd n (tau k n ^ i.val * coordX k n)) =
    q k n (scalarEquation k r i a ^ degree odd * scalarTerm k odd (monomial (a : k) i.val)) := by
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    have hl : ¬ (0+1 = r) := by omega
    have hc : PowerSeries.constantCoeff (1-PowerSeries.C (a : k)) ≠ 0 := by
      simpa only [map_sub, map_one, PowerSeries.constantCoeff_C, sub_ne_zero] using Ne.symm (ha hi)
    simp only [scalarEquation, hi, hl, ↓reduceIte, mul_one, monomial, pow_zero]
    rw [scalarTerm_cleared k odd _ hc]
    cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte, map_mul, map_add, map_one, marked_x]
  · rw [if_neg hi, map_mul, map_pow, marked_equation,
      map_term k odd n (markedPoint k n a) _ (a : k) i.val (by omega)
        (marked_positive k n i.val a), map_mul, map_pow]

lemma marked_neg_summand (odd : Bool) (r n : ℕ) (h3 : 3 ≤ r)
    (i : Fin r) (a : kˣ) (j : ℕ) :
    markedPoint k n a
      (if j = 0 ∧ i.val+1 = r then coordY k n * (if odd then 1+coordY k n else 1)
       else equation k r n i ^ degree odd *
        term k odd n (tau k n ^ (r*(j+1)-i.val-1) * coordY k n)) =
    q k n (scalarEquation k r i a ^ degree odd *
      scalarTerm k odd (monomial (a : k)⁻¹ (r*(j+1)-i.val))) := by
  have he : 0 < r*(j+1)-i.val := by
    have hh := i.isLt
    have hh' : r ≤ r*(j+1) := by nlinarith
    omega
  by_cases hj : j = 0 ∧ i.val+1 = r
  · rw [if_pos hj]
    obtain ⟨rfl, hl⟩ := hj
    have hi : ¬ i.val = 0 := by omega
    have hdeg : r*(0+1)-i.val = 1 := by omega
    have hc : PowerSeries.constantCoeff (1-monomial (a : k)⁻¹ 1) ≠ 0 := by simp [monomial]
    simp only [scalarEquation, hi, hl, ↓reduceIte, one_mul, hdeg]
    rw [scalarTerm_cleared k odd _ hc]
    cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte, map_mul, map_add, map_one, marked_y]
  · rw [if_neg hj, map_mul, map_pow, marked_equation,
      map_term k odd n (markedPoint k n a) _ (a : k)⁻¹ (r*(j+1)-i.val-1+1)
        (by omega) (marked_negative k n _ a), map_mul, map_pow]
    rw [Nat.sub_add_cancel he]

lemma marked_pos_summand (odd : Bool) (r n : ℕ) (hr : 0 < r)
    (i : Fin r) (a : kˣ) (j : ℕ) :
    markedPoint k n a (term k odd n (tau k n ^ (r*(j+1)+i.val) * coordX k n)) =
      q k n (scalarTerm k odd (monomial (a : k) (r*(j+1)+i.val))) :=
  map_term k odd n _ _ _ _ (by nlinarith) (marked_positive k n _ a)

lemma marked_correction (r n : ℕ) (hr : 0 < r) (a : kˣ) (j : ℕ) :
    markedPoint k n a
      ((j+1 : ℕ) * tau k n ^ (r*(j+1)) * geometric k n (tau k n ^ (r*(j+1)))) =
    q k n (PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (r*(j+1)) *
      (1-monomial 1 (r*(j+1)))⁻¹) := by
  have he : 0 < r*(j+1) := by nlinarith
  have hg := inverse_geom k n (r*(j+1)) 1 he
  simp only [monomial, map_one, one_mul, map_pow] at hg
  simp only [map_mul, map_natCast, map_pow, marked_tau, geometric, map_sum,
    monomial, map_one, one_mul, map_natCast, hg]


lemma numerator_at_marked (odd : Bool) (r n : ℕ) (h3 : 3 ≤ r)
    (i : Fin r) (a : kˣ) (ha : i.val = 0 → (a : k) ≠ 1) :
    markedPoint k n a (numerator k odd r n i) =
    (markedPoint k n a (equation k r n i))^degree odd *
      q k n (if odd then tateY r i.val (a : k) else tateX r i.val (a : k)) := by
  have hr : 0 < r := by omega
  have hp := partial_reduction k r n i a hr ha
  have hf := marked_first k odd r n h3 i a ha
  have hn := marked_neg_summand k odd r n h3 i a
  have hpos := marked_pos_summand k odd r n hr i a
  have hc := marked_correction k r n hr a
  cases odd
  · simp only [Bool.false_eq_true, ↓reduceIte] at hf hn hpos ⊢
    simp only [numerator, Bool.false_eq_true, ↓reduceIte, map_sub, map_add]
    simp only [hf, hn, hpos, hc, map_add, map_sub, map_mul, map_pow,
      map_sum, map_ofNat, marked_equation]
    rw [← hp.1]
    simp only [partialX, map_sub, map_add, map_sum, map_mul, map_ofNat,
      scalarTerm, degree, Bool.false_eq_true, ↓reduceIte, mul_one, xTerm,
      map_pow, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · simp only [↓reduceIte] at hf hn hpos ⊢
    simp only [numerator, ↓reduceIte]
    simp only [hf, hn, hpos, hc, marked_base, map_add, map_sub, map_mul, map_pow,
      map_sum, map_ofNat, marked_equation]
    rw [← hp.2]
    simp only [partialY, scalarTerm, degree, ↓reduceIte, yTerm,
      map_mul, map_add, map_sub, map_sum, map_pow, map_one,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (chartIso chartIso_inclusion)
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation)
open ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140
  (baseRestriction)

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def chartMap (M : Model k T) (n : ℕ) (i : Fin r) : specA k n ⟶ M.X :=
  (T.atlas n).chart i ≫ M.inclusion n

def chartFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (i : Fin r) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶
      (Scheme.Modules.pullback (chartMap k M n i)).obj (powerModule k M s d) :=
  fromSection _ (IdentityStageSectionRealizationR0138.localGenerator
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d i) ≫
    (chartIso ((T.atlas n).chart i) (M.inclusion n) _ _
      (stageIso k h3 M hM s hs d n)).inv

instance chartFrame_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (i : Fin r) : IsIso (chartFrame k h3 M hM s hs d n i) := by
  letI := IdentityStageSectionRealizationR0138.localGenerator_frame
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d i
  unfold chartFrame
  infer_instance

lemma chartFrame_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (i : Fin r) :
    chartFrame k h3 M hM s hs d n i ≫
      pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^d)) =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (equation k r n i ^ d)) := by
  have he := chartIso_inclusion ((T.atlas n).chart i) (M.inclusion n)
    (powerModule k M s d) (stageModule k (T.atlas n) d) (stageIso k h3 M hM s hs d n)
    (idealInclusion (s.ker^d)) (idealInclusion ((stageIdeal k (T.atlas n))^d))
    (stageIso_inclusion k h3 M hM s hs d n)
  change _ = pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^d)) at he
  rw [← he]
  simp only [chartFrame, Category.assoc, Iso.inv_hom_id_assoc]
  exact IdentityStageSectionRealizationR0138.frame_inclusion
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d i

lemma chart_mono (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (i : Fin r) :
    Mono (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^d))) := by
  have he := chartIso_inclusion ((T.atlas n).chart i) (M.inclusion n)
    (powerModule k M s d) (stageModule k (T.atlas n) d) (stageIso k h3 M hM s hs d n)
    (idealInclusion (s.ker^d)) (idealInclusion ((stageIdeal k (T.atlas n))^d))
    (stageIso_inclusion k h3 M hM s hs d n)
  change _ = pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^d)) at he
  rw [← he]
  letI : IsOpenImmersion ((T.atlas n).chart i) := (T.atlas n).chart_open _
  letI := (pullback_open_realization ((T.atlas n).chart i)
    ((stageIdeal k (T.atlas n))^d) _ _ (ideal_realization _)).1
  infer_instance

lemma chartFrame_value (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (n : ℕ) (i : Fin r) :
    chartFrame k h3 M hM s hs (degree odd) n i ≫
      pulledInclusion (chartMap k M n i) φ =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (numerator k odd r n i)) := by
  obtain ⟨z, hz, hv⟩ := hφ n i
  letI := chart_mono k h3 M hM s hs (degree odd) n i
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => Scheme.Modules.Hom.app f ⊤)
      (chartFrame_inclusion k h3 M hM s hs (degree odd) n i)) (1 : Γ(specA k n, ⊤))
  have hz' : (Scheme.Modules.Hom.app (X := specA k n)
      (chartFrame k h3 M hM s hs (degree odd) n i) ⊤) (1 : Γ(specA k n, ⊤)) = z := by
    apply mono_app_injective (pulledInclusion (chartMap k M n i) (idealInclusion _)) ⊤
    have hc' : (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^degree odd))).app ⊤
        ((Scheme.Modules.Hom.app (X := specA k n)
          (chartFrame k h3 M hM s hs (degree odd) n i) ⊤) (1 : Γ(specA k n, ⊤))) =
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (equation k r n i ^ degree odd) := by
      change (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^degree odd))).app ⊤
        ((Scheme.Modules.Hom.app (X := specA k n)
          (chartFrame k h3 M hM s hs (degree odd) n i) ⊤) (1 : Γ(specA k n, ⊤))) = _ at hc
      simpa [fromSection_apply] using hc
    exact hc'.trans hz.symm
  apply unit_hom_ext
  change (pulledInclusion (chartMap k M n i) φ).app ⊤
      ((Scheme.Modules.Hom.app (X := specA k n)
        (chartFrame k h3 M hM s hs (degree odd) n i) ⊤) (1 : Γ(specA k n, ⊤))) = _
  rw [hz']
  change (pulledInclusion (chartMap k M n i) φ).app ⊤ z = _ at hv
  simpa [fromSection_apply] using hv

def point (n : ℕ) (a : kˣ) : specR k n ⟶ specA k n :=
  Spec.map (CommRingCat.ofHom (markedPoint k n a))

lemma point_value (n : ℕ) (a : kˣ) (v : A k n) :
    (point k n a).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv v) =
      (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv (markedPoint k n a v) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (markedPoint k n a))) v).symm

lemma point_square (M : Model k T) (i : Fin r) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) (n : ℕ) :
    point k n a ≫ chartMap k M n i = baseRestriction k n ≫ p := by
  exact (hp.2 n).symm

def pointFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (n : ℕ) :=
  pullFrame (point k n a) (chartFrame k h3 M hM s hs d n i) ≫
    (squareIso (chartMap k M n i) (point k n a) p (baseRestriction k n)
      (point_square k M i a p hp n) (powerModule k M s d)).inv

instance pointFrame_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (n : ℕ) :
    IsIso (pointFrame k h3 M hM s hs d i a p hp n) := by
  letI := pullFrame_isIso (point k n a) (chartFrame k h3 M hM s hs d n i)
  unfold pointFrame
  infer_instance

lemma pointFrame_eval (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (n : ℕ) (φ : Dual k M s d) (v : A k n)
    (hv : chartFrame k h3 M hM s hs d n i ≫ pulledInclusion (chartMap k M n i) φ =
      fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv v)) :
    pointFrame k h3 M hM s hs d i a p hp n ≫
      pulledInclusion (baseRestriction k n) (pulled k M s d p φ) =
    fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv (markedPoint k n a v)) := by
  have he := squareIso_inclusion (chartMap k M n i) (point k n a) p
    (baseRestriction k n) (point_square k M i a p hp n) (powerModule k M s d) φ
  change _ = pulledInclusion (baseRestriction k n) (pulled k M s d p φ) at he
  rw [← he]
  simp only [pointFrame, Category.assoc, Iso.inv_hom_id_assoc]
  rw [pullFrame_evaluation _ _ _ _ hv, point_value]

lemma multiplication_unit {X : Scheme.{u}} (v : Γ(X, ⊤)) (hv : IsUnit v) :
    IsIso (C := X.Modules) (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) v) := by
  apply unitEnd_isIso
  have he : (fun x : Γ(X, ⊤) =>
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) v).app ⊤ x) =
      (fun x : Γ(X, ⊤) => x * v) := by
    funext x
    simp [fromSection_apply]
  rw [show ⇑((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) v).app ⊤) = _ from he]
  exact IsUnit.isUnit_iff_mulRight_bijective (M := Γ(X, ⊤)) |>.mp hv

lemma finite_ideal_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (i : Fin r) (a : kˣ) (ha : i.val = 0 → (a : k) ≠ 1)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) (n : ℕ) :
    IsIso (pulledInclusion (baseRestriction k n) (pulledIdeal k M s d p)) := by
  have he := pointFrame_eval k h3 M hM s hs d i a p hp n
    (idealInclusion (s.ker^d)) (equation k r n i ^ d)
    (chartFrame_inclusion k h3 M hM s hs d n i)
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv
      (markedPoint k n a (equation k r n i ^ d))) := by
    rw [map_pow, marked_equation]
    exact ((scalarEquation_unit k r i a ha).map (q k n) |>.pow d).map
      (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv.hom
  have hh := multiplication_unit (X := specR k n) _ hu
  rw [← he] at hh
  change IsIso (pointFrame k h3 M hM s hs d i a p hp n ≫
    pulledInclusion (baseRestriction k n) (pulledIdeal k M s d p)) at hh
  letI := hh
  exact IsIso.of_isIso_comp_left (pointFrame k h3 M hM s hs d i a p hp n) _

def scalarMap (g : PowerSeries k) :
    (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules) ⟶
      (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules) :=
  fromSection _ ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g)

lemma base_value (n : ℕ) (g : PowerSeries k) :
    (baseRestriction k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g) =
      (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv (q k n g) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (q k n))) g).symm

lemma finite_value (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (i : Fin r) (a : kˣ) (ha : i.val = 0 → (a : k) ≠ 1)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) (n : ℕ) :
    pulledInclusion (baseRestriction k n) (pulled k M s (degree odd) p φ) =
    pulledInclusion (baseRestriction k n)
      (pulledIdeal k M s (degree odd) p ≫
        scalarMap k (if odd then tateY r i.val (a : k) else tateX r i.val (a : k))) := by
  let g := if odd then tateY r i.val (a : k) else tateX r i.val (a : k)
  have hv := pointFrame_eval k h3 M hM s hs (degree odd) i a p hp n φ
    (numerator k odd r n i) (chartFrame_value k h3 M hM s hs odd φ hφ n i)
  have hj := pointFrame_eval k h3 M hM s hs (degree odd) i a p hp n
    (idealInclusion (s.ker^degree odd)) (equation k r n i ^ degree odd)
    (chartFrame_inclusion k h3 M hM s hs (degree odd) n i)
  apply (cancel_epi (pointFrame k h3 M hM s hs (degree odd) i a p hp n)).mp
  rw [hv]
  have hm : pulledInclusion (baseRestriction k n)
      (pulledIdeal k M s (degree odd) p ≫ scalarMap k g) =
    pulledInclusion (baseRestriction k n) (pulledIdeal k M s (degree odd) p) ≫
      fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv (q k n g)) := by
    simp only [pulledInclusion, Functor.map_comp, Category.assoc]
    rw [scalarMap, pullback_multiplication, base_value]
  change _ = pointFrame k h3 M hM s hs (degree odd) i a p hp n ≫
    pulledInclusion (baseRestriction k n) (pulledIdeal k M s (degree odd) p ≫ scalarMap k g)
  rw [hm, ← Category.assoc]
  change _ = (pointFrame k h3 M hM s hs (degree odd) i a p hp n ≫
    pulledInclusion (baseRestriction k n)
      (pulled k M s (degree odd) p (idealInclusion (s.ker^degree odd)))) ≫ _
  rw [hj]
  apply unit_hom_ext
  change _ = (fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv (q k n g))).app ⊤
      ((fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv
          (markedPoint k n a (equation k r n i ^ degree odd)))).app ⊤ (1 : Γ(specR k n, ⊤)))
  simp [fromSection_apply, numerator_at_marked k odd r n h3 i a ha, map_mul, map_pow, g]

lemma full_value (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (i : Fin r) (a : kˣ) (ha : i.val = 0 → (a : k) ≠ 1)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) :
    HasValue k M s (degree odd) p φ
      (if odd then tateY r i.val (a : k) else tateX r i.val (a : k)) := by
  have hF := ((power_invertible k h3 M hM s hs (degree odd)).isInvertible_module.pullback p)
  have hG := Scheme.Modules.isInvertible_unit (baseScheme k)
  constructor
  · apply ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.base_isIso_of_pullbacks
      k _ _ hF hG
    intro n
    letI := unitPullback_isIso (baseRestriction k n)
    have hh := finite_ideal_isIso k h3 M hM s hs (degree odd) i a ha p hp n
    change IsIso ((Scheme.Modules.pullback (baseRestriction k n)).map
      (pulledIdeal k M s (degree odd) p) ≫ unitPullback (baseRestriction k n)) at hh
    letI := hh
    exact IsIso.of_isIso_comp_right _ (unitPullback (baseRestriction k n))
  · have he : pulled k M s (degree odd) p φ =
        pulledIdeal k M s (degree odd) p ≫ scalarMap k
          (if odd then tateY r i.val (a : k) else tateX r i.val (a : k)) := by
      apply ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.base_hom_ext
        k _ _ hF hG
      intro n
      letI := unitPullback_isIso (baseRestriction k n)
      apply (cancel_mono (unitPullback (baseRestriction k n))).mp
      exact finite_value k h3 M hM s hs odd φ hφ i a ha p hp n
    intro U x
    rw [he]
    change (Scheme.Modules.Hom.app (X := baseScheme k) (scalarMap k _) U) ((pulledIdeal k M s (degree odd) p).app U x) = _
    simp only [scalarMap, fromSection_apply, baseScalar]
    exact mul_comm (G := (baseScheme k).presheaf.obj (Opposite.op U)) _ _

end CoordinateMarkedEvaluationR0143

/-- Full Tate-series evaluation of the actual algebraic coordinates along every disjoint marking. -/
theorem coordinate_marked_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
      (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s),
      ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (degree odd)),
      RealizesCoordinate k odd M s φ → ∀ (i : Fin r) (a : kˣ),
      (i.val = 0 → (a : k) ≠ 1) →
      ∀ p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X,
      ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M i a p →
      HasValue k M s (degree odd) p φ
        (if odd then ArithmeticThetaTateSeries.tateY r i.val (a : k)
         else ArithmeticThetaTateSeries.tateX r i.val (a : k)) := by
  intro k _ _ r hr h3 T M hM s hs odd φ hφ i a ha p hp
  exact CoordinateMarkedEvaluationR0143.full_value k h3 M hM s hs odd φ hφ i a ha p hp

end ArithmeticThetaAlgebraicCoordinatesR0143
#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_marked_evaluation
