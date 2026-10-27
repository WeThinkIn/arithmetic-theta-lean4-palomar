import OpenIsogenyAlphaR0193

/-! All-cusp orders for the actual normalized cyclic-isogeny alpha. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaIsogenyHalfLinesR0193
namespace IsogenyAlphaAllCuspOrders
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback ArithmeticThetaTensorPower
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality

/-- Minimal arithmetic hypotheses supply the accepted mixed-quotient bounds. -/
lemma level_bounds (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hdiv : 8*m ∣ L) :
    3 ≤ L ∧ Even L ∧ m ∣ L ∧ 3 ≤ L/m ∧ Even (L/m) ∧ 8 ∣ L/m := by
  obtain ⟨q, rfl⟩ := hdiv
  have hq : 0 < q := by nlinarith
  have heq : 8*m*q = m*(8*q) := by ring
  rw [heq, Nat.mul_div_cancel_left _ hm]
  refine ⟨?_, ?_, dvd_mul_right m (8*q), ?_, ?_, ⟨q, rfl⟩⟩
  · nlinarith
  · exact ((show Even 8 by decide).mul_right q).mul_left m
  · omega
  · exact (show Even 8 by decide).mul_right q

/-- The target period and its quarter order are computed without rounded
rational expressions. This also retains the residual component case. -/
lemma order_arithmetic (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hdiv : 8*m ∣ L) (i : Fin L) (hdm : L / L.gcd i.val ∣ m) :
    let d := L / L.gcd i.val
    let e := m / d
    let t := e * L.gcd i.val
    0 < d ∧ 0 < e ∧ e*d = m ∧ 8 ∣ t ∧
      4*m*(t/4) = L*e^2 ∧ Even (t/4) := by
  dsimp only
  let g := L.gcd i.val
  let d := L/g
  let e := m/d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left i.val hL
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left i.val hL) hg
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd hm hdm) hd
  have hed : e*d = m := Nat.div_mul_cancel hdm
  have hgd : g*d = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L i.val)
  have hb := level_bounds L m hL hm hdiv
  have hLm : L/m*m = L := Nat.div_mul_cancel hb.2.2.1
  have hge : g = (L/m)*e := by nlinarith
  have ht8 : 8 ∣ e*g := by
    rw [hge]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hb.2.2.2.2.2 e) e
  obtain ⟨q, hq⟩ := ht8
  have ht4 : e*g/4 = 2*q := by omega
  refine ⟨hd, he, hed, ⟨q, hq⟩, ?_, ?_⟩
  · change 4*m*(e*g/4) = L*e^2
    have ht : e*g/4*4 = e*g := Nat.div_mul_cancel (dvd_trans (by decide : 4 ∣ 8) ⟨q,hq⟩)
    calc
      4*m*(e*g/4) = m*((e*g/4)*4) := by ring
      _ = m*(e*g) := by rw [ht]
      _ = L*e^2 := by rw [← hed, ← hgd]; ring
  · change Even (e*g/4)
    rw [ht4]
    exact even_two_mul q

lemma allowed_order_of_target (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hdiv : 8*m ∣ L) (i : Fin L) (hdm : L / L.gcd i.val ∣ m)
    (j : ℕ) (hj : j = 0 ∨ j = (m/(L/L.gcd i.val)*L.gcd i.val)/4) :
    AllowedOrder L m i j := by
  obtain ⟨hd, he, hed, _, heq, heven⟩ := order_arithmetic L m hL hm hdiv i hdm
  refine ⟨hd, hdm, he, hed, ?_, ?_⟩
  · rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact heven
  · rcases hj with h | rfl
    · exact Or.inl h
    · exact Or.inr heq

section FourMarking
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaCompactifiedDifferentialR0145
variable (k : Type) [Field k] [CharZero k]

/-- Literal roots depend on the Tate equation, not on equality between the
period exponent and the level of the supplied marking. -/
lemma label_literal (r n : ℕ)
    (G : Law (LaurentSeries k) (TateCurve k r))
    (M : FullLevel (LaurentSeries k) (TateCurve k r) G n (𝟙 (Base (LaurentSeries k))))
    (e : Fin 3 → LaurentSeries k)
    (he : Labels (LaurentSeries k) (TateCurve k r) G n M e) (i : Fin 3) :
    ∃ j : Fin 3, e i = root k r j := by
  have h := TwoTorsionSplitCubicR0177.root_equation (he i)
  simp only [TateCurve, curve, zero_mul, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hz : (e i - root k r 0) * (e i - root k r 1) * (e i - root k r 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hz with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact ⟨0, sub_eq_zero.mp ha⟩
    · exact ⟨1, sub_eq_zero.mp hb⟩
  · exact ⟨2, sub_eq_zero.mp hc⟩

lemma root_coefficient_integral (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (G : Law (LaurentSeries k) (TateCurve k L))
    (M : FullLevel (LaurentSeries k) (TateCurve k L) G 4 (𝟙 (Base (LaurentSeries k)))) (e : Fin 3 → LaurentSeries k) (x y g : LaurentSeries k)
    (h : RootData (LaurentSeries k) (TateCurve k L) G 4 M e x y g) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧
      2*g = algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.X^j * (v : PowerSeries k)) := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 0 < m := by omega
  obtain ⟨i, hi⟩ := label_literal k (4*m) 4 G M e h.1 1
  obtain ⟨j, hj⟩ := label_literal k (4*m) 4 G M e h.1 0
  have hij : i ≠ j := by
    intro hij
    have hu := h.2.1.1 1 0 (by decide)
    rw [hi, hj, hij, sub_self] at hu
    exact not_isUnit_zero hu
  have hg : g ≠ 0 := h.2.2.2.2.1.ne_zero
  have hs : g^2 = root k (4*m) i - root k (4*m) j := by
    simpa [hi, hj] using h.2.2.2.2.2.2
  have ho := congrArg (fun z : LaurentSeries k => z.order) hs
  rw [HahnSeries.order_pow] at ho
  have hr := rootSeries_difference_orders k m hm i j hij
  rw [map_sub] at hr
  change (root k (4*m) i - root k (4*m) j).order = _ at hr
  rw [hr] at ho
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h2 : (2 : LaurentSeries k) ≠ 0 := by norm_num
  have htwo : (2 : LaurentSeries k).order = 0 := by
    have hh : (HahnSeries.C (2:k) : LaurentSeries k).order = 0 := HahnSeries.order_C
    simpa only [map_ofNat] using hh
  have hmul : (2*g).order = g.order := by
    rw [HahnSeries.order_mul h2 hg, htwo, zero_add]
  by_cases hz : i = 0 ∨ j = 0
  · rw [if_pos hz] at ho
    have ho0 : (2*g).order = (0 : ℕ) := by rw [hmul]; simpa using ho
    obtain ⟨v, hv⟩ := unit_factor_of_order k (2*g) (mul_ne_zero h2 hg) 0 ho0
    exact ⟨v, 0, Or.inl rfl, hv⟩
  · rw [if_neg hz] at ho
    have hom : (2*g).order = (m : ℤ) := by
      rw [hmul]
      simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at ho
      omega
    obtain ⟨v, hv⟩ := unit_factor_of_order k (2*g) (mul_ne_zero h2 hg) m hom
    exact ⟨v, m, Or.inr (by omega), hv⟩

/-- The accepted four-torsion order calculation at arbitrary Tate period,
with the actual full-four marking and a prescribed normalized differential. -/
lemma four_marking_orders (r : ℕ) (hr : 0 < r) (h4 : 4 ∣ r)
    (G : Law (LaurentSeries k) (TateCurve k r))
    (M : FullLevel (LaurentSeries k) (TateCurve k r) G 4 (𝟙 (Base (LaurentSeries k))))
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k r)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
    (a : Γ(Hodge (LaurentSeries k) (TateCurve k r), ⊤))
    (ha : RealizesAlpha (LaurentSeries k) (TateCurve k r) G 4 M a) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = r/4) ∧
      a = scalar (LaurentSeries k)
        (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k r δ := by
  obtain ⟨e, x, y, g, ε, hd, hε, ha⟩ := ha
  obtain ⟨χ, hχ, hx, hy⟩ := hd.2.2.1.2
  have hy0 : y ≠ 0 := by
    have hu := hd.2.2.2.1
    simpa only [completedY, ArithmeticThetaTateCuspsR0181.TateCurve,
      ArithmeticThetaCompactifiedDifferentialR0145.curve, zero_mul, zero_add,
      mul_zero, add_zero] using hu.ne_zero
  have hg := normalized_hodge_eq k r δ ε hδ hε χ (by simpa only [hy] using hy0)
  rw [hg] at ha
  obtain ⟨v, j, hj, hv⟩ := root_coefficient_integral k r hr h4 G M e x y g hd
  exact ⟨v, j, hj, by simpa only [hv] using ha⟩
end FourMarking

section ActualKernel
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open QuotientComparison Models

lemma test_kernel_eq (k : Type) [Field k] [CharZero k]
    (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hmL : m ∣ L)
    (D : LevelData k L) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    (testCyclic (OpenDiscriminantFullTateExpansionR0182.affineTest k L V)
      (levelCyclic k L hL D m hm hmL)).point = testKernel k L m D V := by
  let C := OpenDiscriminantFullTateExpansionR0182.affineTest k L V
  apply C.cartesian.hom_ext
  · have ht := test_nsmul k L V _ _ V.classifies.2.2.2.1 (L/m)
    have hb : baseMap _ _ (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom =
        V.base ≫ D.quotient.inclusion := Spec.map_preimage _
    exact (liftSection_map C (levelCyclic k L hL D m hm hmL).point
      (levelCyclic k L hL D m hm hmL).over_eq).trans
        ((congrArg (fun b => b ≫ kernelPoint k L D.atlas m) hb).trans ht.symm)
  · exact (testCyclic C (levelCyclic k L hL D m hm hmL)).over_eq.trans
      (V.level.law.nsmul (𝟙 _) (L/m) V.level.marking.x).property.symm

/-- Keep the component, toric and period identities when packaging the accepted
mixed-quotient construction. No new quotient geometry is asserted here. -/
lemma exact_factorization (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hdiv : 8*m ∣ L)
    (P : Models.Presentation k L hL) (i : Fin L) (a : kˣ)
    (ho : orderOf (Multiplicative.ofAdd (i.val : ZMod L), a) = m) :
    ∃ F : Models.Factorization P m i a,
      F.d = L/L.gcd i.val ∧ F.e = m/(L/L.gcd i.val) ∧
      F.t = m/(L/L.gcd i.val)*L.gcd i.val ∧ L/L.gcd i.val ∣ m := by
  obtain ⟨hd, he, hdm, hed, htor, β, hβ, hβi⟩ :=
    KernelArithmetic.mixed_rescaling k L m hL hm i a ho
  have hb := level_bounds L m hL hm hdiv
  obtain ⟨he', ht3, hteven, htdiv, hidiv, hdeg, htotal⟩ :=
    Models.factor_exponents m hm hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 i hdm
  let e := m/(L/L.gcd i.val)
  let t := e*L.gcd i.val
  have hs : 0 < L*e := Nat.mul_pos hL he
  have ht : 0 < t := lt_of_lt_of_le (by decide : 0 < 3) ht3
  obtain ⟨I⟩ := Models.presentation_exists k (L*e) hs
    (P.three_le.trans (Nat.le_mul_of_pos_right L he)) (P.even.mul_right e)
  obtain ⟨T⟩ := Models.presentation_exists k t ht ht3 hteven
  refine ⟨⟨L/L.gcd i.val, e, t, he, hs, ht, I, T, htdiv, hidiv, hdeg,
    htotal, β, ?_, hβi⟩, rfl, rfl, rfl, hdm⟩
  simpa only [e, Nat.mul_comm] using hβ

/-- The actual cyclic generator has coordinates with its exact total order;
the factorization retains the numerical identities needed by AllowedOrder. -/
lemma labeled_factorization (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (P : Models.Presentation k L hL) :
    ∃ (i : Fin L) (a : kˣ) (F : Models.Factorization P m i a),
      Models.point P i a = testKernel k L m D V ∧ KernelCoordinates k L m D V i a ∧
      F.d = L/L.gcd i.val ∧ F.e = m/(L/L.gcd i.val) ∧
      F.t = m/(L/L.gcd i.val)*L.gcd i.val ∧ L/L.gcd i.val ∣ m := by
  have hb := level_bounds L m hL hm hdiv
  let C := OpenDiscriminantFullTateExpansionR0182.affineTest k L V
  let PC := levelCyclic k L hL D m hm hb.2.2.1
  let T := testCyclic C PC
  letI : NeZero L := ⟨hL.ne'⟩
  letI : NeZero (L : k) := ⟨Nat.cast_ne_zero.mpr hL.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k L
  let ζ : kˣ := (hz.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : k) L := by simpa only [ζ, (hz.isUnit hL.ne').unit_spec] using hz
  have hkill := (KernelArithmetic.cyclic_torsion_iff (LaurentSeries k) (TateCurve k L)
    V.level.law V.level.originLaw m hm T L).mpr hb.2.2.1
  obtain ⟨ij, hij⟩ := ModelCoordinates.torsion_section_marked k L hL P.three_le P.even
    P.tower P.model P.isModel P.zero P.markedZero P.law P.originLaw V.level.law V.level.originLaw
    P.cubic P.cubic_over P.cubic_zero ζ hζ T.point T.over_eq hkill
  have ho := ModelCoordinates.cyclic_label_order k L m hL hm P.three_le P.even
    P.tower P.model P.isModel P.zero P.markedZero P.law P.originLaw V.level.law V.level.originLaw
    P.cubic P.cubic_over P.cubic_zero T ij.1 (ζ^ij.2.val) hij
  obtain ⟨F, hd, he, ht, hdm⟩ := exact_factorization k L m hL hm hdiv P ij.1 (ζ^ij.2.val) ho
  have hne : ij.1.val ≠ 0 ∨ ((ζ^ij.2.val : kˣ) : k) ≠ 1 := by
    by_contra h
    push Not at h
    have hi : (ij.1.val : ZMod L) = 0 := by rw [h.1]; simp
    have ha : ζ^ij.2.val = 1 := Units.ext h.2
    rw [hi, ha] at ho
    have hm1 : m = 1 := by
      change orderOf ((1 : Multiplicative (ZMod L)), (1 : kˣ)) = m at ho
      simpa only [Prod.orderOf, orderOf_one, Nat.lcm_self] using ho.symm
    rw [hm1] at hmeven
    norm_num at hmeven
  have hp : Models.point P ij.1 (ζ^ij.2.val) = testKernel k L m D V :=
    hij.trans (test_kernel_eq k L m hL hm hb.2.2.1 D V)
  refine ⟨ij.1, ζ^ij.2.val, F, hp, ⟨hne, ?_⟩, hd, he, ht, hdm⟩
  rw [← hp]
  exact Models.point_coordinates P ij.1 (ζ^ij.2.val) hne
/-- The quotient test keeps the actual source kernel coordinates, the exact
component degree, and the numerical target period visible to the consumer. -/
lemma comparison_with_labels (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (Q : CyclicQuotient k L m D) :
    let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k L V
    ∃ (P : Models.Presentation k L hL) (i : Fin L) (a : kˣ)
      (F : Models.Factorization P m i a)
      (Gt : Law (LaurentSeries k) F.equation)
      (hGt : IsOriginLaw (LaurentSeries k) F.equation Gt)
      (Ct : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring Q.target
        (LaurentSeries k) F.equation Gt),
      KernelCoordinates k L m D V i a ∧
      F.d = L/L.gcd i.val ∧ F.e = m/(L/L.gcd i.val) ∧
      F.t = m/(L/L.gcd i.val)*L.gcd i.val ∧ L/L.gcd i.val ∣ m ∧
      Ct.scalar = Cs.scalar ∧ V.map ≫ Q.arrow.map = F.map ≫ Ct.map := by
  dsimp only
  have hb := level_bounds L m hL hm hdiv
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := V.level.elliptic
  let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k L V
  let PC := levelCyclic k L hL D m hm hb.2.2.1
  obtain ⟨P⟩ := Models.presentation_exists k L hL hb.1 hb.2.1
  obtain ⟨i, a, F, hpoint, hcoords, hd, he, ht, hdm⟩ :=
    labeled_factorization k L m hL hm hmeven hdiv D V P
  letI := TateFullLevelMarking.elliptic k F.t F.target.three_le F.target.even
  letI : F.equation.IsElliptic := by unfold Models.Factorization.equation; infer_instance
  obtain ⟨H, hH⟩ := CoefficientMap.origin_law_exists (TateCurve k F.t)
    (Models.cubicLaw F.target) (Models.cubicLaw_origin F.target) (laurentRescale k F.beta).toRingHom
  let f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap
      (LaurentSeries k) (TateCurve k L) F.equation := ⟨F.map, F.map_over, F.origin⟩
  have hg := F.geometry
  letI : IsFinite f.map := hg.1
  letI : Etale f.map := hg.2.1
  letI : Surjective f.map := hg.2.2.1
  have hkill : (testCyclic Cs PC).point ≫ f.map = origin (LaurentSeries k) F.equation := by
    rw [test_kernel_eq k L m hL hm hb.2.2.1 D V, ← hpoint]
    exact F.kills
  obtain ⟨E, hE, hEover, hEzero⟩ := CyclicKernel.compare D.atlas.descent.family m PC Q
    (TateCurve k L) F.equation V.level.law V.level.originLaw H hH Cs f hg.2.2.2 hkill
  obtain ⟨Gt, hGt, Ct, hscalar, hmap⟩ := TargetTest.of_iso_over Q.target
    (baseMap D.atlas.quotient.ring (LaurentSeries k) Cs.scalar) Cs.scalar rfl
    F.equation E hEover hEzero
  refine ⟨P, i, a, F, Gt, hGt, Ct, hcoords, hd, he, ht, hdm, hscalar, ?_⟩
  change Cs.map ≫ Q.arrow.map = f.map ≫ Ct.map
  rw [hmap, ← hE, Category.assoc, Iso.hom_inv_id_assoc]
  exact (baseChangeArrow_fst _ _ _ _ _ _ _).symm

end ActualKernel

section AlphaTransport
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Any actual family alpha has the calculated order on a pure Tate test;
the marking is the canonical Cartesian lift of the supplied full-four marking. -/
lemma pure_alpha_orders (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h4 : 4 ∣ r) [(TateCurve k r).IsElliptic]
    {S : Type} [CommRing S] (E : EllipticFamily S) (M : FamilyLevel S E 4)
    (a : Γ(hodge E, ⊤)) (ha : IsFamilyAlpha S E M a)
    (G : Law (LaurentSeries k) (TateCurve k r))
    (hG : IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k) (TateCurve k r) G)
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k r)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = r/4) ∧
      alphaPull C ⊤ ⊤ (by simp) a = scalar (LaurentSeries k)
        (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k r δ := by
  letI : Algebra ℚ (LaurentSeries k) := HahnSeries.powerSeriesAlgebra ℤ k
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h := ha.2 (LaurentSeries k) (TateCurve k r) G hG C (liftMarking G hG C M)
    (liftMarkPoint_map G C M.x) (liftMarkPoint_map G C M.y)
  have h' : RealizesAlpha (LaurentSeries k) (TateCurve k r) G 4 (liftMarking G hG C M)
      (alphaPull C ⊤ ⊤ (by simp) a) := by
    simpa only [alphaPull, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
      Scheme.Hom.preimage_top, InitialHodgeSection.res_self] using h
  exact four_marking_orders k r hr h4 G (liftMarking G hG C M) δ hδ _ h'

lemma constant_rescale_factor (k : Type) [Field k] (β : kˣ) (c : k) (hc : c ≠ 0)
    (j : ℕ) (v : (PowerSeries k)ˣ) :
    ∃ u : (PowerSeries k)ˣ,
      HahnSeries.C c * laurentRescale k β
        (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (u : PowerSeries k)) := by
  let w : (PowerSeries k)ˣ := Units.map (powerRescale k β).toMonoidHom v
  let z : kˣ := Units.mk0 (c*(β : k)^j) (mul_ne_zero hc (pow_ne_zero _ β.ne_zero))
  let u : (PowerSeries k)ˣ := Units.map PowerSeries.C.toMonoidHom z * w
  refine ⟨u, ?_⟩
  rw [laurentRescale_powerSeries]
  have hpoly : PowerSeries.C c * powerRescale k β (PowerSeries.X^j * (v : PowerSeries k)) =
      PowerSeries.X^j * (u : PowerSeries k) := by
    change PowerSeries.C c * PowerSeries.rescale (β : k) _ = _
    rw [map_mul, map_pow, PowerSeries.rescale_X, mul_pow]
    change PowerSeries.C c * (PowerSeries.C (β : k)^j * PowerSeries.X^j *
      PowerSeries.rescale (β : k) (v : PowerSeries k)) =
      PowerSeries.X^j * (PowerSeries.C (c*(β : k)^j) * PowerSeries.rescale (β : k) (v : PowerSeries k))
    rw [map_mul, map_pow]
    ring
  have h := congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hpoly
  rw [map_mul] at h
  simpa only [algebraMap, HahnSeries.ofPowerSeries_C] using h

lemma transport_top_eq {X Y : Scheme} (b : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (E : (Scheme.Modules.pullback b).obj M ≅ N) (s : Γ(M, ⊤)) :
    transportSection b M N E s = E.hom.app ⊤ (pullbackGlobalSection b M s) := by
  simp only [transportSection, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top, InitialHodgeSection.res_self]

lemma transport_change_map {X Y : Scheme} (p q : X ⟶ Y) (h : p = q)
    (M : Y.Modules) (N : X.Modules) (E : (Scheme.Modules.pullback q).obj M ≅ N)
    (s : Γ(M, ⊤)) :
    transportSection p M N (pullbackEqIso h M ≪≫ E) s = transportSection q M N E s := by
  subst q
  rfl

lemma test_alpha_eq (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    testAlpha k L m D A V =
      alphaPull (affineTest k L V) ⊤ ⊤ (by simp) (ambientAlpha k L m D A) := by
  have h := transport_change_map _ _ (Spec.map_preimage (V.base ≫ D.quotient.inclusion)).symm
    (hodge D.atlas.descent.family) _ (comparison (affineTest k L V)) (ambientAlpha k L m D A)
  rw [transport_top_eq] at h
  exact h
lemma alphaPull_scalar {S K : Type} [CommRing S] [Field K]
    {E : EllipticFamily S} {W : WeierstrassCurve K} {G : Law K W}
    (C : Test S E K W G) (c : S) (a : Γ(hodge E, ⊤)) :
    alphaPull C ⊤ ⊤ (by simp) (scalar S c • a) =
      scalar K (C.scalar c) • alphaPull C ⊤ ⊤ (by simp) a := by
  have h := transportSection_smul (baseMap S K C.scalar) (hodge E) (Hodge K W)
    (comparison C) (scalar S c) a
  rw [NormalizedSection.base_scalar] at h
  exact h

lemma cubic_apply_scalar {K : Type} [Field K] (W Wt : WeierstrassCurve K)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) (c : K) (a : Γ(Hodge K Wt, ⊤)) :
    cubicHodgeApply W Wt ψ hψ hψo (scalar K c • a) =
      scalar K c • cubicHodgeApply W Wt ψ hψ hψo a := by
  unfold cubicHodgeApply
  rw [Scheme.Modules.Hom.app_smul]

lemma normalize_scalar {K : Type} [Field K] (W : WeierstrassCurve K)
    (m e : ℕ) (f : K) (ω : Γ(Hodge K W, ⊤)) :
    scalar K (m : K)⁻¹ • (scalar K f • (scalar K (e : K) • ω)) =
      scalar K ((m : K)⁻¹ * (e : K) * f) • ω := by
  rw [smul_smul, smul_smul]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv _ *
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv _ *
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv _ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv _
  rw [← map_mul, ← map_mul]
  congr 1
  ring

lemma alpha_refinement_transport {S R T : Type} [CommRing S] [CommRing R] [IsDomain R]
    [CommRing T] [IsDomain T] {E : EllipticFamily S}
    {W : WeierstrassCurve R} [W.IsElliptic] {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt}
    (C : Test S E R W G) (D : Test S E T Wt Gt)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G T Wt Gt ρ b)
    (hm : b ≫ C.map = D.map)
    (hbase : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar)
    (a : Γ(hodge E, ⊤)) :
    alphaPull D ⊤ ⊤ (by simp) a =
      transportSection (baseMap R T ρ) (Hodge R W) (Hodge T Wt)
        (hodgeIso R W G T Wt Gt ρ b hb) (alphaPull C ⊤ ⊤ (by simp) a) := by
  exact alphaPull_refinement C D ρ b hb hm hbase ⊤ ⊤ ⊤ (by simp) (by simp) (by simp) a

lemma coefficient_hodge_eq {K : Type} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (e : K ≃+* K) (G : Law K W) (H : Law K (W.map e.toRingHom))
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange K W G K (W.map e.toRingHom) H
      e.toRingHom (CoefficientMap.map W e.toRingHom)) :
    hodgeIso K W G K (W.map e.toRingHom) H e.toRingHom (CoefficientMap.map W e.toRingHom) hb =
      CoefficientMap.hodgeComparison W e := rfl

lemma coefficient_alpha_refinement {K : Type} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] (e : K ≃+* K)
    {S : Type} [CommRing S] {E : EllipticFamily S}
    (G : Law K W) (hG : IsOriginLaw K W G)
    (H : Law K (W.map e.toRingHom)) (hH : IsOriginLaw K (W.map e.toRingHom) H)
    (C : Test S E K (W.map e.toRingHom) H) (a : Γ(hodge E, ⊤)) :
    alphaPull C ⊤ ⊤ (by simp) a = CoefficientMap.transport W e
      (alphaPull (CoefficientMap.inverseTest W e G hG H hH C) ⊤ ⊤ (by simp) a) := by
  let C₀ := CoefficientMap.inverseTest W e G hG H hH C
  let b := CoefficientMap.map W e.toRingHom
  letI := CoefficientMap.map_isIso W e
  have hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      K W G K (W.map e.toRingHom) H e.toRingHom b :=
    ⟨CoefficientMap.cartesian W e.toRingHom, CoefficientMap.origin_map W e.toRingHom,
      CoefficientMap.multiplication_of_cartesian W (W.map e.toRingHom) G hG H hH
        e.toRingHom b (CoefficientMap.cartesian W e.toRingHom) (CoefficientMap.origin_map W e.toRingHom)⟩
  have hm : b ≫ C₀.map = C.map := by
    dsimp only [C₀, CoefficientMap.inverseTest, b]
    rw [IsIso.hom_inv_id_assoc]
  have hs : baseMap S K C.scalar = baseMap K K e.toRingHom ≫ baseMap S K C₀.scalar := by
    unfold baseMap
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (e.apply_symm_apply (C.scalar x)).symm
  have ht := alpha_refinement_transport C₀ C e.toRingHom b hb hm hs a
  rw [coefficient_hodge_eq W e G H hb] at ht
  exact ht


lemma coefficient_alpha_orders (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h4 : 4 ∣ r) [(TateCurve k r).IsElliptic] (β : kˣ)
    {S : Type} [CommRing S] (E : EllipticFamily S) (M : FamilyLevel S E 4)
    (a : Γ(hodge E, ⊤)) (ha : IsFamilyAlpha S E M a)
    (G : Law (LaurentSeries k) (TateCurve k r))
    (hG : IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (H : Law (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom))
    (hH : IsOriginLaw (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k r)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = r/4) ∧
      alphaPull C ⊤ ⊤ (by simp) a = scalar (LaurentSeries k)
        (laurentRescale k β (algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.X^j * (v : PowerSeries k)))) •
        CoefficientMap.transport (TateCurve k r) (laurentRescale k β)
          (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k r δ) := by
  let e := laurentRescale k β
  let C₀ := CoefficientMap.inverseTest (TateCurve k r) e G hG H hH C
  obtain ⟨v, j, hj, hv⟩ := pure_alpha_orders k r hr h4 E M a ha G hG C₀ δ hδ
  refine ⟨v, j, hj, ?_⟩
  rw [coefficient_alpha_refinement (TateCurve k r) e G hG H hH C a]
  rw [hv]
  unfold CoefficientMap.transport
  rw [transportSection_smul, NormalizedSection.base_scalar]
  rfl


lemma hodge_pullback_test {S : Type} [CommRing S]
    (E T : EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] (W Wt : WeierstrassCurve K)
    (G : Law K W) (Gt : Law K Wt)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt)
    (hscalar : Ct.scalar = Cs.scalar)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) (hψmap : Cs.map ≫ f.map = ψ ≫ Ct.map)
    (a : Γ(hodge T, ⊤)) :
    alphaPull Cs ⊤ ⊤ (by simp) ((familyHodgeMap f).app ⊤ a) =
      cubicHodgeApply W Wt ψ hψ hψo (alphaPull Ct ⊤ ⊤ (by simp) a) := by
  rcases Cs with ⟨ρ, u, hu, huo, hun⟩
  rcases Ct with ⟨ρt, v, hv, hvo, hvn⟩
  dsimp only [ArithmeticThetaOpenHodgeR0180.Test.scalar] at hscalar
  subst ρt
  letI : Algebra S K := ρ.toAlgebra
  letI := E.smooth
  letI := T.smooth
  let Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G := ⟨ρ, u, hu, huo, hun⟩
  let Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt := ⟨ρ, v, hv, hvo, hvn⟩
  have hcomm : (Scheme.Modules.pullback (baseMap S K ρ)).map
      (familyHodgeMap f) ≫ (comparison Cs).hom =
      (comparison Ct).hom ≫ cubicHodgeMap W Wt ψ hψ hψo := by
    have hn := PeriodDifferential.pointMap_baseChange_naturality (A := S) (B := K)
      E.projection T.projection (structureMap K W) (structureMap K Wt)
      u v hu hv (zero E) (zero T) (origin K W) (origin K Wt) huo hvo
      f.map f.over_eq f.zero_eq ψ hψ hψo hψmap
    dsimp only [comparison, familyHodgeMap, cubicHodgeMap, PeriodDifferential.pointMap, Cs, Ct] at hn ⊢
    exact hn
  have ht := HodgeTransport.square_section (baseMap S K ρ) _ _ _ _
    (familyHodgeMap f) (cubicHodgeMap W Wt ψ hψ hψo) (comparison Ct) (comparison Cs) hcomm a
  dsimp only [Cs, Ct, Base, Hodge, alphaPull, transportSection, cubicHodgeApply, cubicHodgeMap] at ht ⊢
  with_reducible exact ht


end AlphaTransport

end IsogenyAlphaAllCuspOrders
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback ArithmeticThetaTensorPower
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality
open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open IsogenyAlphaAllCuspOrders

theorem isogeny_alpha_all_cusp_orders :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ),
      0 < L → 0 < m → Even m → 8*m ∣ L →
      ∀ (D : LevelData k L), ∀ A : OpenAlpha k L m D, AllCuspOrders k L m D A := by
  intro k _ _ _ L m hL hm hmeven hdiv D A V
  obtain ⟨P, i, z, F, H, hH, C, hcoords, hd, he, ht, hdm, hscalar, hmap⟩ :=
    comparison_with_labels k L m hL hm hmeven hdiv D V A.quotient
  letI := TateFullLevelMarking.elliptic k F.t F.target.three_le F.target.even
  obtain ⟨δ, hδ⟩ := CubicComparison.normalized_tate_frame k F.t F.target.three_le F.target.even
  have har := order_arithmetic L m hL hm hdiv i hdm
  have ht8 : 8 ∣ F.t := by rw [ht]; exact har.2.2.2.1
  have ht4 : 4 ∣ F.t := dvd_trans (by decide : 4 ∣ 8) ht8
  obtain ⟨v, j, hj, hv⟩ := coefficient_alpha_orders k F.t F.positive_t ht4 F.beta
    A.quotient.target A.marking A.alpha A.intrinsic (Models.cubicLaw F.target)
    (Models.cubicLaw_origin F.target) H hH C δ hδ
  have hallowed : AllowedOrder L m i j := allowed_order_of_target L m hL hm hdiv i hdm j
    (by simpa only [ht] using hj)
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he0 : (F.e : k) ≠ 0 := Nat.cast_ne_zero.mpr F.positive_e.ne'
  obtain ⟨u, hu⟩ := constant_rescale_factor k F.beta ((m : k)⁻¹*(F.e : k))
    (mul_ne_zero (inv_ne_zero hm0) he0) j v
  have hconst : (HahnSeries.C ((m : k)⁻¹*(F.e : k)) : LaurentSeries k) =
      (m : LaurentSeries k)⁻¹*(F.e : LaurentSeries k) := by
    rw [map_mul, map_inv₀, map_natCast, map_natCast]
  rw [hconst] at hu
  refine ⟨i, z, j, u, hcoords, hallowed, ?_⟩
  rw [test_alpha_eq, ambientAlpha, alphaPull_scalar]
  let Cs := affineTest k L V
  have hsc : Cs.scalar (algebraMap k D.atlas.quotient.ring (m : k)⁻¹) =
      (m : LaurentSeries k)⁻¹ := by
    exact (map_inv₀ (Cs.scalar.comp (algebraMap k D.atlas.quotient.ring)) (m : k)).trans
      (congrArg Inv.inv (by simp))
  rw [hsc]
  have hp := hodge_pullback_test D.atlas.descent.family A.quotient.target A.quotient.arrow
    (LaurentSeries k) (TateCurve k L) F.equation V.level.law H Cs C hscalar
    F.map F.map_over F.origin hmap A.alpha
  rw [hp, hv, cubic_apply_scalar]
  have hw := F.weight V.differential V.normalized δ hδ
  rw [hw, normalize_scalar, hu]

end ArithmeticThetaIsogenyHalfLinesR0193

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.allowed_order_of_target
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.four_marking_orders

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.comparison_with_labels
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.pure_alpha_orders
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.constant_rescale_factor
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.IsogenyAlphaAllCuspOrders.test_alpha_eq

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.isogeny_alpha_all_cusp_orders
