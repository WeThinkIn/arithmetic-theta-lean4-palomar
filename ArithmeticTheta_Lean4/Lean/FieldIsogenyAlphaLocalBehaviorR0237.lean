import IsogenyAlphaDesignatedExpansionR0193
import IsogenyAlphaAllCuspOrdersR0193
import TateMarkingConstantTransferR0235
import TateHodgeGeneratorTransferR0235
import TateCoordinateConstantMapR0235
import Mathlib.FieldTheory.Galois.Infinite

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaArithmeticHalfLinesR0237
namespace FieldIsogenyAlphaLocalBehavior
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaIsogenyHalfLinesR0193

set_option backward.isDefEq.respectTransparency true in
/-- Complete signed designated expansion of the same normalized section. -/
theorem field_designated_expansion :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L),
    ∀ A : OpenAlpha k L m D, DesignatedExpansion k L m D A := by
  intro k _ _ L m hL hm _ hdiv D A V ζ hζ hcan
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨C⟩ := DesignatedExpansionProof.tate_comparison k L m hL hm hdiv D A.quotient V ζ hζ hcan
  have ha := DesignatedExpansionProof.comparison_alpha k L m hL hm hdiv D A V ζ hζ C
  let Cs := DesignatedExpansionProof.sourceTest k L D V
  have hv : Cs.scalar (algebraMap k D.atlas.quotient.ring (m : k)⁻¹) =
      (m : LaurentSeries k)⁻¹ := by
    change (Cs.scalar.comp (algebraMap k D.atlas.quotient.ring)) ((m : k)⁻¹) = _
    rw [map_inv₀, map_natCast]
  have h0 := DesignatedExpansionProof.normalized_test_formula
    (S := D.atlas.quotient.ring) D.atlas.descent.family A.quotient.target A.quotient.arrow (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k L)
    (ArithmeticThetaTateCuspsR0181.TateCurve k (L*m)) V.level.law C.law Cs C.test
    C.scalar_eq C.map C.over_eq C.zero_eq C.square
  have h1 := h0 A.alpha
    (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k (L*m) C.differential)
    (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential)
    m hm (algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m)^2))
    (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)
  have h2 := h1 hv
  have h3 := h2 ha
  have hw := C.weight
  -- Align the field-derived and direct Hahn-series ring instances without unfolding curves.
  have h := h3 (by with_reducible_and_instances exact hw)
  change (ArithmeticThetaBoundaryHodgeR0182.testIso k L V).hom.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (V.base ≫ D.quotient.inclusion)
      (ArithmeticThetaOpenHodgeR0180.hodge D.atlas.descent.family) (ambientAlpha k L m D A)) = _
  rw [DesignatedExpansionProof.source_test_transport k L D V (ambientAlpha k L m D A)]
  exact h


/-- Literal coefficient extension, used to identify the accepted completion map. -/
def coefficientHom {k l : Type} [Field k] [Field l] (ι : k →+* l) :
    LaurentSeries k →+* LaurentSeries l where
  toFun f := f.map ι
  map_zero' := HahnSeries.map_zero ι.toZeroHom
  map_one' := HahnSeries.map_one ι.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add ι.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul ι.toNonUnitalRingHom

lemma coefficientHom_powerSeries {k l : Type} [Field k] [Field l]
    (ι : k →+* l) (f : PowerSeries k) :
    coefficientHom ι (algebraMap (PowerSeries k) (LaurentSeries k) f) =
      algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f) := by
  ext n
  change ι ((algebraMap (PowerSeries k) (LaurentSeries k) f).coeff n) =
    (algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f)).coeff n
  by_cases hn : n < 0
  · simp [PowerSeries.coeff_coe, hn]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hn)
    simp [LaurentSeries.coeff_coe_powerSeries]

/-- The valuation is unchanged by any injective coefficient-field extension. -/
lemma coefficientHom_order {k l : Type} [Field k] [Field l]
    (ι : k →+* l) (f : LaurentSeries k) :
    (coefficientHom ι f).order = f.order := by
  by_cases hf : f = 0
  · simp [hf]
  have hmf : coefficientHom ι f ≠ 0 := (map_ne_zero (coefficientHom ι)).mpr hf
  have hc : (coefficientHom ι f).coeff f.order ≠ 0 :=
    (map_ne_zero ι).mpr (HahnSeries.coeff_order_eq_zero.not.mpr hf)
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc)
  apply (HahnSeries.le_order_iff_forall hmf).mpr
  intro n hn
  change ι (f.coeff n) = 0
  rw [HahnSeries.coeff_eq_zero_of_lt_order hn, map_zero]

/-- The statement applies to the actual completion map through its defining
power-series equation, independently of the presentation of that map. -/
lemma completion_order {k l : Type} [Field k] [Field l]
    (ι : k →+* l) (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ∀ f : PowerSeries k,
      ell (algebraMap (PowerSeries k) (LaurentSeries k) f) =
        algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f))
    (f : LaurentSeries k) : (ell f).order = f.order := by
  have he : ell = coefficientHom ι := IsFractionRing.ringHom_ext
    (fun f => (hell f).trans (coefficientHom_powerSeries ι f).symm)
  rw [he, coefficientHom_order]

/-- A monomial-times-unit expansion upstairs descends with its entire unit
factor downstairs. No descent of a chosen root or of the upstairs unit is assumed. -/
lemma completion_unit_factor_descent {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ∀ f : PowerSeries k,
      ell (algebraMap (PowerSeries k) (LaurentSeries k) f) =
        algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f))
    (f : LaurentSeries k) (j : ℕ) (u : (PowerSeries l)ˣ)
    (h : ell f = algebraMap (PowerSeries l) (LaurentSeries l)
      (PowerSeries.X^j * (u : PowerSeries l))) :
    ∃ v : (PowerSeries k)ˣ,
      f = algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.X^j * (v : PowerSeries k)) := by
  have hu : PowerSeries.constantCoeff (u : PowerSeries l) ≠ 0 := by
    exact (isUnit_iff_ne_zero.mp (u.isUnit.map PowerSeries.constantCoeff))
  have ho : (ell f).order = (j : ℤ) := by
    rw [h]
    apply ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior.laurent_order_of_coeff
    · simpa only [PowerSeries.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] using hu
    · intro i hi
      simp [PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hi]
  have hfn : f ≠ 0 := by
    intro hz
    have he : algebraMap (PowerSeries l) (LaurentSeries l)
        (PowerSeries.X^j * (u : PowerSeries l)) = 0 := by simpa [hz] using h.symm
    have hp : PowerSeries.X^j * (u : PowerSeries l) = 0 :=
      (IsFractionRing.injective (PowerSeries l) (LaurentSeries l))
        (he.trans (map_zero (algebraMap (PowerSeries l) (LaurentSeries l))).symm)
    have hn : PowerSeries.X^j * (u : PowerSeries l) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (Units.ne_zero u)
    exact hn hp
  apply ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior.unit_factor_of_order k f hfn j
  rw [← completion_order ι ell hell f]
  exact ho

/-- The exact cyclic order is retained after extending coefficients. -/
lemma label_order_extension {k l : Type} [Field k] [Field l]
    (ι : k →+* l) (L : ℕ) (i : Fin L) (a : kˣ) :
    orderOf (Multiplicative.ofAdd (i.val : ZMod L), Units.map ι.toMonoidHom a) =
      orderOf (Multiplicative.ofAdd (i.val : ZMod L), a) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality.KernelArithmetic.label_power_eq_one,
    ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality.KernelArithmetic.label_power_eq_one]
  apply and_congr_right
  intro _
  have h : Units.map ι.toMonoidHom (a^n) = Units.map ι.toMonoidHom 1 ↔ a^n = 1 :=
    (Units.map_injective ι.injective).eq_iff
  simpa only [map_pow, map_one] using h

/-- Split the residual scalar only in the specified algebraically closed
extension; the component and toric degrees remain those of the original label. -/
lemma extended_mixed_rescaling {k l : Type} [Field k] [Field l] [IsAlgClosed l]
    (ι : k →+* l) (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (i : Fin L) (a : kˣ)
    (ho : orderOf (Multiplicative.ofAdd (i.val : ZMod L), a) = m) :
    let d := L / L.gcd i.val
    let e := m / d
    0 < d ∧ 0 < e ∧ d ∣ m ∧ e*d = m ∧
      IsPrimitiveRoot (ι (a : k)^d) e ∧
      ∃ β : lˣ, (β : l)^(e*L) = 1 ∧ (β : l)^(e*i.val) = ι (a : k)^e := by
  have h := ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality.KernelArithmetic.mixed_rescaling
    l L m hL hm i (Units.map ι.toMonoidHom a)
    ((label_order_extension ι L i a).trans ho)
  exact h


set_option backward.isDefEq.respectTransparency false

section OriginalFamilyTest
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality
open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open IsogenyAlphaAllCuspOrders
open QuotientComparison Models

/-- Compare a mixed Tate quotient with the given quotient of the original
family. The family ring is independent of the coefficient field of the test. -/
lemma original_family_comparison (k : Type) [Field k] [CharZero k]
    {S : Type} [CommRing S] (E : EllipticFamily S) (L m : ℕ) (hL : 0 < L)
    (PC : Cyclic E m) (Q : Quotient S E m PC.point)
    (G : Law (LaurentSeries k) (TateCurve k L))
    (hG : IsOriginLaw (LaurentSeries k) (TateCurve k L) G)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k) (TateCurve k L) G)
    (P : Models.Presentation k L hL) (i : Fin L) (a : kˣ)
    (F : Models.Factorization P m i a)
    (hpoint : Models.point P i a = (testCyclic Cs PC).point) :
    ∃ (Gt : Law (LaurentSeries k) F.equation)
      (hGt : IsOriginLaw (LaurentSeries k) F.equation Gt)
      (Ct : ArithmeticThetaOpenHodgeR0180.Test S Q.target (LaurentSeries k) F.equation Gt),
      Ct.scalar = Cs.scalar ∧ Cs.map ≫ Q.arrow.map = F.map ≫ Ct.map := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := TateFullLevelMarking.elliptic k L P.three_le P.even
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
    rw [← hpoint]
    exact F.kills
  obtain ⟨e, he, heover, hezero⟩ := CyclicKernel.compare E m PC Q
    (TateCurve k L) F.equation G hG H hH Cs f hg.2.2.2 hkill
  obtain ⟨Gt, hGt, Ct, hscalar, hmap⟩ := TargetTest.of_iso_over Q.target
    (baseMap S (LaurentSeries k) Cs.scalar) Cs.scalar rfl
    F.equation e heover hezero
  refine ⟨Gt, hGt, Ct, hscalar, ?_⟩
  change Cs.map ≫ Q.arrow.map = f.map ≫ Ct.map
  rw [hmap, ← he, Category.assoc, Iso.hom_inv_id_assoc]
  exact (baseChangeArrow_fst _ _ _ _ _ _ _).symm

/-- The complete local factor of the original normalized alpha is calculated
on a split mixed-quotient test, retaining its original family and section. -/
lemma original_family_alpha_orders (k : Type) [Field k] [CharZero k]
    {S : Type} [CommRing S] (E : EllipticFamily S) (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (PC : Cyclic E m) (Q : Quotient S E m PC.point)
    (M : FamilyLevel S Q.target 4) (α : Γ(hodge Q.target, ⊤))
    (hα : IsFamilyAlpha S Q.target M α)
    (G : Law (LaurentSeries k) (TateCurve k L))
    (hG : IsOriginLaw (LaurentSeries k) (TateCurve k L) G)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k) (TateCurve k L) G)
    (P : Models.Presentation k L hL) (i : Fin L) (a : kˣ)
    (F : Models.Factorization P m i a)
    (hpoint : Models.point P i a = (testCyclic Cs PC).point) (h4 : 4 ∣ F.t)
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ)
    (c : S) (hc : Cs.scalar c = (m : LaurentSeries k)⁻¹) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = F.t/4) ∧
      alphaPull Cs ⊤ ⊤ (by simp) (scalar S c • (familyHodgeMap Q.arrow).app ⊤ α) =
        scalar (LaurentSeries k)
          (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ := by
  obtain ⟨H, hH, C, hscalar, hmap⟩ := original_family_comparison k E L m hL PC Q G hG Cs P i a F hpoint
  letI := TateFullLevelMarking.elliptic k F.t F.target.three_le F.target.even
  obtain ⟨ε, hε⟩ := CubicComparison.normalized_tate_frame k F.t F.target.three_le F.target.even
  obtain ⟨v, j, hj, hv⟩ := coefficient_alpha_orders k F.t F.positive_t h4 F.beta
    Q.target M α hα (Models.cubicLaw F.target) (Models.cubicLaw_origin F.target) H hH C ε hε
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he0 : (F.e : k) ≠ 0 := Nat.cast_ne_zero.mpr F.positive_e.ne'
  obtain ⟨u, hu⟩ := constant_rescale_factor k F.beta ((m : k)⁻¹*(F.e : k))
    (mul_ne_zero (inv_ne_zero hm0) he0) j v
  have hconst : (HahnSeries.C ((m : k)⁻¹*(F.e : k)) : LaurentSeries k) =
      (m : LaurentSeries k)⁻¹*(F.e : LaurentSeries k) := by
    rw [map_mul, map_inv₀, map_natCast, map_natCast]
  rw [hconst] at hu
  refine ⟨u, j, hj, ?_⟩
  rw [alphaPull_scalar, hc]
  have hp := hodge_pullback_test E Q.target Q.arrow (LaurentSeries k)
    (TateCurve k L) F.equation G H Cs C hscalar F.map F.map_over F.origin hmap α
  rw [hp, hv, cubic_apply_scalar]
  have hw := F.weight δ hδ ε hε
  rw [hw, normalize_scalar, hu]


/-- The actual model comparison is faithful on both marked-section labels. -/
lemma model_point_labels_injective (k : Type) [Field k] [CharZero k]
    (L : ℕ) (hL : 0 < L) (P : Models.Presentation k L hL)
    (i j : Fin L) (a b : kˣ) (h : Models.point P i a = Models.point P j b) :
    i = j ∧ a = b := by
  open ArithmeticThetaMarkedGroupLawR0146 in
  apply MarkedExactTorsion.labels_eq k P.model P.isModel
    (MarkedPointAddition.sectionAt k P.three_le P.model P.isModel i a)
    (MarkedPointAddition.sectionAt k P.three_le P.model P.isModel j b)
    (MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel i a)
    (MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel j b)
  apply Subtype.ext
  exact (cancel_mono P.cubic.hom).mp h

/-- Both literal coordinates, including the derivative coordinate, determine
an individual nonidentity scalar label. -/
lemma literal_parameter_injective (k : Type) [Field k] [CharZero k]
    (L : ℕ) (hL : 0 < L) (P : Models.Presentation k L hL)
    (i : Fin L) (a b : kˣ)
    (ha : i.val ≠ 0 ∨ (a : k) ≠ 1) (hb : i.val ≠ 0 ∨ (b : k) ≠ 1)
    (hx : algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L i.val a) =
      algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L i.val b))
    (hy : algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L i.val a) =
      algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L i.val b)) :
    a = b := by
  have hp := Models.point_coordinates P i a ha
  rw [hx, hy] at hp
  have he := Models.point_eq_of_coordinates P (Models.cubicLaw P)
    (Models.cubicLaw_origin P) i b hb (Models.point P i a) hp
  exact (model_point_labels_injective k L hL P i i a b he).2

/-- A scalar label whose two actual Tate coordinates are defined over the
coefficient field descends through a Galois extension. -/
lemma literal_parameter_descent (k l : Type) [Field k] [CharZero k]
    [Field l] [CharZero l] [Algebra k l] [IsGalois k l]
    (L : ℕ) (hL : 0 < L) (P : Models.Presentation l L hL)
    (i : Fin L) (a : lˣ) (ha : i.val ≠ 0 ∨ (a : l) ≠ 1)
    (x y : LaurentSeries k)
    (hx : coefficientHom (algebraMap k l) x =
      algebraMap (PowerSeries l) (LaurentSeries l) (ArithmeticThetaTateSeries.tateX L i.val a))
    (hy : coefficientHom (algebraMap k l) y =
      algebraMap (PowerSeries l) (LaurentSeries l) (ArithmeticThetaTateSeries.tateY L i.val a)) :
    ∃ b : kˣ, Units.map (algebraMap k l).toMonoidHom b = a := by
  have hfixed : ∀ σ : l ≃ₐ[k] l, σ (a : l) = (a : l) := by
    intro σ
    let b : lˣ := Units.map σ.toRingHom.toMonoidHom a
    have hb : i.val ≠ 0 ∨ (b : l) ≠ 1 := by
      rcases ha with hi | ha
      · exact Or.inl hi
      · right
        intro he
        apply ha
        apply σ.injective
        exact he.trans σ.map_one.symm
    have hc (f : LaurentSeries k) :
        coefficientHom σ.toRingHom (coefficientHom (algebraMap k l) f) =
          coefficientHom (algebraMap k l) f := by
      ext n
      exact σ.commutes (f.coeff n)
    have htx : algebraMap (PowerSeries l) (LaurentSeries l)
        (ArithmeticThetaTateSeries.tateX L i.val a) =
        algebraMap (PowerSeries l) (LaurentSeries l)
          (ArithmeticThetaTateSeries.tateX L i.val b) := by
      calc
        _ = coefficientHom (algebraMap k l) x := hx.symm
        _ = coefficientHom σ.toRingHom (coefficientHom (algebraMap k l) x) := (hc x).symm
        _ = _ := by
          rw [hx, coefficientHom_powerSeries,
            ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.map_tateX]
          rfl
    have hty : algebraMap (PowerSeries l) (LaurentSeries l)
        (ArithmeticThetaTateSeries.tateY L i.val a) =
        algebraMap (PowerSeries l) (LaurentSeries l)
          (ArithmeticThetaTateSeries.tateY L i.val b) := by
      calc
        _ = coefficientHom (algebraMap k l) y := hy.symm
        _ = coefficientHom σ.toRingHom (coefficientHom (algebraMap k l) y) := (hc y).symm
        _ = _ := by
          rw [hy, coefficientHom_powerSeries,
            ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.map_tateY]
          rfl
    have he := literal_parameter_injective l L hL P i a b ha hb htx hty
    exact (congrArg (fun u : lˣ => (u : l)) he).symm
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (K := l) (a : l)).mpr hfixed
  have hb0 : b ≠ 0 := by
    intro hz
    apply a.ne_zero
    rw [← hb, hz, map_zero]
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  exact hb


/-- Compose a test with the specified coefficient square, retaining its maps. -/
def refinedTest {S R T : Type} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G T Wt Gt ρ b) :
    ArithmeticThetaOpenHodgeR0180.Test S E T Wt Gt := by
  have hbase : baseMap S T (ρ.comp C.scalar) = baseMap R T ρ ≫ baseMap S R C.scalar :=
    Spec.map_comp (CommRingCat.ofHom C.scalar) (CommRingCat.ofHom ρ)
  exact {
    scalar := ρ.comp C.scalar
    map := b ≫ C.map
    cartesian := by rw [hbase]; exact hb.1.paste_horiz C.cartesian
    origin_eq := by
      rw [← Category.assoc, hb.2.1, Category.assoc, C.origin_eq, ← Category.assoc, hbase]
      rfl
    nsmul_eq := by
      intro n
      rw [← Category.assoc, hb.2.2 n, Category.assoc, C.nsmul_eq, Category.assoc] }

lemma refined_cyclic_point {S R T : Type} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {Wt : WeierstrassCurve T}
    {G : Law R W} {Gt : Law T Wt}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (ρ : R →+* T) (b : Curve T Wt ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G T Wt Gt ρ b)
    {m : ℕ} (PC : Cyclic E m) :
    (testCyclic (refinedTest C ρ b hb) PC).point ≫ b =
      baseMap R T ρ ≫ (testCyclic C PC).point := by
  let Ct := refinedTest C ρ b hb
  have hbase : baseMap S T Ct.scalar = baseMap R T ρ ≫ baseMap S R C.scalar :=
    Spec.map_comp (CommRingCat.ofHom C.scalar) (CommRingCat.ofHom ρ)
  apply C.cartesian.hom_ext
  · change ((testCyclic Ct PC).point ≫ b) ≫ C.map = _
    rw [Category.assoc]
    change (testCyclic Ct PC).point ≫ Ct.map = _
    have ht : (testCyclic Ct PC).point ≫ Ct.map = baseMap S T Ct.scalar ≫ PC.point :=
      ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180.liftSection_map Ct PC.point PC.over_eq
    have hk : (testCyclic C PC).point ≫ C.map = baseMap S R C.scalar ≫ PC.point :=
      ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180.liftSection_map C PC.point PC.over_eq
    rw [ht, Category.assoc, hk, hbase, Category.assoc]
  · change ((testCyclic Ct PC).point ≫ b) ≫ structureMap R W = _
    rw [Category.assoc, hb.1.w, ← Category.assoc, (testCyclic Ct PC).over_eq,
      Category.id_comp, Category.assoc, (testCyclic C PC).over_eq, Category.comp_id]
    rfl

lemma cyclic_point_avoids (K : Type) [Field K] (W : WeierstrassCurve K)
    (G : Law K W) (hG : IsOriginLaw K W G) (m : ℕ) (hm : 1 < m)
    (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection K W G m) :
    Disjoint (Set.range P.point) (Set.range (origin K W)) := by
  let p : NeronModelInfra.SchemeHomOver (𝟙 (Base K)) (structureMap K W) := ⟨P.point, P.over_eq⟩
  have h1 : P.point ≫ G.schemeNsmul 1 = P.point := by
    rw [ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul G (𝟙 _) p 1,
      G.nsmul_one_apply]
  have h0 : P.point ≫ G.schemeNsmul 0 = origin K W := by
    rw [ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul G (𝟙 _) p 0,
      G.nsmul_zero, hG.1, Category.id_comp]
  have hd := P.disjoint (⟨1, hm⟩ : Fin m) (⟨0, by omega⟩ : Fin m)
    (by intro h; have := congrArg Fin.val h; norm_num at this)
  simpa only [h1, h0] using hd

lemma cyclic_point_coordinates (K : Type) [Field K] (W : WeierstrassCurve K)
    (G : Law K W) (hG : IsOriginLaw K W G) (m : ℕ) (hm : 1 < m)
    (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection K W G m) :
    ∃ x y : K, ArithmeticThetaLegendreComparisonR0177.HasCoordinates K W P.point x y := by
  obtain ⟨χ, hχ⟩ := ArithmeticThetaLegendreComparisonR0177.TwoTorsionAffineCoordinates.exists_chart_factorization
    W P.point (cyclic_point_avoids K W G hG m hm P)
  exact ⟨_, _, P.over_eq, χ, hχ, rfl, rfl⟩

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange in
/-- Descend a full expansion in an explicitly transported frame. -/
lemma framed_unit_factor_descent (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ∀ f : PowerSeries k,
      ell (algebraMap (PowerSeries k) (LaurentSeries k) f) =
        algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f))
    (M : (Base (LaurentSeries k)).Modules) (N : (Base (LaurentSeries l)).Modules)
    (e : (Scheme.Modules.pullback (baseMap (LaurentSeries k) (LaurentSeries l) ell)).obj M ≅ N)
    (ω : Γ(M, ⊤)) (η : Γ(N, ⊤)) (hω : IsFrame M ⊤ ω) (hη : IsFrame N ⊤ η)
    (hgen : transportSection (baseMap (LaurentSeries k) (LaurentSeries l) ell) M N e ω = η)
    (s : Γ(M, ⊤)) (j : ℕ) (u : (PowerSeries l)ˣ)
    (hs : transportSection (baseMap (LaurentSeries k) (LaurentSeries l) ell) M N e s =
      scalar (LaurentSeries l)
        (algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.X^j * (u : PowerSeries l))) • η) :
    ∃ v : (PowerSeries k)ˣ, s = scalar (LaurentSeries k)
      (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) • ω := by
  have hω' := hω ⊤ le_rfl
  have hη' := hη ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at hω' hη'
  obtain ⟨r, hr⟩ := hω'.2 s
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).2 r
  have hcs : scalar (LaurentSeries k) c • ω = s := by
    change (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c • ω = s
    rw [hc]
    exact hr
  rw [← hcs, transportSection_smul, NormalizedSection.base_scalar, hgen] at hs
  have heq := hη'.1 hs
  have heq' : ell c = algebraMap (PowerSeries l) (LaurentSeries l)
      (PowerSeries.X^j * (u : PowerSeries l)) :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries l))).inv).1 heq
  obtain ⟨v, hv⟩ := completion_unit_factor_descent ι ell hell c j u heq'
  exact ⟨v, by rw [← hcs, hv]⟩


/-- Construct the actual cusp expansion after a Galois coefficient extension
and descend its kernel label and full scalar factor to the original field. -/
lemma cusp_orders_via_extension (k l : Type) [Field k] [CharZero k]
    [Field l] [CharZero l] [Algebra k l] [IsAlgClosed l] [IsGalois k l]
    (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (A : OpenAlpha k L m D) : AllCuspOrders k L m D A := by
  intro V
  let ι := algebraMap k l
  let ell := ArithmeticThetaBoundaryConstantsR0235.laurentMap ι
  have hell (f : PowerSeries k) :
      ell (algebraMap (PowerSeries k) (LaurentSeries k) f) =
        algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f) :=
    ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.laurent_powerSeries ι f
  have hell' : ell = coefficientHom ι := IsFractionRing.ringHom_ext
    (fun f => (hell f).trans (coefficientHom_powerSeries ι f).symm)
  have bounds := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  have hm1 : 1 < m := by obtain ⟨r, hr⟩ := hmeven; omega
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : CharZero (LaurentSeries l) := LaurentSeries.XAdic.charZero l
  letI := V.level.elliptic
  letI := TateFullLevelMarking.elliptic l L bounds.1 bounds.2.1
  let Cs := affineTest k L V
  let PC := levelCyclic k L hL D m hm bounds.2.2.1
  obtain ⟨b, hb, _⟩ := ArithmeticThetaBoundaryConstantsR0235.tate_coordinate_constant_map
    k l ι L bounds.1 bounds.2.1
  obtain ⟨H, hH, hbc⟩ := ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.law_exists
    ι L b hb V.level
  let Ct := refinedTest Cs ell b hbc
  let Ck := testCyclic Cs PC
  let Cl := testCyclic Ct PC
  obtain ⟨P⟩ := Models.presentation_exists l L hL bounds.1 bounds.2.1
  obtain ⟨i, a, hpoint, _⟩ := Models.cyclic_factorization_exists P H hH m hm
    bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.1 Cl
  have ho := ModelCoordinates.cyclic_label_order l L m hL hm P.three_le P.even
    P.tower P.model P.isModel P.zero P.markedZero P.law P.originLaw H hH
    P.cubic P.cubic_over P.cubic_zero Cl i a hpoint
  obtain ⟨F, hd, he, ht, hdm⟩ := exact_factorization l L m hL hm hdiv P i a ho
  have hne : i.val ≠ 0 ∨ (a : l) ≠ 1 := by
    by_contra h
    push Not at h
    have hi : (i.val : ZMod L) = 0 := by rw [h.1]; simp
    have ha : a = 1 := Units.ext h.2
    rw [hi, ha] at ho
    have hmone : m = 1 := by
      change orderOf ((1 : Multiplicative (ZMod L)), (1 : lˣ)) = m at ho
      simpa only [Prod.orderOf, orderOf_one, Nat.lcm_self] using ho.symm
    omega
  obtain ⟨x, y, hxy⟩ := cyclic_point_coordinates (LaurentSeries k) (TateCurve k L)
    V.level.law V.level.originLaw m hm1 Ck
  have hpull := refined_cyclic_point Cs ell b hbc PC
  have hxy' := ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.coordinates_transfer
    ι L b hb Ck.point Cl.point Cl.over_eq
    (cyclic_point_avoids (LaurentSeries l) (TateCurve l L) H hH m hm1 Cl)
    hpull x y hxy
  have hcoords := Models.point_coordinates P i a hne
  rw [hpoint] at hcoords
  have heq := ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior.coordinates_unique
    (TateCurve l L) Cl.point _ _ _ _ hxy' hcoords
  have hx : coefficientHom ι x = algebraMap (PowerSeries l) (LaurentSeries l)
      (ArithmeticThetaTateSeries.tateX L i.val a) := by rw [← hell']; exact heq.1
  have hy : coefficientHom ι y = algebraMap (PowerSeries l) (LaurentSeries l)
      (ArithmeticThetaTateSeries.tateY L i.val a) := by rw [← hell']; exact heq.2
  obtain ⟨z, hz⟩ := literal_parameter_descent k l L hL P i a hne x y hx hy
  have hzv : ι (z : k) = (a : l) := congrArg (fun u : lˣ => (u : l)) hz
  have hnz : i.val ≠ 0 ∨ (z : k) ≠ 1 := by
    rcases hne with hi | ha
    · exact Or.inl hi
    · right
      intro hz1
      apply ha
      rw [← hzv, hz1, map_one]
  have hxdown : x = algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateX L i.val z) := by
    apply ell.injective
    rw [hell, ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.map_tateX, hzv]
    exact heq.1
  have hydown : y = algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateY L i.val z) := by
    apply ell.injective
    rw [hell, ArithmeticThetaBoundaryConstantsR0235.TateMarkingConstantTransfer.map_tateY, hzv]
    exact heq.2
  have hkernel : KernelCoordinates k L m D V i z := by
    refine ⟨hnz, ?_⟩
    rw [← test_kernel_eq k L m hL hm bounds.2.2.1 D V, ← hxdown, ← hydown]
    exact hxy
  obtain ⟨δ, hδ⟩ := CubicComparison.normalized_tate_frame l L bounds.1 bounds.2.1
  have har := order_arithmetic L m hL hm hdiv i hdm
  have ht8 : 8 ∣ F.t := by rw [ht]; exact har.2.2.2.1
  have ht4 : 4 ∣ F.t := dvd_trans (by decide : 4 ∣ 8) ht8
  let c := algebraMap k D.atlas.quotient.ring (m : k)⁻¹
  have hc : Ct.scalar c = (m : LaurentSeries l)⁻¹ := by
    change (Ct.scalar.comp (algebraMap k D.atlas.quotient.ring)) ((m : k)⁻¹) = _
    rw [map_inv₀, map_natCast]
  obtain ⟨u, j, hj, hu⟩ := original_family_alpha_orders l D.atlas.descent.family L m hL hm
    PC A.quotient A.marking A.alpha A.intrinsic H hH Ct P i a F hpoint ht4 δ hδ c hc
  have hallowed : AllowedOrder L m i j := allowed_order_of_target L m hL hm hdiv i hdm j
    (by simpa only [ht] using hj)
  let e := ArithmeticThetaBoundaryConstantsR0235.tateHodgeIso ι V.level b hb
  have heiso : ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.hodgeIso
      (LaurentSeries k) (TateCurve k L) V.level.law
      (LaurentSeries l) (TateCurve l L) H ell b hbc = e := rfl
  have hbase : baseMap D.atlas.quotient.ring (LaurentSeries l) Ct.scalar =
      baseMap (LaurentSeries k) (LaurentSeries l) ell ≫
        baseMap D.atlas.quotient.ring (LaurentSeries k) Cs.scalar :=
    Spec.map_comp (CommRingCat.ofHom Cs.scalar) (CommRingCat.ofHom ell)
  have href := alpha_refinement_transport Cs Ct ell b hbc rfl hbase (ambientAlpha k L m D A)
  rw [heiso] at href
  have hgen : transportSection (baseMap (LaurentSeries k) (LaurentSeries l) ell) _ _ e
      (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L V.differential) =
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator l L δ :=
    ArithmeticThetaBoundaryConstantsR0235.tate_hodge_generator_transfer k l ι L
      bounds.1 bounds.2.1 V.level b hb V.differential δ V.normalized hδ
  have hs : transportSection (baseMap (LaurentSeries k) (LaurentSeries l) ell) _ _ e
      (alphaPull Cs ⊤ ⊤ (by simp) (ambientAlpha k L m D A)) =
      scalar (LaurentSeries l) (algebraMap (PowerSeries l) (LaurentSeries l)
        (PowerSeries.X^j * (u : PowerSeries l))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator l L δ := href.symm.trans hu
  obtain ⟨v, hv⟩ := framed_unit_factor_descent k l ι ell hell _ _ e _ _
    (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.hodgeGenerator_frame k L V.differential)
    (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.hodgeGenerator_frame l L δ)
    hgen _ j u hs
  refine ⟨i, z, j, v, hkernel, hallowed, ?_⟩
  rw [test_alpha_eq]
  exact hv

end OriginalFamilyTest

end FieldIsogenyAlphaLocalBehavior

/-- Full arithmetic local behavior, in the original coefficient field and frame. -/
theorem field_isogeny_alpha_local_behavior :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ),
      0 < L → 0 < m → Even m → 8*m ∣ L →
      ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L),
      ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D,
        ArithmeticThetaIsogenyHalfLinesR0193.AllCuspOrders k L m D A ∧
        ArithmeticThetaIsogenyHalfLinesR0193.DesignatedExpansion k L m D A := by
  intro k _ _ L m hL hm hmeven hdiv D A
  constructor
  · exact FieldIsogenyAlphaLocalBehavior.cusp_orders_via_extension k (AlgebraicClosure k)
      L m hL hm hmeven hdiv D A
  · exact FieldIsogenyAlphaLocalBehavior.field_designated_expansion k L m hL hm hmeven hdiv D A

end ArithmeticThetaArithmeticHalfLinesR0237

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.field_designated_expansion

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.completion_unit_factor_descent
#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.extended_mixed_rescaling

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.original_family_comparison
#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.original_family_alpha_orders

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.literal_parameter_descent

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.refined_cyclic_point
#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.cyclic_point_coordinates
#print axioms ArithmeticThetaArithmeticHalfLinesR0237.FieldIsogenyAlphaLocalBehavior.framed_unit_factor_descent

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.field_isogeny_alpha_local_behavior
