import DistinctNormSharpArithmeticR0195
import RatioUnaryRegularSectionsR0195
import LegendreLevelFamilyConstructionR0176

/-! The norm-only sharp cover and actual matrix theta sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSharpKernelR0195
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections

namespace SharpMatrixGeometricFamily

lemma theta_coeff_card (k : Type) [Field k] (n : ℕ) :
    PowerSeries.coeff n (ArithmeticThetaTateSeries.theta k) =
      (Nat.card {z : ℤ // z^2 = (n : ℤ)} : k) := by
  classical
  let s := (Finset.Icc (-(n : ℤ)) ((n : ℤ)+1)).filter (fun z => z^2 = (n : ℤ))
  let e : {z : ℤ // z^2 = (n : ℤ)} ≃ ↥s :=
    { toFun := fun z => ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by
        have hz := z.2
        constructor <;> nlinarith [sq_nonneg (z.1+1), sq_nonneg (z.1-1)]), z.2⟩⟩
      invFun := fun z => ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := ArithmeticThetaTateIdentities.integer_square_count n
  rw [← Finset.sum_filter] at hc
  have hc' : (s.card : ℤ) = (if n = 0 then 1 else 0) +
      2 * (((Finset.Icc 1 n).filter (fun j : ℕ => j^2 = n)).card : ℤ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hc
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcast := congrArg (Int.castRingHom k) hc'
  simpa [ArithmeticThetaTateSeries.theta, PowerSeries.coeff_mk] using hcast.symm

lemma cleared_zero (k : Type) [Field k] (m : ℕ) (hm : 0 < m) :
    PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.clearedUnaryTheta m 0) =
      PowerSeries.expand (12*m^2) (by positivity) (ArithmeticThetaTateSeries.theta k) := by
  ext b
  rw [PowerSeries.coeff_map, ArithmeticThetaUnaryProduct.clearedUnaryTheta_coefficient_card
    m b 0 hm (by constructor <;> omega), map_natCast]
  by_cases hb : 12*m^2 ∣ b
  · obtain ⟨a, rfl⟩ := hb
    rw [PowerSeries.coeff_expand_mul, theta_coeff_card]
    congr 1
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro z
    have hmz : (m : ℤ) ≠ 0 := by omega
    have hw : (12 : ℤ)*(m : ℤ)^2 ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero _ hmz)
    simp only [add_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    constructor <;> intro hz
    · apply mul_left_cancel₀ hw
      nlinarith only [hz]
    · rw [mul_pow, hz]
      ring
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hb]
    letI hempty : IsEmpty {z : ℤ // 12*((m : ℤ)*z+0)^2 = (b : ℤ)} := by
      refine ⟨fun z => hb ⟨z.val.natAbs^2, ?_⟩⟩
      apply Int.ofNat_inj.mp
      simpa [Nat.cast_mul, Nat.cast_pow, sq_abs, mul_pow, mul_assoc] using z.2.symm
    rw [Nat.card_of_isEmpty, Nat.cast_zero]

lemma basic_series (k : Type) [Field k] [CharZero k] (N m : ℕ) (hN : 0 < N)
    (hm : 0 < m) (hd : m ∣ N) :
    ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (level N*m) = unarySeries k N m 0 := by
  have hd2 : m ∣ N^2 := dvd_trans hd ⟨N, by ring⟩
  have hq : N^2/m ≠ 0 := ne_of_gt (Nat.div_pos (Nat.le_of_dvd (pow_pos hN 2) hd2) hm)
  have he : level N*m/2 = N^2/m*(12*m^2) := by
    have hmul := Nat.div_mul_cancel hd2
    have hh : level N*m/2 = 12*N^2*m := by
      apply Nat.div_eq_of_eq_mul_right (by decide : 0 < 2)
      unfold level
      ring
    rw [hh]
    calc
      12*N^2*m = 12*(N^2/m*m)*m := by rw [hmul]
      _ = _ := by ring
  rw [ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior.thetaAt_eq_expand
    k (level N*m) (by rw [he]; positivity)]
  unfold unarySeries
  rw [← PowerSeries.expand_apply _ hq, PowerSeries.map_expand, cleared_zero k m hm,
    ← PowerSeries.expand_mul]
  simp only [he]

/-- Assemble on the existing cover indexed by distinct norms alone. -/
lemma assemble {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    (hU : Indexed A U) (hformal : FormalIdentity A U)
    (hN : 0 < commonN A) (hNeven : Even (commonN A))
    (hpairs : ∀ j, 0 < (U.pair j).1 ∧ Even (U.pair j).1 ∧
      (U.pair j).1 ∣ commonN A ∧
      (-((U.pair j).1 : ℤ) ≤ 2*(U.pair j).2 ∧ 2*(U.pair j).2 < ((U.pair j).1 : ℤ)))
    (hr : 0 < normCount A) (I : NormIndex A) (hI : IndexesNorms A I)
    (hm : ∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ commonN A ∧
      8*I.norm i ∣ level (commonN A))
    (D : LevelData ℂ (level (commonN A)))
    (X : Compactification ℂ (level (commonN A)) D)
    (H : Extension ℂ (level (commonN A)) D X)
    (hH : Canonical ℂ (level (commonN A)) H)
    (V : DiskTest ℂ (level (commonN A)) D X) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (level (commonN A)))
    (hmark : CanonicalMarking ℂ (level (commonN A)) ζ V.level) :
    ArithmeticThetaSharpKernelR0195.GeometricFamily A U H V := by
  classical
  have hr' : normCount A - 1 + 1 = normCount A := by omega
  let m : Fin (normCount A - 1 + 1) → ℕ := fun i => I.norm (Fin.cast hr' i)
  have hm' (i) : 0 < m i ∧ Even (m i) ∧ 8*m i ∣ level (commonN A) :=
    ⟨(hm _).1, (hm _).2.1, (hm _).2.2.2⟩
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12*(commonN A)^2, ?_⟩
    unfold level
    omega
  obtain ⟨B, C, het, hiso, g, hg, hgd, e, he0, he, frame, η, t₀, hframe, hη, hsquare, ht₀⟩ :=
    common_basic_unary_cover ℂ (level (commonN A)) (normCount A-1) (by omega)
      m hm' D X H hH V ζ hζ hmark
  let J := (B 0).squareLine
  let F : CoverFrame ℂ (commonN A) H V J (2^(normCount A-1)) C :=
    { disk := g, triangle := hg, dominant := hgd, frame := frame,
      isFrame := hframe, generator := η, extendsGenerator := hη, square_eq := hsquare }
  have hj (j : Fin U.count) : ∃ a : Fin (normCount A-1+1), m a = (U.pair j).1 := by
    obtain ⟨i, a, l, rfl⟩ := hU.2.2.2.2 j
    refine ⟨Fin.cast hr'.symm (I.index (i,l)), ?_⟩
    change I.norm (I.index (i,l)) = _
    rw [hI.2.2, hU.2.2.2.1]
  choose index hindex using hj
  let basic := fun j => t₀ (index j)
  have hbasic (j) : pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line)
      (basic j) = scalar (PowerSeries ℂ) (unarySeries ℂ (commonN A) (U.pair j).1 0) • F.frame := by
    have ht := (ht₀ (index j)).2.2
    rw [hindex j, basic_series ℂ (commonN A) (U.pair j).1 hN
      (hpairs j).1 (hpairs j).2.2.1] at ht
    exact ht
  obtain ⟨t, hpowers, ht⟩ := ratio_unary_regular_sections ℂ (commonN A) U.count
    hN hNeven (fun j => (U.pair j).1) (fun j => (U.pair j).2) hpairs
    D X H hH V ζ hζ hmark J _ C F basic hbasic
  let σ := fun i : Fin h => ∑ a : Cosets A i,
    tensorProductSection C.space ((Scheme.Modules.pullback C.map).obj J.line) n ⊤
      (fun j => t (U.index i a j))
  refine ⟨J, C, het, (fun hr1 => hiso (by omega)),
    square_half_hodge_cover_degree ℂ _ hL heven D X H hH _ J _ n C,
    F, t, σ, (fun j => ⟨(ht j).1, (ht j).2.1⟩), (fun _ => rfl), ?_⟩
  have hgb : F.disk ≫ (C.map ≫ projection ℂ (level (commonN A)) D X
      (V.disk (closedPoint ℂ))) = diskStructure ℂ := by
    change F.disk ≫ (C.map ≫ (inclusion ℂ (level (commonN A)) D X
      (V.disk (closedPoint ℂ)) ≫ X.projection)) = _
    rw [← Category.assoc C.map, ← Category.assoc F.disk, F.triangle]
    exact V.extends_eq.1
  intro c
  exact MatrixFamilyGlobalSectionsR0188.linear_expansion A U hformal _ F.disk hgb _
    F.frame F.isFrame t (fun j => (ht j).2.1) c

end SharpMatrixGeometricFamily

/-- Arithmetic input alone produces all geometry and the sharp matrix family. -/
theorem sharp_matrix_geometric_family :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ArithmeticThetaSharpKernelR0195.GeometricFamily A U H V := by
  intro n h hn hh A hA
  classical
  obtain ⟨hN, hNeven, _, U, hU, hpairs, hformal⟩ :=
    indexed_full_unary_factorization n h hn hh A hA
  obtain ⟨hr, I, hI, hm, _⟩ := distinct_norm_sharp_arithmetic n h hn hh A hA
  let L := level (commonN A)
  have hL : 3 ≤ L := by
    have hp : 0 < (commonN A)^2 := pow_pos hN 2
    dsimp [L, level]
    omega
  have heven : Even L := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [L, level]
    omega
  obtain ⟨atlas⟩ := legendre_level_family_construction ℂ L hL
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    normal_affine_classifying_construction ℂ L hL heven atlas
  let D : LevelData ℂ L := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨X⟩ := smooth_projective_level_completion ℂ L hL heven D
  obtain ⟨H, hH⟩ := compact_hodge_lattice_extension ℂ L hL heven D X
  letI : NeZero L := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ L
  obtain ⟨E, hE⟩ := tate_full_level_marking ℂ L hL heven ζ hζ
  obtain ⟨b, hb, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique ℂ L hL heven D E
  obtain ⟨T, hTE, hTb⟩ := (tate_hodge_comparison_tests ℂ L hL heven D).1 E b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension ℂ L hL heven D E X b hb
  let V : DiskTest ℂ L D X :=
    { toTest := T, disk := disk, extends_eq := hTb.symm ▸ hdisk }
  have hmark : CanonicalMarking ℂ L ζ V.level := by
    change CanonicalMarking ℂ L ζ T.level
    rw [hTE]
    exact hE
  exact ⟨U, hU, hformal, D, X, H, V, hH,
    SharpMatrixGeometricFamily.assemble A U hU hformal hN hNeven hpairs hr I hI hm
      D X H hH V ζ hζ hmark⟩

#print axioms sharp_matrix_geometric_family
end ArithmeticThetaSharpKernelR0195
