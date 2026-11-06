module

public import ValidGramFieldFormalIdentityR0232
public import RecoveredFieldConsumersR0232
public import FieldCommonBasicUnaryCoverR0238
public import FieldRatioUnaryRegularSectionsR0238
public import GeometricCanonicalHodgeDescentR0235
public import SplitSquareCoverDegreeR0239
public import FieldCosetSectionExpansionR0231
public import CompactActualMetaplecticLevelR0209
public import SharpMatrixGeometricFamilyR0195

@[expose] public section

/-! The sharp compact theta family over a characteristic-zero field containing the prescribed primitive root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCyclotomicModularityR0239
open ArithmeticThetaArithmeticFieldR0231
open ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections

open ArithmeticThetaSharpKernelR0195 ArithmeticThetaCompactModularityR0209

namespace SplitMatrixModularFamilyR0239

private lemma assemble (k : Type) [Field k] [CharZero k] {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    (hU : Indexed A U) (hformal : ArithmeticThetaArithmeticFieldR0231.FormalIdentity k A U)
    (hN : 0 < commonN A) (hNeven : Even (commonN A))
    (hpairs : ∀ j, 0 < (U.pair j).1 ∧ Even (U.pair j).1 ∧
      (U.pair j).1 ∣ commonN A ∧
      (-((U.pair j).1 : ℤ) ≤ 2*(U.pair j).2 ∧ 2*(U.pair j).2 < ((U.pair j).1 : ℤ)))
    (hr : 0 < normCount A) (I : NormIndex A) (hI : IndexesNorms A I)
    (hm : ∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ commonN A ∧
      8*I.norm i ∣ level (commonN A))
    (D : LevelData k (level (commonN A)))
    (X : Compactification k (level (commonN A)) D)
    (H : Extension k (level (commonN A)) D X)
    (hH : Canonical k (level (commonN A)) H)
    (hgH : ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H)
    (V : DiskTest k (level (commonN A)) D X) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (level (commonN A)))
    (hmark : CanonicalMarking k (level (commonN A)) ζ V.level) :
    ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ActualLevel G.root := by
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
    field_common_basic_unary_cover k (level (commonN A)) (normCount A-1) (by omega)
      m hm' D X H hH hgH V ζ hζ hmark
  let J := (B 0).squareLine
  let F : CoverFrame k (commonN A) H V J (2^(normCount A-1)) C :=
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
      (basic j) = scalar (PowerSeries k) (unarySeries k (commonN A) (U.pair j).1 0) • F.frame := by
    have ht := (ht₀ (index j)).2.2
    rw [hindex j, SharpMatrixGeometricFamily.basic_series k (commonN A) (U.pair j).1 hN
      (hpairs j).1 (hpairs j).2.2.1] at ht
    exact ht
  obtain ⟨t, hpowers, ht⟩ := field_ratio_unary_regular_sections k (commonN A) U.count
    hN hNeven (fun j => (U.pair j).1) (fun j => (U.pair j).2) hpairs
    D X H hH hgH V ζ hζ hmark J _ C F basic hbasic
  let σ := fun i : Fin h => ∑ a : Cosets A i,
    tensorProductSection C.space ((Scheme.Modules.pullback C.map).obj J.line) n ⊤
      (fun j => t (U.index i a j))
  have hgb : F.disk ≫ (C.map ≫ projection k (level (commonN A)) D X
      (V.disk (closedPoint k))) = diskStructure k := by
    change F.disk ≫ (C.map ≫ (inclusion k (level (commonN A)) D X
      (V.disk (closedPoint k)) ≫ X.projection)) = _
    rw [← Category.assoc C.map, ← Category.assoc F.disk, F.triangle]
    exact V.extends_eq.1
  let G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A :=
    { indexing := U
      indexed := hU
      formal := hformal
      data := D
      compact := X
      hodge := H
      canonical := hH
      test := V
      half := J
      cover := C
      etale := het
      oneNorm := fun hr1 => hiso (by omega)
      degree := split_square_cover_degree k _ ζ hζ hL heven D X H hH _ J _ n C
      frame := F
      unary := t
      sections := σ
      unary_expansion := fun j => ⟨(ht j).1, (ht j).2.1⟩
      coset_eq := fun _ => rfl
      expansion := fun c => field_coset_section_expansion k n h A U hformal _ _
        F.disk hgb _ F.frame F.isFrame t (fun j => (ht j).2.1) c }
  exact ⟨G, compact_actual_metaplectic_level k (level (commonN A))
    (2^(normCount A-1)) G.root hL heven G.etale⟩

end SplitMatrixModularFamilyR0239

/-- Construct the same norm-only compact cover, all matrix sections, their full
expansions and its actual finite metaplectic level over the specified field. -/
theorem split_matrix_modular_family :
∀ (k : Type) [Field k] [CharZero k] (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ ζ : k, IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) → ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root := by
  intro k _ _ n h hn hh A hA ζ hζ
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
  obtain ⟨atlas⟩ := legendre_level_family_construction k L hL
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    normal_affine_classifying_construction k L hL heven atlas
  let D : LevelData k L := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨X⟩ := smooth_projective_level_completion k L hL heven D
  obtain ⟨H, hH, hgH⟩ :=
    ArithmeticThetaBoundaryConstantsR0235.geometric_canonical_hodge_descent k L hL heven D X
  obtain ⟨E, hE⟩ := tate_full_level_marking k L hL heven ζ hζ
  obtain ⟨b, hb, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E
  obtain ⟨T, hTE, hTb⟩ := (tate_hodge_comparison_tests k L hL heven D).1 E b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension k L hL heven D E X b hb
  let V : DiskTest k L D X :=
    { toTest := T, disk := disk, extends_eq := hTb.symm ▸ hdisk }
  have hmark : CanonicalMarking k L ζ V.level := by
    change CanonicalMarking k L ζ T.level
    rw [hTE]
    exact hE
  have hfield := ArithmeticThetaArithmeticFieldR0232.valid_gram_field_formal_identity
    k n h A U hA hformal
  exact SplitMatrixModularFamilyR0239.assemble k A U hU hfield hN hNeven hpairs hr I hI hm
    D X H hH hgH V ζ hζ hmark

end ArithmeticThetaCyclotomicModularityR0239

#print axioms ArithmeticThetaCyclotomicModularityR0239.split_matrix_modular_family
