module

public import PeriodOneGeometricComparisonR0246
public import PeriodOneNormalizedFrameR0246
public import UnmarkedTateDiscriminantR0245
public import ArbitraryDiscriminantNaturalityR0243

@[expose] public section

/-! The intrinsic five-Kato discriminant on the concrete period-one cubic.
Faithful pullback uses the actual Laurent extension Q ↦ t⁴ throughout. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaPeriodOneR0246
namespace DiscriminantProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open ArithmeticThetaTateCuspsR0181

/-- A framed section module detects equality after any injective coefficient map.
The two field carriers need not be distinct; the specified ring map is retained. -/
lemma framed_pull_injective {R S : Type} [Field R] [Field S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι)
    (d : Sections (HodgePower R W 24)) (hd : IsFrame (HodgePower R W 24) ⊤ d) :
    Function.Injective (pull C) := by
  intro s t h
  have hpull := (NormalDiscriminantIndependence.pull_eq_iff C s t).mp h
  obtain ⟨a, ha⟩ := (hd ⊤ le_rfl).2 s
  obtain ⟨b, hb⟩ := (hd ⊤ le_rfl).2 t
  rw [InitialHodgeSection.res_self] at ha hb
  change a • d = s at ha
  change b • d = t at hb
  rw [← ha, ← hb, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.pullbackLocalSection_smul] at hpull
  have hframe := pullback_frame (Spec.map (CommRingCat.ofHom ι)) _ d hd
  have hab : (Spec.map (CommRingCat.ofHom ι)).app ⊤ a =
      (Spec.map (CommRingCat.ofHom ι)).app ⊤ b := (hframe _ le_rfl).1 (by
    simpa only [InitialHodgeSection.res_self] using hpull)
  have habTop : (Spec.map (CommRingCat.ofHom ι)).appTop a =
      (Spec.map (CommRingCat.ofHom ι)).appTop b :=
    congrArg (fun z => (Spec (CommRingCat.of S)).presheaf.map
      (homOfLE (show ⊤ ≤ (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ ⊤ by simp)).op z) hab
  have he := NormalDiscriminantIndependence.CoordinateUniverse.Extensionality.DenseExtAux.specMap_appTop_injective
    ι ι.injective habTop
  rw [← ha, ← hb, he]

lemma boundary_frame (k : Type) [Field k] [CharZero k] :
    ∃ δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k 4,
      ArithmeticThetaBoundaryHodgeR0182.Normalized k 4 δ := by
  letI := TateFullLevelMarking.elliptic k 4 (by decide) (by decide)
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k 4)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k 4).toProjective
  have hΩ : Scheme.Modules.IsInvertible
      (structureMap (LaurentSeries k) (TateCurve k 4)).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap (LaurentSeries k) (TateCurve k 4)).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  exact ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.lifted_global_frame
    k 4 (Iso.refl _) (by decide) (by decide)
    (structureMap (LaurentSeries k) (TateCurve k 4)) (Category.id_comp _) hΩ

/-- Pulling the proposed full expansion transports both its literal series
and its specified differential by the same coordinate comparison. -/
lemma pull_expansion (k : Type) [Field k] [CharZero k]
    [(periodOneCurve k).IsElliptic]
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell)
    (C : CoordinateComparison k ell) (δ : PeriodFrame k) (hδ : Normalized k δ)
    (ε : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k 4)
    (hε : ArithmeticThetaBoundaryHodgeR0182.Normalized k 4 ε) :
    pull C.toComparison (scalar (LaurentSeries k)
      (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 1) •
        tensorPowerSection (Base (LaurentSeries k))
          (Hodge (LaurentSeries k) (periodOneCurve k)) 24 ⊤ (generator k δ)) =
      scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 4) •
        tensorPowerSection (Base (LaurentSeries k))
          (Hodge (LaurentSeries k) (TateCurve k 4)) 24 ⊤
          (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k 4 ε) := by
  change transportSection _ _ _ (comparisonPower C.toComparison) _ = _
  rw [transportSection_smul]
  change _ • transportSection _ _ _ (tensorComparison _ _ _
    (comparisonHodge C.toComparison) 24) _ = _
  rw [transportSection_tensor]
  have hgen := (period_one_normalized_frame k).2 ell hell C δ hδ ε hε
  change transportSection _ _ _ (comparisonHodge C.toComparison) (generator k δ) = _ at hgen
  rw [hgen]
  have hscalar : (Spec.map (CommRingCat.ofHom ell)).appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 1)) =
      scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 4) := by
    rw [show (Spec.map (CommRingCat.ofHom ell)).appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 1)) =
      scalar (LaurentSeries k) (ell (ArithmeticThetaUnaryKatoPowerR0160.discriminant k 1)) from
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom ell)) _).symm]
    rw [ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.discriminant_ramification
      k 1 4 (by decide) (by decide) ell hell, Nat.one_mul]
  rw [hscalar]

lemma full_expansion (k : Type) [Field k] [CharZero k]
    [(periodOneCurve k).IsElliptic] (d : PeriodSections k)
    (hd : ArithmeticThetaPeriodOneR0246.IsD2 k d)
    (hframe : IsFrame (HodgePower (LaurentSeries k) (periodOneCurve k) 24) ⊤ d)
    (δ : PeriodFrame k) (hδ : Normalized k δ) : FullExpansion k δ d := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := TateFullLevelMarking.elliptic k 4 (by decide) (by decide)
  obtain ⟨ell, ⟨hell, _⟩, _⟩ :=
    ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k 4 (by decide)
  obtain ⟨C⟩ := ((period_one_geometric_comparison k).2 ell hell).2
  obtain ⟨ε, hε⟩ := boundary_frame k
  obtain ⟨e, he, _⟩ := arbitrary_weierstrass_discriminant (LaurentSeries k) (TateCurve k 4)
  let ι : LaurentSeries k →ₐ[ℚ] LaurentSeries k := {
    toRingHom := ell
    commutes' := ell.map_rat_algebraMap }
  have hn := arbitrary_discriminant_naturality (LaurentSeries k) (periodOneCurve k)
    (LaurentSeries k) (TateCurve k 4) ι C.toComparison d e hd he.1
  have hx := ArithmeticThetaSchemeTateDiscriminantR0245.unmarked_tate_discriminant
    k 4 (by decide) (by decide) ε hε e he.1
  apply framed_pull_injective C.toComparison d hframe
  rw [hn, pull_expansion k ell hell C δ hδ ε hε]
  exact hx

end DiscriminantProof

open ArithmeticThetaRelativeDiscriminantR0171

/-- The concrete period-one curve carries the unique intrinsic five-Kato
discriminant, with its complete product expansion in every normalized frame. -/
theorem period_one_discriminant :
    ∀ (k : Type) [Field k] [CharZero k],
      ∃ δ : PeriodFrame k, Normalized k δ ∧ ∃! d : PeriodSections k,
        IsD2 k d ∧ IsFrame (HodgePower (LaurentSeries k) (periodOneCurve k) 24) ⊤ d ∧
          ∀ δ' : PeriodFrame k, Normalized k δ' → FullExpansion k δ' d := by
  intro k _ _
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := (period_one_geometric_comparison k).1
  obtain ⟨δ, hδ, _⟩ := (period_one_normalized_frame k).1
  obtain ⟨d, hd, hu⟩ :=
    ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_weierstrass_discriminant
      (LaurentSeries k) (periodOneCurve k)
  refine ⟨δ, hδ, d, ⟨hd.1, hd.2, ?_⟩, ?_⟩
  · intro δ' hδ'
    exact DiscriminantProof.full_expansion k d hd.1 hd.2 δ' hδ'
  · intro e he
    exact hu e ⟨he.1, he.2.1⟩

#print axioms period_one_discriminant
end ArithmeticThetaPeriodOneR0246
