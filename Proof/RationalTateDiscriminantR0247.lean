module

public import RationalTatePresentationR0247
public import RationalCoordinateHodgeR0247

@[expose] public section

/-! The full period-one discriminant expansion over arbitrary rational rings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaRationalTateR0247
namespace RationalDiscriminantProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open ArithmeticThetaPeriodOneR0246

variable (R : Type) [CommRing R] [Algebra ℚ R]

/-- The coefficient map preserves the specified rational algebra structures. -/
def rationalAlgMap : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries R where
  toRingHom := rationalMap R
  commutes' := (rationalMap R).map_rat_algebraMap

lemma map_inclusion (s : PowerSeries ℚ) :
    rationalMap R (HahnSeries.ofPowerSeries ℤ ℚ s) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.map (algebraMap ℚ R) s) := by
  ext n
  change (algebraMap ℚ R) ((s : LaurentSeries ℚ).coeff n) =
    ((PowerSeries.map (algebraMap ℚ R) s : LaurentSeries R).coeff n)
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map]

/-- This is equality of entire Laurent series, including every coefficient. -/
lemma map_product :
    rationalMap R (ArithmeticThetaUnaryKatoPowerR0160.discriminant ℚ 1) =
      productSeries R := by
  simp only [ArithmeticThetaUnaryKatoPowerR0160.discriminant, pow_one,
    PowerSeries.X_subst, Algebra.algebraMap_self, PowerSeries.map_id, id_eq]
  exact map_inclusion R _

lemma pull_expansion [(periodOneCurve ℚ).IsElliptic] [(equation R).IsElliptic]
    (C : ArithmeticThetaRationalTateR0247.CoordinateComparison (LaurentSeries ℚ)
      (LaurentSeries R) (periodOneCurve ℚ) (equation R) (rationalMap R))
    (δ : PeriodFrame ℚ) (hδ : ArithmeticThetaPeriodOneR0246.Normalized ℚ δ)
    (ε : Frame R) (hε : ArithmeticThetaRationalTateR0247.Normalized R ε) :
    pull C.toComparison (scalar (LaurentSeries ℚ)
      (ArithmeticThetaUnaryKatoPowerR0160.discriminant ℚ 1) •
        tensorPowerSection (Base (LaurentSeries ℚ))
          (Hodge (LaurentSeries ℚ) (periodOneCurve ℚ)) 24 ⊤
          (ArithmeticThetaPeriodOneR0246.generator ℚ δ)) =
      scalar (LaurentSeries R) (productSeries R) •
        tensorPowerSection (Base (LaurentSeries R))
          (Hodge (LaurentSeries R) (equation R)) 24 ⊤
          (ArithmeticThetaRationalTateR0247.generator R ε) := by
  change transportSection _ _ _ (comparisonPower C.toComparison) _ = _
  rw [transportSection_smul]
  change _ • transportSection _ _ _ (tensorComparison _ _ _
    (comparisonHodge C.toComparison) 24) _ = _
  rw [transportSection_tensor]
  have hgen := rational_coordinate_hodge (LaurentSeries ℚ) (LaurentSeries R)
    (periodOneCurve ℚ) (equation R) (rationalAlgMap R) C δ ε hδ hε
  change transportSection _ _ _ (comparisonHodge C.toComparison)
    (ArithmeticThetaPeriodOneR0246.generator ℚ δ) = _ at hgen
  rw [hgen]
  have hscalar : (Spec.map (CommRingCat.ofHom (rationalMap R))).appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries ℚ) (ArithmeticThetaUnaryKatoPowerR0160.discriminant ℚ 1)) =
      scalar (LaurentSeries R) (productSeries R) := by
    rw [show (Spec.map (CommRingCat.ofHom (rationalMap R))).appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries ℚ) (ArithmeticThetaUnaryKatoPowerR0160.discriminant ℚ 1)) =
      scalar (LaurentSeries R)
        (rationalMap R (ArithmeticThetaUnaryKatoPowerR0160.discriminant ℚ 1)) from
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (rationalMap R))) _).symm]
    rw [map_product]
  rw [hscalar]

lemma full_expansion [(equation R).IsElliptic]
    (d : ArithmeticThetaRationalTateR0247.Sections R)
    (hd : ArithmeticThetaRationalTateR0247.IsD2 R d)
    (ε : Frame R) (hε : ArithmeticThetaRationalTateR0247.Normalized R ε) :
    ArithmeticThetaRationalTateR0247.FullExpansion R ε d := by
  let := (period_one_geometric_comparison ℚ).1
  obtain ⟨C⟩ := (rational_tate_presentation.1 R).2
  obtain ⟨δ, hδ, e, he, _⟩ := period_one_discriminant ℚ
  have hn := arbitrary_discriminant_naturality (LaurentSeries ℚ) (periodOneCurve ℚ)
    (LaurentSeries R) (equation R) (rationalAlgMap R) C.toComparison e d he.1 hd
  have hx := he.2.2 δ hδ
  change e = _ at hx
  change d = _
  rw [← hn, hx]
  exact pull_expansion R C δ hδ ε hε

end RationalDiscriminantProof
open ArithmeticThetaRelativeDiscriminantR0171

/-- The intrinsic section is a frame on every open and has the full product
expansion in every normalized frame, without restrictions on the rational ring. -/
theorem rational_tate_discriminant :
    ∀ (R : Type) [CommRing R] [Algebra ℚ R],
      ∃ δ : Frame R, Normalized R δ ∧ ∃! d : Sections R,
        IsD2 R d ∧ IsFrame (HodgePower (LaurentSeries R) (equation R) 24) ⊤ d ∧
          ∀ δ' : Frame R, Normalized R δ' → FullExpansion R δ' d := by
  intro R _ _
  let := (rational_tate_presentation.1 R).1
  obtain ⟨δ, hδ, _⟩ := rational_normalized_frame (LaurentSeries R) (equation R)
  obtain ⟨d, hd, hu⟩ :=
    ArithmeticThetaArbitraryDiscriminantR0243.arbitrary_weierstrass_discriminant
      (LaurentSeries R) (equation R)
  refine ⟨δ, hδ, d, ⟨hd.1, hd.2, ?_⟩, ?_⟩
  · intro δ' hδ'
    exact RationalDiscriminantProof.full_expansion R d hd.1 δ' hδ'
  · intro e he
    exact hu e ⟨he.1, he.2.1⟩

#print axioms rational_tate_discriminant
end ArithmeticThetaRationalTateR0247
