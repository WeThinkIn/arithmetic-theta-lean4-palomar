module

public import ArithmeticCommonCoverDefinitionsR0238
public import FieldCommonBasicUnaryCoverR0238
public import FieldRatioUnaryRegularSectionsR0238
public import SharpMatrixGeometricFamilyR0195

@[expose] public section

/-! Assemble the arithmetic common unary family on the basic comparison cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaSharpKernelR0195
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaPullback

/-- The common cover, full frame and regular unary sections are all constructed. -/
theorem arithmetic_common_unary_family :
    ∀ (k : Type) [Field k] [CharZero k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ), (∀ i, 0 < m i ∧ Even (m i) ∧ m i ∣ N ∧ (-(m i : ℤ) ≤ 2*ν i ∧ 2*ν i < (m i : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ArithmeticThetaArithmeticCommonCoverR0238.CommonUnary k N s m ν D X H V := by
  intro k _ _ N s hN hNeven m ν hm D X H hH hgH V ζ hζ hmark
  classical
  have hm' (i : Fin (s+1)) : 0 < m i ∧ Even (m i) ∧ 8*m i ∣ level N := by
    refine ⟨(hm i).1, (hm i).2.1, ?_⟩
    obtain ⟨a, ha⟩ := (hm i).2.2.1
    refine ⟨3*a*N, ?_⟩
    unfold level
    calc
      24*N^2 = 24*N*N := by ring
      _ = 8*(m i)*(3*a*N) := by rw [ha]; ring
  obtain ⟨A, C, het, hiso, g, hg, hgd, e, he0, he, frame, η, t₀,
      hframe, hη, hsquare, ht₀⟩ :=
    field_common_basic_unary_cover k (level N) s (by unfold level; positivity)
      m hm' D X H hH hgH V ζ hζ hmark
  let F : CoverFrame k N H V (A 0).squareLine (2^s) C :=
    { disk := g, triangle := hg, dominant := hgd, frame := frame,
      isFrame := hframe, generator := η, extendsGenerator := hη, square_eq := hsquare }
  have hbasic (i : Fin (s+1)) :
      pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj (A 0).data.line)
        (t₀ i) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
          (unarySeries k N (m i) 0) • F.frame := by
    have ht := (ht₀ i).2.2
    rw [ArithmeticThetaSharpKernelR0195.SharpMatrixGeometricFamily.basic_series
      k N (m i) hN (hm i).1 (hm i).2.2.1] at ht
    exact ht
  refine ⟨A, C, het, hiso, F, t₀, fun i => ⟨(ht₀ i).2.1, hbasic i⟩, ?_⟩
  exact field_ratio_unary_regular_sections k N (s+1) hN hNeven m ν hm
    D X H hH hgH V ζ hζ hmark (A 0).squareLine (2^s) C F t₀ hbasic

#print axioms arithmetic_common_unary_family
end ArithmeticThetaArithmeticCommonCoverR0238
