module

public import SharpCoverRatiosDefinitionsR0194
public import SplitHodgePowerDegreeR0239

@[expose] public section

/-! Degree of every power of an arbitrary actual Hodge square root on a finite cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaCyclotomicModularityR0239
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSharpCoverR0194
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree ArithmeticThetaDegreeAssembly
open ComponentHodgePowerDegreeR0184

/-- Compare the actual pulled Hodge power with the corresponding even power
of the square root, retaining the specified square map. -/
private def squarePowerPull {Z Y : Scheme} {W : Z.Modules}
    (p : Y ⟶ Z) (J : SquareLine Z W) (a : ℕ) :
    tensorPower Y ((Scheme.Modules.pullback p).obj J.line) (2*a) ≅
      (Scheme.Modules.pullback p).obj (tensorPower Z W a) :=
  (powerMul Y ((Scheme.Modules.pullback p).obj J.line) 2 a).symm ≪≫
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.powerCongr Y (squarePull p J) a ≪≫
    (pullback_tensorPower_iso Y Z p W a).symm

/-- The residue-weighted degree on every actual finite smooth proper cover,
without a section or an effective divisor assumption on the base square root. -/
theorem split_square_cover_degree :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L →
    ∀ (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X),
      Canonical k L H → ∀ (x : X.space)
      (J : SquareLine (Component k L D X x) (hodge k L D X x H)) (b n : ℕ)
      (C : RootCover k (Component k L D X x) (projection k L D X x) b),
      SquareCoverDegree k L D X H x J b n C := by
  intro k _ _ L ζ hζ hL heven D X H hH x J b n C
  have hg := ArithmeticThetaArithmeticHalfLinesR0237.field_component_geometry
    k L hL heven D X x
  letI := hg.1
  letI := C.integral
  letI := C.finite
  letI := C.flat
  letI := C.surjective
  letI := C.proper
  letI := C.smooth
  letI hY : IsLocallyNoetherian C.space :=
    LocallyOfFiniteType.isLocallyNoetherian (C.map ≫ projection k L D X x)
  have hcurve : OneDimensionalCharts C.space :=
    ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.smooth_oneDimensionalCharts
      (C.map ≫ projection k L D X x)
  have hnormal : NormalAffine C.space := fun U hU =>
    ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed
      C.space k (C.map ≫ projection k L D X x) U hU
  have hinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback C.map).obj J.line) :=
    J.invertible.pullback C.map
  obtain ⟨B⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    C.space hnormal _ hinv
  -- The discriminant supplies a section of Hodge^24, hence of J^48 after pullback.
  obtain ⟨A0⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hg.2.2.2 (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  let ι := Component k L D X x
  let A := powerCover (Component k L D X x) (hodge k L D X x H) A0 24
  obtain ⟨s, hs⟩ := split_compact_discriminant k L ζ hζ hL heven D X x H hH
  obtain ⟨hs0, hdiv⟩ := split_component_discriminant_divisor k L ζ hζ hL heven D X x H hH s hs
  obtain ⟨F, hF, _⟩ := hdiv ι A
  have hbase := (split_hodge_power_degree k L ζ hζ hL heven D X x H hH
    24 ι A (restrict k L D X x H 24 s) F hs0 hF).1
  have hbaseLine := tensorPower_isLineBundle (Component k L D X x)
    (hodge k L D X x H) A0 24
  have hpLine := pullback_isLineBundle C.space (Component k L D X x) C.map _ hbaseLine
  let e := squarePowerPull C.map J 24
  let BP := powerCover C.space ((Scheme.Modules.pullback C.map).obj J.line) B 48
  have h48 := tensorPower_isLineBundle C.space _ B 48
  -- Transport frames to the actual pullback of Hodge^24 through the inverse comparison.
  let Q : NormalFrameCover C.space
      ((Scheme.Modules.pullback C.map).obj (power k L D X x H 24)) C.space :=
    { opens := BP.opens
      covers := BP.covers
      nonempty := BP.nonempty
      affine := BP.affine
      normal := BP.normal
      frame := fun i => inverseImageFrame e.symm (BP.frame i) }
  have hp0 := pullbackGlobalSection_ne_zero C.map _ hbaseLine _ hs0
  obtain ⟨FY, hFY⟩ := exists_section_divisor C.space k
    (C.map ≫ projection k L D X x) hcurve _ C.space Q
    (pullbackGlobalSection C.map _ (restrict k L D X x H 24 s)) hp0
  have hpdeg := (finite_pullback_section_degree (Component k L D X x) C.space k
    (projection k L D X x) C.map hg.2.2.1 hcurve _ hbaseLine ι C.space A Q
    (restrict k L D X x H 24 s) F FY hs0 hF hFY).2
  obtain ⟨hv, hV⟩ := line_isomorphism_divisor C.space _ _ hpLine h48
    C.space C.space Q BP e.symm
    (pullbackGlobalSection C.map _ (restrict k L D X x H 24 s)) FY hp0 hFY
  refine ⟨hY, hcurve, hnormal, hinv, ⟨C.space, ⟨powerCover _ _ B n⟩⟩, ?_⟩
  intro κ A' t E ht hE
  have hcross := cross_power_degree C.space k (C.map ≫ projection k L D X x)
    hcurve ((Scheme.Modules.pullback C.map).obj J.line) n 48 κ C.space A' BP t
    (e.symm.hom.app ⊤ (pullbackGlobalSection C.map _ (restrict k L D X x H 24 s)))
    E FY ht hv hE hV
  have hex : 24 * weightedDegree k (C.map ≫ projection k L D X x) E =
      (n : ℤ) * (C.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
        (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) := by
    rw [hpdeg] at hcross
    norm_num only [Nat.cast_ofNat, Nat.cast_mul] at hbase hcross
    have hbase' : weightedDegree k (projection k L D X x) F =
        2 * (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) := by nlinarith [hbase]
    rw [hbase'] at hcross
    nlinarith [hcross]
  refine ⟨hex, ?_⟩
  have hb : (2 : ℤ) * (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
    exact_mod_cast (split_component_cusp_bound k L ζ hζ hL heven D X x).2.2
  have hr : (C.map.finrank (genericPoint (Component k L D X x)) : ℤ) ≤ (b : ℤ) := by
    exact_mod_cast (C.degree (genericPoint (Component k L D X x))).2
  calc
    48 * weightedDegree k (C.map ≫ projection k L D X x) E =
        (n : ℤ) * (C.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
          (2 * (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ)) := by
      calc
        _ = 2 * (24 * weightedDegree k (C.map ≫ projection k L D X x) E) := by ring
        _ = _ := by rw [hex]; ring
    _ ≤ (n : ℤ) * (C.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity)

#print axioms split_square_cover_degree
end ArithmeticThetaCyclotomicModularityR0239
