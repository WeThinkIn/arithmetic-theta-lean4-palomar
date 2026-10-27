import ComponentDiscriminantDivisorR0184
import GeometricComponentCuspBoundR0184

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaComponentDegreeR0184.ComponentHodgePowerDegreeR0184
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree ArithmeticThetaDegreeAssembly

local instance (Y : Scheme) : MonoidalCategory Y.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := Y.presheaf)

/-- The counit identifies the sheafification of an actual sheaf with itself. -/
def sheafCounit (Y : Scheme) (M : Y.Modules) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj M.val ≅ M :=
  asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit.app M)

/-- Genuine associativity, obtained from presheaf associativity and the
accepted tensor/sheafification comparison. -/
def tensorAssoc (Y : Scheme) (M N P : Y.Modules) :
    sheafTensor Y (sheafTensor Y M N) P ≅ sheafTensor Y M (sheafTensor Y N P) :=
  (sheafTensorCongr Y (Iso.refl _) (sheafCounit Y P)).symm ≪≫
  (sheafificationTensorIso Y (M.val ⊗ N.val) P.val).symm ≪≫
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso (α_ M.val N.val P.val) ≪≫
  sheafificationTensorIso Y M.val (N.val ⊗ P.val) ≪≫
  sheafTensorCongr Y (sheafCounit Y M) (Iso.refl _)

def tensorRightUnit (Y : Scheme) (M : Y.Modules) :
    sheafTensor Y M (SheafOfModules.unit Y.ringCatSheaf) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
  sheafCounit Y M

/-- Addition of exponents for the actual recursively sheafified tensor. -/
def powerAdd (Y : Scheme) (M : Y.Modules) (a : ℕ) :
    (b : ℕ) → tensorPower Y M (a+b) ≅
      sheafTensor Y (tensorPower Y M a) (tensorPower Y M b)
  | 0 => (tensorRightUnit Y (tensorPower Y M a)).symm
  | b+1 => sheafTensorCongr Y (powerAdd Y M a b) (Iso.refl M) ≪≫
      tensorAssoc Y (tensorPower Y M a) (tensorPower Y M b) M

/-- Multiplication of exponents includes the structure sheaf at exponent zero. -/
def powerMul (Y : Scheme) (M : Y.Modules) (a : ℕ) :
    (b : ℕ) → tensorPower Y (tensorPower Y M a) b ≅ tensorPower Y M (a*b)
  | 0 => Iso.refl _
  | b+1 => sheafTensorCongr Y (powerMul Y M a b) (Iso.refl _) ≪≫
      (powerAdd Y M (a*b) a).symm ≪≫
      eqToIso (congrArg (tensorPower Y M) (Nat.mul_succ a b).symm)

/-- Both iterated tensor powers identify with the same actual tensor sheaf. -/
def powerExchange (Y : Scheme) (M : Y.Modules) (a b : ℕ) :
    tensorPower Y (tensorPower Y M a) b ≅ tensorPower Y (tensorPower Y M b) a :=
  powerMul Y M a b ≪≫ eqToIso (congrArg (tensorPower Y M) (Nat.mul_comm a b)) ≪≫
    (powerMul Y M b a).symm

/-- Compare powers of two existing nonzero sections; no section of M is
required. All divisors are the actual local orders in the supplied frames. -/
theorem cross_power_degree (Y : Scheme) [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type) [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts Y) (M : Y.Modules) (a b : ℕ)
    (ι κ : Type) (C : NormalFrameCover Y (tensorPower Y M a) ι)
    (B : NormalFrameCover Y (tensorPower Y M b) κ)
    (t : Γ(tensorPower Y M a, ⊤)) (s : Γ(tensorPower Y M b, ⊤))
    (E F : Y →₀ ℤ) (ht : t ≠ 0) (hs : s ≠ 0)
    (hE : MatchesSectionOrder Y _ C t E) (hF : MatchesSectionOrder Y _ B s F) :
    (b : ℤ) * weightedDegree k f E = (a : ℤ) * weightedDegree k f F := by
  have hC := isLineBundle_of_normalFrameCover Y _ C
  have hB := isLineBundle_of_normalFrameCover Y _ B
  obtain ⟨htp, hEp⟩ := tensor_power_divisor Y _ hC ι C b t E ht hE
  obtain ⟨hsp, hFp⟩ := tensor_power_divisor Y _ hB κ B a s F hs hF
  have hCb := tensorPower_isLineBundle Y _ C b
  have hBa := tensorPower_isLineBundle Y _ B a
  obtain ⟨hte, hEe⟩ := line_isomorphism_divisor Y _ _ hCb hBa ι κ
    (powerCover Y _ C b) (powerCover Y _ B a) (powerExchange Y M a b)
    (tensorPowerSection Y _ b ⊤ t) (b • E) htp hEp
  have hd := ArithmeticThetaSectionCompletion.section_fixed_degree Y k f hcurve
    _ hBa κ (powerCover Y _ B a) _ _ (b • E) (a • F) hte hsp hEe hFp
  simpa only [weightedDegree_nsmul] using hd

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182

/-- The intrinsic open frame has its already proved canonical compact extension. -/
lemma compactD2_exists (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : LevelData k L)
    (X : Compactification k L D) (H : Extension k L D X) (hH : Canonical k L H) :
    ∃ s : Γ(tensorPower X.space H.line 24, ⊤), IsCompactD2 k L D X H s := by
  obtain ⟨d, hd, _⟩ := ArithmeticThetaOpenHodgeR0180.global_family_discriminant
    k D.atlas.quotient.ring D.atlas.quotient.smooth D.atlas.descent.family
  obtain ⟨s, hs, _⟩ := compact_discriminant_section k L hL heven D X H hH d hd
  exact ⟨s, d, hd, hs.1⟩

/-- Residue degrees are one at the actual cusps, through the component's
specified base map; summing the discriminant divisor counts precisely them. -/
lemma cusp_divisor_degree (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space)
    (F : (Component k L D X x) →₀ ℤ)
    (hF : ∀ y, (y ∈ cuspSet k L D X x → F y = (2*L : ℕ)) ∧
      (y ∉ cuspSet k L D X x → F y = 0)) :
    weightedDegree k (projection k L D X x) F =
      (2*L : ℕ) * (Nat.card (Cusps k L D X x) : ℤ) := by
  classical
  have hg := component_curve_frames k L hL heven D X x
  have hmem (y : Component k L D X x) : y ∈ F.support ↔ y ∈ cuspSet k L D X x := by
    rw [Finsupp.mem_support_iff]
    constructor
    · intro hy
      by_contra hc
      exact hy ((hF y).2 hc)
    · intro hy
      rw [(hF y).1 hy]
      exact_mod_cast (show 2 * L ≠ 0 by omega)
  have hcard := Nat.card_congr (Equiv.subtypeEquivRight hmem)
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  have hdeg (y : Component k L D X x) (hy : y ∈ F.support) :
      placeDegree k (projection k L D X x) y = 1 := by
    apply hg.2.2.2.2.2 y
    have hc := BoundaryGeometry.boundary_point_closed k L D X
      (inclusion k L D X x y) ((hmem y).mp hy)
    convert hc.preimage (inclusion k L D X x).continuous using 1
    ext z
    exact (inclusion k L D X x).isOpenEmbedding.injective.eq_iff.symm
  unfold weightedDegree Finsupp.sum
  calc
    ∑ y ∈ F.support, (placeDegree k (projection k L D X x) y : ℤ) * F y =
        ∑ _y ∈ F.support, ((2*L : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hdeg y hy, (hF y).1 ((hmem y).mp hy)]
      simp
    _ = (2*L : ℕ) * (Nat.card (Cusps k L D X x) : ℤ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcard]
      ring

#print axioms powerExchange
#print axioms cross_power_degree
#print axioms compactD2_exists
#print axioms cusp_divisor_degree
end ArithmeticThetaComponentDegreeR0184.ComponentHodgePowerDegreeR0184

namespace ArithmeticThetaComponentDegreeR0184
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaCurveDegree
open ComponentHodgePowerDegreeR0184

/-- Every nonzero section of any canonical Hodge power has the required
residue-weighted divisor degree and the geometric full-level upper bound. -/
theorem component_hodge_power_degree :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) ι) (t : (ArithmeticThetaComponentDegreeR0184.power k L D X x H n).presheaf.obj (Opposite.op ⊤)) (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ), t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) C t E → 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) = (n : ℤ) * (2*L : ℕ) * (Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) : ℤ) ∧ 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) ≤ (n : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
  intro k _ _ _ L hL heven D X x H hH n ι C t E ht hE
  have hg := component_curve_frames k L hL heven D X x
  letI := hg.1
  obtain ⟨κ, ⟨B⟩⟩ := (hg.2.2.2.2.1 H 24).2
  obtain ⟨s, hs⟩ := compactD2_exists k L hL heven D X H hH
  obtain ⟨hs0, hdiv⟩ := component_discriminant_divisor k L hL heven D X x H hH s hs
  obtain ⟨F, hF, hFc⟩ := hdiv κ B
  have hd := cross_power_degree (Component k L D X x) k (projection k L D X x)
    hg.2.2.1 (hodge k L D X x H) n 24 ι κ C B t
    (restrict k L D X x H 24 s) E F ht hs0 hE hF
  rw [cusp_divisor_degree k L hL heven D X x F hFc] at hd
  norm_num only at hd
  constructor
  · simpa only [mul_assoc] using hd
  · rw [hd]
    have hb := (geometric_component_cusp_bound k L hL heven D X x).2.2.2
    have hb' : ((2*L : ℕ) : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
      exact_mod_cast hb
    exact mul_le_mul_of_nonneg_left hb' (Int.natCast_nonneg n)

#print axioms component_hodge_power_degree
end ArithmeticThetaComponentDegreeR0184
