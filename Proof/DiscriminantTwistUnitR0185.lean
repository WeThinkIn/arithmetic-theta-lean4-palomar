module

public import CommonHalfHodgeDefinitionsR0185

@[expose] public section

/-! Construction of the discriminant twist on the actual compact component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTwistUnitR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree ArithmeticThetaDegreeAssembly
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaGeometricPrerequisites

/-- The local sheaf trivializations and the invertibility predicate use the
same restriction/pullback comparison. -/
lemma invertible_of_lineBundle (Y : Scheme.{0}) (M : Y.Modules) (hM : IsLineBundle Y M) :
    Scheme.Modules.IsInvertible M := by
  constructor
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hM y
  refine ⟨U, hy, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e.symm ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    Scheme.Modules.pullbackUnitIso U.ι

/-- A global natural frame gives a genuine global sheaf isomorphism. -/
def globalFrameIso (Y : Scheme.{0}) (M : Y.Modules) (e : LocalFrame Y M ⊤) :
    SheafOfModules.unit Y.ringCatSheaf ≅ M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U => (e.equiv U.unop le_top).toModuleIso)
      (fun {U V} f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (e.naturality U.unop V.unop f.unop.le le_top a).symm))

/-- The canonical effective divisor section has the prescribed orders in
every normal frame; its construction is the accepted bounded-pole sheaf. -/
lemma canonical_divisor_orders (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (hc : OneDimensionalCharts Y) (hN : NormalAffine Y) (E : Y →₀ ℤ)
    (hE : ∀ y, 0 ≤ E y) (hco : ∀ y, E y ≠ 0 → Order.coheight y = 1)
    (ι : Type) (C : NormalFrameCover Y (divisorSheaf Y hN E) ι) :
    MatchesSectionOrder Y (divisorSheaf Y hN E) C
      (divisorCanonicalSection Y hN E hE) E := by
  intro i y hy
  obtain ⟨U, hyU, _, r, hr, hord⟩ := exists_local_divisor_equation Y hc hN E hE hco y
  letI : Nonempty U := ⟨⟨y, hyU⟩⟩
  change E y = Scheme.ord (sectionCoefficient Y _ _ (C.frame i) _) y
  rw [section_order_frame_invariant Y _ (C.opens i) U (C.frame i)
    (equationFrame Y hN E U r hr hord) _ y hy hyU,
    equationFrame_canonical_coefficient Y hN E hE U r hr hord]
  exact (hord y hyU).symm

/-- Construct the actual negative divisor line and its cancellation map
against any line with the given nonzero canonical effective section. -/
theorem inverse_of_effective_section (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (hc : OneDimensionalCharts Y) (hN : NormalAffine Y)
    (B : Y.Modules) (ι : Type) (C : NormalFrameCover Y B ι)
    (b : Γ(B, ⊤)) (hb : b ≠ 0) (E : Y →₀ ℤ)
    (hE : ∀ y, 0 ≤ E y) (hco : ∀ y, E y ≠ 0 → Order.coheight y = 1)
    (hB : MatchesSectionOrder Y B C b E) :
    ∃ (N : Y.Modules), Scheme.Modules.IsInvertible N ∧
      Nonempty (sheafTensor Y N B ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  have hline := ArithmeticThetaCoverComparison.signed_divisor_line Y hc hN E hco
  have hi := invertible_of_lineBundle Y _ hline
  obtain ⟨F⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible Y hN _ hi
  obtain ⟨e, _, _⟩ := equal_divisor_rigidified_isomorphism Y hc hN B _
    (isLineBundle_of_normalFrameCover Y B C) hline ι Y C F b
    (divisorCanonicalSection Y hN E hE) E hb
    (divisorCanonicalSection_ne_zero Y hN E hE) hB
    (canonical_divisor_orders Y hc hN E hE hco Y F)
  have hneg : ∀ y, (-E) y ≠ 0 → Order.coheight y = 1 := by
    intro y hy
    apply hco y
    simpa using hy
  have hinv := invertible_of_lineBundle Y _
    (ArithmeticThetaCoverComparison.signed_divisor_line Y hc hN (-E) hneg)
  obtain ⟨m, _⟩ := ArithmeticThetaCoverComparison.signed_divisor_tensor Y hc hN (-E) E hneg hco
  let z : LocalFrame Y (divisorSheaf Y hN 0) ⊤ :=
    equationFrame Y hN 0 ⊤ 1 one_ne_zero (by
      intro y _
      simp only [Finsupp.zero_apply]
      exact rational_order_one Y y)
  refine ⟨divisorSheaf Y hN (-E), hinv, ⟨?_⟩⟩
  exact sheafTensorCongr Y (Iso.refl _) e ≪≫ m ≪≫
    eqToIso (congrArg (divisorSheaf Y hN) (neg_add_cancel E)) ≪≫
    (globalFrameIso Y _ z).symm

/-- The exact discriminant divisor rigidifies the comparison between the
twenty-fourth power of the square cusp line and the Hodge discriminant line.
The section on the right is the restriction of the given compact D2. -/
theorem discriminant_comparison
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 0 < L) (h24 : 24 ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A) :
    ∃ e : tensorPower (Component k L D X x)
        (tensorPower (Component k L D X x) A.line 2) 24 ≅ power k L D X x H 24,
      e.hom.app ⊤ (tensorPowerSection (Component k L D X x)
        (tensorPower (Component k L D X x) A.line 2) 24 ⊤
        (tensorPowerSection (Component k L D X x) A.line 2 ⊤ A.section_)) =
          restrict k L D X x H 24 s := by
  have hlev : 3 ≤ L := by obtain ⟨n, rfl⟩ := h24; omega
  have heven : Even L := by
    obtain ⟨n, rfl⟩ := h24
    exact ⟨12 * n, by omega⟩
  have hg := component_curve_frames k L hlev heven D X x
  obtain ⟨E, ⟨hAi, ha0, ⟨ι, ⟨C⟩⟩, hAE⟩, hEc⟩ := hA
  have hline := isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨ha2, hE2⟩ := tensor_power_divisor _ A.line hline ι C 2 A.section_ E ha0
    (hAE ι C)
  have hline2 := tensorPower_isLineBundle _ A.line C 2
  let C2 := powerCover _ A.line C 2
  obtain ⟨ha48, hE48⟩ := tensor_power_divisor _ _ hline2 ι C2 24 _ (2 • E) ha2 hE2
  have hline48 := tensorPower_isLineBundle _ _ C2 24
  obtain ⟨κ, ⟨B⟩⟩ := (hg.2.2.2.2.1 H 24).2
  obtain ⟨hs0, hsD⟩ := component_discriminant_divisor k L hlev heven D X x H hH s hs
  obtain ⟨F, hF, hFc⟩ := hsD κ B
  have heq : 24 • (2 • E) = F := by
    ext y
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    by_cases hy : y ∈ cuspSet k L D X x
    · rw [(hEc y).1 hy, (hFc y).1 hy]
      have hdiv : 24 * (L / 24) = L := Nat.mul_div_cancel' h24
      have hdiv' : (24 : ℤ) * (L / 24 : ℕ) = (L : ℤ) := by exact_mod_cast hdiv
      push_cast
      nlinarith
    · rw [(hEc y).2 hy, (hFc y).2 hy]
      simp
  rw [heq] at hE48
  obtain ⟨e, he, _⟩ := equal_divisor_rigidified_isomorphism _ hg.2.2.1 hg.2.2.2.1
    _ _ hline48 (hg.2.2.2.2.1 H 24).1 ι κ (powerCover _ _ C2 24) B
    _ _ F ha48 hs0 hE48 hF
  exact ⟨e, he⟩

/-- The actual inverse divisor line produces the twist and its multiplication
map. Codimension one is proved for the actual component cusp support. -/
theorem twist_line_exists
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 0 < L) (h24 : 24 ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A) :
    ∃ M : (Component k L D X x).Modules, Scheme.Modules.IsInvertible M ∧
      Nonempty (sheafTensor (Component k L D X x) M
        (tensorPower (Component k L D X x) A.line 2) ≅ hodge k L D X x H) := by
  have hlev : 3 ≤ L := by obtain ⟨n, rfl⟩ := h24; omega
  have heven : Even L := by obtain ⟨n, rfl⟩ := h24; exact ⟨12 * n, by omega⟩
  have hg := component_curve_frames k L hlev heven D X x
  letI := hg.2.1
  letI := X.openImmersion
  obtain ⟨E, ⟨_, ha0, ⟨ι, ⟨C⟩⟩, hAE⟩, hEc⟩ := hA
  have hco : ∀ y, E y ≠ 0 → Order.coheight y = 1 := by
    intro y hy
    have hc : y ∈ cuspSet k L D X x := by
      by_contra hn
      exact hy ((hEc y).2 hn)
    apply ArithmeticThetaGeometricNormR0150.NormOrders.smooth_coheight_one_of_ne_generic
      k (projection k L D X x)
    intro heq
    have hgen : genericPoint (Component k L D X x) ∈
        inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange :=
      ((genericPoint_spec (Component k L D X x)).mem_open_set_iff
        (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange).isOpen).mpr
          (by simpa using ComponentDiscriminantDivisorR0184.component_interior_nonempty k L D X x)
    rw [← heq] at hgen
    exact hc hgen
  have hE : ∀ y, 0 ≤ E y := by
    intro y
    by_cases hy : y ∈ cuspSet k L D X x
    · rw [(hEc y).1 hy]; exact Int.natCast_nonneg _
    · rw [(hEc y).2 hy]
  have hline := isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨ha2, hE2⟩ := tensor_power_divisor _ _ hline ι C 2 A.section_ E ha0 (hAE ι C)
  obtain ⟨N, hN, ⟨eN⟩⟩ := inverse_of_effective_section _ hg.2.2.1 hg.2.2.2.1
    _ ι (powerCover _ _ C 2) _ ha2 (2 • E)
    (fun y => by simpa only [Finsupp.smul_apply] using nsmul_nonneg (hE y) 2)
    (fun y hy => hco y (by intro hz; apply hy; simp [hz])) hE2
  refine ⟨sheafTensor _ (hodge k L D X x H) N,
    CompactHodgeLatticeExtensionR0182.sheafTensor_invertible
      (H.invertible.pullback (inclusion k L D X x)) hN, ⟨?_⟩⟩
  exact ComponentHodgePowerDegreeR0184.tensorAssoc _ _ _ _ ≪≫
    sheafTensorCongr _ (Iso.refl _) eN ≪≫
    ComponentHodgePowerDegreeR0184.tensorRightUnit _ _

section Normalize
variable {Y : Scheme.{0}} {M B H : Y.Modules} (n : ℕ)
    (m : sheafTensor Y M B ≅ H) (e : tensorPower Y B n ≅ tensorPower Y H n)

lemma hom_restrict {P Q : Y.Modules} (f : P ⟶ Q) {V W : Y.Opens}
    (h : W ≤ V) (s : Γ(P,V)) :
    Q.presheaf.map (homOfLE h).op (f.app V s) =
      f.app W (P.presheaf.map (homOfLE h).op s) :=
  (PresheafOfModules.naturality_apply f.val (homOfLE h).op s).symm

/-- Transport the actual tensor frame through the specified multiplication. -/
def productFrame {U : Y.Opens} (μ : LocalFrame Y M U) (ν : LocalFrame Y B U) :
    LocalFrame Y H U where
  equiv V h := ((tensorFrame Y M B U μ ν).equiv V h).trans
    (lineIsoSectionsLinearEquiv m V)
  naturality V W hWV hVU a := by
    change H.presheaf.map (homOfLE hWV).op
      (m.hom.app V ((tensorFrame Y M B U μ ν).equiv V hVU a)) = _
    rw [hom_restrict]
    rw [(tensorFrame Y M B U μ ν).naturality V W hWV hVU a]
    rfl

lemma productFrame_apply {U : Y.Opens} (μ : LocalFrame Y M U) (ν : LocalFrame Y B U)
    (V : Y.Opens) (h : V ≤ U) (a b : Γ(Y, V)) :
    m.hom.app V (tensorSection Y M B V (μ.equiv V h a) (ν.equiv V h b)) =
      (productFrame m μ ν).equiv V h (a * b) := by
  rw [tensorSection_frame]
  rfl

/-- The normalization scalar is the ratio of two genuine power frames. -/
def normalizationCoefficient {U : Y.Opens} (μ : LocalFrame Y M U) (ν : LocalFrame Y B U)
    (V : Y.Opens) (h : V ≤ U) : Γ(Y, V) :=
  ((tensorPowerFrame Y H U (productFrame m μ ν) n).equiv V h).symm
    (e.hom.app V ((tensorPowerFrame Y B U ν n).equiv V h 1))

lemma normalizationCoefficient_unit {U : Y.Opens}
    (μ : LocalFrame Y M U) (ν : LocalFrame Y B U) (V : Y.Opens) (h : V ≤ U) :
    IsUnit (normalizationCoefficient n m e μ ν V h) := by
  exact (transitionUnit
    ((tensorPowerFrame Y H U (productFrame m μ ν) n).equiv V h)
    (((tensorPowerFrame Y B U ν n).equiv V h).trans
      (lineIsoSectionsLinearEquiv e V))).isUnit

/-- Local normalized section, constructed from the two actual frames. -/
def normalizedLocal {U : Y.Opens} (μ : LocalFrame Y M U) (ν : LocalFrame Y B U) :
    Γ(tensorPower Y M n, U) :=
  (tensorPowerFrame Y M U μ n).equiv U le_rfl
    (normalizationCoefficient n m e μ ν U le_rfl)

lemma normalizationCoefficient_restrict {U : Y.Opens}
    (μ : LocalFrame Y M U) (ν : LocalFrame Y B U)
    (V W : Y.Opens) (hWV : W ≤ V) (hVU : V ≤ U) :
    Y.presheaf.map (homOfLE hWV).op (normalizationCoefficient n m e μ ν V hVU) =
      normalizationCoefficient n m e μ ν W (hWV.trans hVU) := by
  unfold normalizationCoefficient
  rw [← ArithmeticThetaGlobalization.frame_coordinate_restrict]
  rw [hom_restrict]
  rw [(tensorPowerFrame Y B U ν n).naturality V W hWV hVU 1, map_one]

lemma normalizedLocal_restrict {U : Y.Opens}
    (μ : LocalFrame Y M U) (ν : LocalFrame Y B U) (V : Y.Opens) (h : V ≤ U) :
    (tensorPower Y M n).presheaf.map (homOfLE h).op (normalizedLocal n m e μ ν) =
      (tensorPowerFrame Y M U μ n).equiv V h
        (normalizationCoefficient n m e μ ν V h) := by
  unfold normalizedLocal
  rw [(tensorPowerFrame Y M U μ n).naturality U V h le_rfl,
    normalizationCoefficient_restrict]

/-- Normalization is an identity for every frame of M and every local
section of B, so it will descend without any chosen global Hodge frame. -/
def Normalizes (U : Y.Opens) (d : Γ(tensorPower Y M n, U)) : Prop :=
  ∀ (V : Y.Opens) (hVU : V ≤ U) (ζ : LocalFrame Y M V) (b : Γ(B, V)),
    e.hom.app V (tensorPowerSection Y B n V b) =
      ((tensorPowerFrame Y M V ζ n).equiv V le_rfl).symm
        ((tensorPower Y M n).presheaf.map (homOfLE hVU).op d) •
      tensorPowerSection Y H n V
        (m.hom.app V (tensorSection Y M B V (ζ.equiv V le_rfl 1) b))

lemma normalizedLocal_spec {U : Y.Opens}
    (μ : LocalFrame Y M U) (ν : LocalFrame Y B U) :
    Normalizes n m e U (normalizedLocal n m e μ ν) := by
  intro V h ζ b
  let a := (μ.equiv V h).symm (ζ.equiv V le_rfl 1)
  let c := (ν.equiv V h).symm b
  let q := normalizationCoefficient n m e μ ν V h
  let μn := (tensorPowerFrame Y M U μ n).equiv V h
  let ζn := (tensorPowerFrame Y M V ζ n).equiv V le_rfl
  let hn := (tensorPowerFrame Y H U (productFrame m μ ν) n).equiv V h
  have hμ : μ.equiv V h a = ζ.equiv V le_rfl 1 := LinearEquiv.apply_symm_apply _ _
  have hν : ν.equiv V h c = b := LinearEquiv.apply_symm_apply _ _
  have hz : ζn 1 = μn (a ^ n) := by
    have h₁ := tensorPowerSection_frame Y M V ζ n V le_rfl 1
    have h₂ := tensorPowerSection_frame Y M U μ n V h a
    rw [hμ] at h₂
    simpa only [one_pow] using h₁.symm.trans h₂
  have hzall (r : Γ(Y,V)) : ζn r = μn (a ^ n * r) := by
    calc
      ζn r = r • ζn 1 := by simpa using (ζn.map_smul r 1)
      _ = μn (a ^ n * r) := by rw [hz, ← μn.map_smul]; congr 1; exact mul_comm _ _
  have hq : q = a ^ n * ζn.symm (μn q) := by
    apply μn.injective
    rw [← hzall, LinearEquiv.apply_symm_apply]
  have hec : e.hom.app V (tensorPowerSection Y B n V b) = hn (q * c ^ n) := by
    rw [← hν, tensorPowerSection_frame]
    have hbpow : (tensorPowerFrame Y B U ν n).equiv V h (c ^ n) =
        c ^ n • (tensorPowerFrame Y B U ν n).equiv V h 1 := by
      simpa using ((tensorPowerFrame Y B U ν n).equiv V h).map_smul (c ^ n) 1
    rw [hbpow, Scheme.Modules.Hom.app_smul]
    have he1 : e.hom.app V ((tensorPowerFrame Y B U ν n).equiv V h 1) = hn q :=
      (hn.apply_symm_apply _).symm
    rw [he1, ← hn.map_smul]
    congr 1
    exact mul_comm _ _
  have hprod : tensorPowerSection Y H n V
      (m.hom.app V (tensorSection Y M B V (ζ.equiv V le_rfl 1) b)) = hn ((a*c)^n) := by
    rw [← hμ, ← hν, productFrame_apply, tensorPowerSection_frame]
  rw [normalizedLocal_restrict, hec, hprod]
  change hn (q * c ^ n) = ζn.symm (μn q) • hn ((a*c)^n)
  rw [← hn.map_smul]
  apply hn.congr_arg
  change q * c ^ n = ζn.symm (μn q) * (a*c)^n
  rw [mul_pow]
  calc
    q * c ^ n = (a ^ n * ζn.symm (μn q)) * c ^ n := congrArg (· * c ^ n) hq
    _ = ζn.symm (μn q) * (a ^ n * c ^ n) := by ring

lemma normalizes_restrict {U V : Y.Opens} (h : V ≤ U)
    (d : Γ(tensorPower Y M n, U)) (hd : Normalizes n m e U d) :
    Normalizes n m e V ((tensorPower Y M n).presheaf.map (homOfLE h).op d) := by
  intro W hWV ζ b
  convert hd W (hWV.trans h) ζ b using 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma normalizes_ext {U : Y.Opens} (μ : LocalFrame Y M U) (ν : LocalFrame Y B U)
    (d d' : Γ(tensorPower Y M n, U))
    (hd : Normalizes n m e U d) (hd' : Normalizes n m e U d') : d = d' := by
  have ha := hd U le_rfl μ (ν.equiv U le_rfl 1)
  have hb := hd' U le_rfl μ (ν.equiv U le_rfl 1)
  have h := ha.symm.trans hb
  have hid (z : Γ(tensorPower Y M n, U)) :
      (tensorPower Y M n).presheaf.map (homOfLE (le_refl U)).op z = z := by
    change ((tensorPower Y M n).presheaf.map (𝟙 (Opposite.op U))) z = z
    exact ConcreteCategory.congr_hom ((tensorPower Y M n).presheaf.map_id _) z
  rw [hid, hid] at h
  have hp : tensorPowerSection Y H n U
      (m.hom.app U (tensorSection Y M B U (μ.equiv U le_rfl 1) (ν.equiv U le_rfl 1))) =
      (tensorPowerFrame Y H U (productFrame m μ ν) n).equiv U le_rfl 1 := by
    rw [productFrame_apply, tensorPowerSection_frame]
    simp
  rw [hp] at h
  let f := (tensorPowerFrame Y H U (productFrame m μ ν) n).equiv U le_rfl
  have hscalar (r : Γ(Y,U)) : r • f 1 = f r := by
    simpa using (f.map_smul r 1).symm
  change _ • f 1 = _ • f 1 at h
  rw [hscalar, hscalar] at h
  exact ((tensorPowerFrame Y M U μ n).equiv U le_rfl).symm.injective (f.injective h)

lemma powerFrame_restrict_equiv {P : Y.Modules} {U V : Y.Opens}
    (μ : LocalFrame Y P U) (h : V ≤ U) (W : Y.Opens) (hWV : W ≤ V) :
    (tensorPowerFrame Y P V (ArithmeticThetaGlobalization.restrictFrame μ V h) n).equiv W hWV =
      (tensorPowerFrame Y P U μ n).equiv W (hWV.trans h) := by
  let f := (tensorPowerFrame Y P V (ArithmeticThetaGlobalization.restrictFrame μ V h) n).equiv W hWV
  let g := (tensorPowerFrame Y P U μ n).equiv W (hWV.trans h)
  have h1 : f 1 = g 1 := by
    have h₁ := tensorPowerSection_frame Y P V (ArithmeticThetaGlobalization.restrictFrame μ V h) n W hWV 1
    have h₂ := tensorPowerSection_frame Y P U μ n W (hWV.trans h) 1
    simpa only [one_pow] using h₁.symm.trans h₂
  apply LinearEquiv.ext
  intro r
  calc
    f r = r • f 1 := by simpa using f.map_smul r 1
    _ = r • g 1 := by rw [h1]
    _ = g r := by simpa using (g.map_smul r 1).symm

/-- Local normalization descends to the global section, using the sheaf
axiom and the actual naturality of every tensor and multiplication map. -/
lemma normalizes_of_cover {ι : Type} (U : ι → Y.Opens)
    (hU : (⊤ : Y.Opens) ≤ iSup U) (d : Γ(tensorPower Y M n, ⊤))
    (hd : ∀ i, Normalizes n m e (U i)
      ((tensorPower Y M n).presheaf.map (homOfLE le_top).op d)) :
    Normalizes n m e ⊤ d := by
  intro V hV ζ b
  apply (tensorPower Y H n).isSheaf.section_ext
  intro y hy
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU (show y ∈ (⊤ : Y.Opens) by trivial))
  let W := V ⊓ U i
  let ζW := ArithmeticThetaGlobalization.restrictFrame ζ W inf_le_left
  have hloc := hd i W inf_le_right ζW (B.presheaf.map (homOfLE inf_le_left).op b)
  refine ⟨W, inf_le_left, ⟨hy, hi⟩, ?_⟩
  rw [hom_restrict, tensorPowerSection_restrict, Scheme.Modules.map_smul,
    tensorPowerSection_restrict, hom_restrict, tensorSection_restrict]
  have hζ : M.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op (ζ.equiv V le_rfl 1) =
      ζW.equiv W le_rfl 1 := by
    rw [ζ.naturality, map_one]
    rfl
  rw [hζ]
  have hcoord : Y.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op
      (((tensorPowerFrame Y M V ζ n).equiv V le_rfl).symm
        ((tensorPower Y M n).presheaf.map (homOfLE hV).op d)) =
    ((tensorPowerFrame Y M W ζW n).equiv W le_rfl).symm
      ((tensorPower Y M n).presheaf.map (homOfLE (inf_le_right : W ≤ U i)).op
        ((tensorPower Y M n).presheaf.map (homOfLE le_top).op d)) := by
    rw [← ArithmeticThetaGlobalization.frame_coordinate_restrict]
    dsimp only [ζW]
    rw [powerFrame_restrict_equiv]
    congr 1
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hcoord]
  exact hloc

/-- A power comparison divided by a line multiplication gives an everywhere
unit section. The construction is independent of every local frame choice. -/
theorem normalized_section_exists (hM : IsLineBundle Y M) (hB : IsLineBundle Y B) :
    ∃ d : Γ(tensorPower Y M n, ⊤),
      ArithmeticThetaRootTorsor.IsGeneratingSection Y (tensorPower Y M n) d ∧
      Normalizes n m e ⊤ d := by
  classical
  have hc : ∀ y : Y, ∃ (U : Y.Opens), y ∈ U ∧
      Nonempty (LocalFrame Y M U) ∧ Nonempty (LocalFrame Y B U) := by
    intro y
    obtain ⟨U, hyU, ⟨μ⟩⟩ := hM y
    obtain ⟨V, hyV, ⟨ν⟩⟩ := hB y
    exact ⟨U ⊓ V, ⟨hyU, hyV⟩,
      ⟨ArithmeticThetaGlobalization.restrictFrame (localFrameOfIso Y M U μ) _ inf_le_left⟩,
      ⟨ArithmeticThetaGlobalization.restrictFrame (localFrameOfIso Y B V ν) _ inf_le_right⟩⟩
  choose U hy hμ hν using hc
  let μ (y : Y) := Classical.choice (hμ y)
  let ν (y : Y) := Classical.choice (hν y)
  let t (y : Y) := normalizedLocal n m e (μ y) (ν y)
  have cover : (⊤ : Y.Opens) ≤ iSup U := fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
  have compat (i j : Y) :
      (tensorPower Y M n).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (t i) =
      (tensorPower Y M n).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (t j) := by
    apply normalizes_ext n m e
      (ArithmeticThetaGlobalization.restrictFrame (μ i) _ inf_le_left)
      (ArithmeticThetaGlobalization.restrictFrame (ν i) _ inf_le_left)
    · exact normalizes_restrict n m e _ _ (normalizedLocal_spec n m e _ _)
    · exact normalizes_restrict n m e _ _ (normalizedLocal_spec n m e _ _)
  obtain ⟨d, hd, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(tensorPower Y M n).presheaf, (tensorPower Y M n).isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) cover t compat
  refine ⟨d, ?_, normalizes_of_cover n m e U cover d (fun i => ?_)⟩
  · intro y
    refine ⟨U y, hy y, tensorPowerFrame Y M (U y) (μ y) n, ?_⟩
    rw [hd y]
    change IsUnit (((tensorPowerFrame Y M (U y) (μ y) n).equiv (U y) le_rfl).symm
      ((tensorPowerFrame Y M (U y) (μ y) n).equiv (U y) le_rfl _))
    rw [LinearEquiv.symm_apply_apply]
    exact normalizationCoefficient_unit n m e _ _ _ _
  · rw [hd i]
    exact normalizedLocal_spec n m e _ _

end Normalize

#print axioms discriminant_comparison
#print axioms inverse_of_effective_section
#print axioms twist_line_exists
end ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTwistUnitR0185

namespace ArithmeticThetaCommonHalfHodgeR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor
open ArithmeticThetaSectionOrder ArithmeticThetaDegreeAssembly
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184
open DiscriminantTwistUnitR0185

/-- The normalized discriminant is an everywhere generating section of the
actual inverse-divisor twist, with its exact framewise multiplication law. -/
theorem discriminant_twist_unit :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L →
    ∀ (D : LevelData k L) (X : Compactification k L D) (x : X.space)
      (H : Extension k L D X), Canonical k L H →
    ∀ (s : (tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)),
      IsCompactD2 k L D X H s →
    ∀ (A : DivisorLine (Component k L D X x)), IsCuspHalfLine k L D X x A →
    ∃ W : Twist k L D X x A H, IsTwist k L D X x s W := by
  intro k _ _ _ L hL h24 D X x H hH s hs A hA
  obtain ⟨e, he⟩ := discriminant_comparison k L hL h24 D X x H hH s hs A hA
  obtain ⟨M, hM, ⟨m⟩⟩ := twist_line_exists k L hL h24 D X x H A hA
  have hlev : 3 ≤ L := by obtain ⟨n, rfl⟩ := h24; omega
  have heven : Even L := by obtain ⟨n, rfl⟩ := h24; exact ⟨12 * n, by omega⟩
  have hg := component_curve_frames k L hlev heven D X x
  obtain ⟨CM⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible _ hg.2.2.2.1 M hM
  obtain ⟨E, ⟨_, _, ⟨ι, ⟨CA⟩⟩, _⟩, _⟩ := hA
  obtain ⟨d, hd, hn⟩ := normalized_section_exists 24 m e
    (isLineBundle_of_normalFrameCover _ M CM) (tensorPower_isLineBundle _ _ CA 2)
  refine ⟨⟨M, m, d⟩, hM, hd, ?_⟩
  intro U μ
  have heU := congrArg ((power k L D X x H 24).presheaf.map
    (homOfLE (show U ≤ ⊤ from le_top)).op) he
  rw [hom_restrict, tensorPowerSection_restrict, tensorPowerSection_restrict] at heU
  exact heU.symm.trans (hn U le_top μ
    (tensorPowerSection (Component k L D X x) A.line 2 U
      (A.line.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op A.section_)))

#print axioms discriminant_twist_unit
end ArithmeticThetaCommonHalfHodgeR0185
