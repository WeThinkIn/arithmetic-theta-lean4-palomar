module

public import IndexedFullUnaryFactorizationR0188
public import CuspHalfLineCoverDegreeR0188

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaLatticeSectionsR0188
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaPullback
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaRelativeDiscriminantR0171
open HodgeBaseChange ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
namespace MatrixFamilyGlobalSectionsR0188

/-- Tensor comparison coherence for the actual composite pullback. -/
lemma comparison_comp {Y Z W : Scheme.{0}} (r : Z ⟶ Y) (g : W ⟶ Z)
    (f : W ⟶ Y) (hf : g ≫ r = f) (M : Y.Modules) (B : Z.Modules)
    (hM : Scheme.Modules.IsInvertible M) (a : (Scheme.Modules.pullback r).obj M ≅ B)
    (n : ℕ) :
    let E := ((Scheme.Modules.pullback g).mapIso a).symm ≪≫ along g r f hf M
    (Scheme.Modules.pullback g).map (tensorComparison r M B a n).hom ≫
        (tensorComparison g B ((Scheme.Modules.pullback f).obj M) E n).hom =
      (along g r f hf (tensorPower Y M n)).hom ≫
        (pullback_tensorPower_iso W Y f M n).hom := by
  subst f
  dsimp only
  let E := ((Scheme.Modules.pullback g).mapIso a).symm ≪≫ along g r (g ≫ r) rfl M
  have he : composeComparison r g (g ≫ r) rfl M B
      ((Scheme.Modules.pullback (g ≫ r)).obj M) a E = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, E, along, pullbackEqIso, Scheme.Modules.pullbackCongr,
      Category.assoc, ← Functor.map_comp]
  have ht := tensorComparison_comp r g M B ((Scheme.Modules.pullback (g ≫ r)).obj M)
    hM a E n
  rw [he, tensorComparison_refl _ _ hM] at ht
  have hh := congrArg Iso.hom ht
  have hh' := congrArg (fun z => (along g r (g ≫ r) rfl (tensorPower Y M n)).hom ≫ z) hh
  simpa [composeComparison, E, along, pullbackEqIso, Scheme.Modules.pullbackCongr,
    Category.assoc] using hh'.symm

/-- The square-Hodge map and disk frame commute with the same cover composite. -/
lemma square_comparison (k : Type) [Field k] {Y Z X : Scheme.{0}}
    (r : Z ⟶ Y) (p : Y ⟶ X) (M : Y.Modules) (B : Z.Modules) (H : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (a : (Scheme.Modules.pullback r).obj M ≅ B)
    (β : tensorPower Y M 2 ≅ (Scheme.Modules.pullback p).obj H)
    (g : Disk k ⟶ Z) (f : Disk k ⟶ Y) (hf : g ≫ r = f)
    (d : Disk k ⟶ X) (hd : f ≫ p = d) (hg : g ≫ (r ≫ p) = d) :
    let E := ((Scheme.Modules.pullback g).mapIso a).symm ≪≫ along g r f hf M
    let β' := (tensorComparison r M B a 2).symm ≪≫
      (Scheme.Modules.pullback r).mapIso β ≪≫ along r p (r ≫ p) rfl H
    squareOnDisk k (r ≫ p) B H β' g d hg =
      powerCongr (Disk k) E 2 ≪≫ squareOnDisk k p M H β f d hd := by
  dsimp only
  let E := ((Scheme.Modules.pullback g).mapIso a).symm ≪≫ along g r f hf M
  have ht := comparison_comp r g f hf M B hM a 2
  dsimp only at ht
  have ht' : (Scheme.Modules.pullback g).map (tensorComparison r M B a 2).inv ≫
      (along g r f hf (tensorPower Y M 2)).hom =
      (tensorComparison g B ((Scheme.Modules.pullback f).obj M) E 2).hom ≫
        (pullback_tensorPower_iso (Disk k) Y f M 2).inv := by
    apply (cancel_mono (pullback_tensorPower_iso (Disk k) Y f M 2).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← ht]
    simp [E, ← Functor.map_comp, Category.assoc]
  have hc := ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.compIso_assoc
    g r p f (r ≫ p) d hf rfl hd hg H
  have hn := ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.compIso_naturality
    g r f hf β.hom
  change (Scheme.Modules.pullback g).map (along r p (r ≫ p) rfl H).hom ≫
    (along g (r ≫ p) d hg H).hom =
    (along g r f hf ((Scheme.Modules.pullback p).obj H)).hom ≫
      (along f p d hd H).hom at hc
  change (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback r).map β.hom) ≫
    (along g r f hf ((Scheme.Modules.pullback p).obj H)).hom =
    (along g r f hf (tensorPower Y M 2)).hom ≫
      (Scheme.Modules.pullback f).map β.hom at hn
  apply Iso.ext
  simp only [squareOnDisk, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc _ _ (along f p d hd H).hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc _ (along g r f hf (tensorPower Y M 2)).hom, ht']
  simp [tensorComparison, E, Category.assoc]

/-- Products of coordinates in the single actual frame. -/
lemma product_frame {Y : Scheme} (M : Y.Modules) (e : Sections Y M)
    (he : IsFrame M ⊤ e) (n : ℕ) (a : Fin n → Γ(Y, ⊤)) :
    tensorProductSection Y M n ⊤ (fun j => a j • e) =
      (∏ j, a j) • tensorPowerSection Y M n ⊤ e := by
  let F := InitialHodgeSection.frame M e he
  have h := tensorProductSection_frame Y M ⊤ F n ⊤ le_rfl a
  have h1 := tensorProductSection_frame Y M ⊤ F n ⊤ le_rfl (fun _ => 1)
  simp only [Finset.prod_const_one, tensorProductSection_diagonal] at h1
  change tensorPowerSection Y M n ⊤ (F.equiv ⊤ le_rfl 1) = _ at h1
  have hf : ∀ c, F.equiv ⊤ le_rfl c = c • e := by
    intro c
    simp [F, InitialHodgeSection.frame, InitialHodgeSection.res_self]
  rw [hf] at h1
  simp only [one_smul] at h1
  simp only [hf] at h
  rw [h1, ← map_smul, smul_eq_mul, mul_one]
  exact h

/-- Structural complex scalars and all coset products have the full disk expansion. -/
lemma linear_expansion {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    (hformal : FormalIdentity A U) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (CommRingCat.of ℂ)) (g : Disk ℂ ⟶ Y)
    (hgb : g ≫ b = diskStructure ℂ) (M : Y.Modules)
    (e : Sections (Disk ℂ) ((Scheme.Modules.pullback g).obj M))
    (he : IsFrame _ ⊤ e) (t : Fin U.count → Sections Y M)
    (ht : ∀ j, pullbackGlobalSection g M (t j) =
      scalar (PowerSeries ℂ) (unarySeries ℂ (commonN A) (U.pair j).1 (U.pair j).2) • e)
    (c : Fin h → ℂ) :
    pullbackPowerSection g M n
      (∑ i : Fin h, baseScalar ℂ b (c i) • ∑ a : Cosets A i,
        tensorProductSection Y M n ⊤ (fun j => t (U.index i a j))) =
      scalar (PowerSeries ℂ) (expanded A c) •
        tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj M) n ⊤ e := by
  classical
  have hp (a : Γ(Y, ⊤)) (v : Sections Y (tensorPower Y M n)) :
      pullbackPowerSection g M n (a • v) =
        g.appTop a • pullbackPowerSection g M n v := by
    unfold pullbackPowerSection pullbackGlobalSection
    rw [((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (tensorPower Y M n)).app_smul]
    exact Scheme.Modules.Hom.app_smul _ _ _
  have hc (z : ℂ) : g.appTop (baseScalar ℂ b z) =
      scalar (PowerSeries ℂ) (PowerSeries.C z) := by
    change (g ≫ b).appTop (scalar ℂ z) = _
    rw [hgb]
    exact GlobalFamilyTorsionValueR0180.scalar_natural (algebraMap ℂ (PowerSeries ℂ)) z
  have hs {ι : Type} [Fintype ι] (v : ι → Sections Y (tensorPower Y M n)) :
      pullbackPowerSection g M n (∑ i, v i) = ∑ i, pullbackPowerSection g M n (v i) := by
    simp only [pullbackPowerSection, pullbackGlobalSection, map_sum]
  rw [hs]
  simp only [hp, hc, hs]
  have hprod (i : Fin h) (a : Cosets A i) :
      pullbackPowerSection g M n (tensorProductSection Y M n ⊤ (fun j => t (U.index i a j))) =
      scalar (PowerSeries ℂ) (∏ j : Fin n,
        unarySeries ℂ (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2) •
        tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj M) n ⊤ e := by
    rw [pullbackPowerSection, pullback_tensorProduct_section]
    simp only [ht]
    change tensorProductSection (Disk ℂ) ((Scheme.Modules.pullback g).obj M) n ⊤
      (fun j => scalar (PowerSeries ℂ)
        (unarySeries ℂ (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2) • e) = _
    rw [product_frame _ e he]
    simp only [scalar, map_prod]
  simp only [hprod, ← Finset.sum_smul, smul_smul]
  rw [hformal c]
  simp only [PowerSeries.smul_eq_C_mul, scalar, map_sum, map_mul, Finset.sum_smul]


end MatrixFamilyGlobalSectionsR0188
open MatrixFamilyGlobalSectionsR0188
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185

/-- Actual matrix theta sections, in one common tensor line and normalized disk frame. -/
theorem matrix_family_global_sections :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) →∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H → ∀ (d2 : ArithmeticThetaSimultaneousUnaryR0187.Sections X.space (ArithmeticThetaTensorPower.tensorPower X.space H.line 24)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X H d2 → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (ζ : ℂ), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) → ArithmeticThetaTateCuspsR0181.CanonicalMarking ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ζ V.level → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by
  intro n h hn hh A hA D X H hH d2 hd2 V ζ hζ hmark
  classical
  obtain ⟨hN, hNeven, hnorm, U, hU, hpairs, hformal⟩ :=
    indexed_full_unary_factorization n h hn hh A hA
  refine ⟨U, hU, hformal, ?_⟩
  obtain ⟨f, hf, J, hJ, C, hC, g, hg, hgp, η, hη, u, hu, hcanonical,
      hsquare, F, hF, R, hR, hdegree⟩ :=
    simultaneous_unary_common_cover ℂ (commonN A) U.count hN hNeven
      (fun j => (U.pair j).1) (fun j => (U.pair j).2) hpairs D X H hH d2 hd2 V ζ hζ hmark
  obtain ⟨q, hq, hdom, t, ht⟩ := hR
  let x := V.disk (closedPoint ℂ)
  let L := ArithmeticThetaCompactUnaryR0183.level (commonN A)
  letI := C.integral
  letI := C.finite
  letI := C.etale
  letI := C.surjective
  letI := R.integral
  letI := R.finite
  letI := R.flat
  letI := R.surjective
  let R' : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x)
      (24 * (exponent (commonN A))^U.count) := {
    space := R.space
    map := R.map ≫ C.map
    integral := R.integral
    finite := inferInstance
    flat := inferInstance
    surjective := inferInstance
    proper := by simpa only [Category.assoc] using R.proper
    smooth := by simpa only [Category.assoc] using R.smooth
    degree := hdegree }
  have hqd : q ≫ (R'.map ≫ inclusion ℂ L D X x) = V.disk := by
    change q ≫ ((R.map ≫ C.map) ≫ inclusion ℂ L D X x) = _
    rw [Category.assoc, ← Category.assoc q, hq, hgp]
  have hqb : q ≫ (R'.map ≫ projection ℂ L D X x) = diskStructure ℂ := by
    change q ≫ (R'.map ≫ (inclusion ℂ L D X x ≫ X.projection)) = _
    rw [← Category.assoc R'.map, ← Category.assoc q, hqd]
    exact V.extends_eq.1
  let M := (Scheme.Modules.pullback C.map).obj J.line
  have hM : Scheme.Modules.IsInvertible M := hJ.choose_spec.1.1.pullback C.map
  let a : (Scheme.Modules.pullback R.map).obj M ≅ coverLine J R' :=
    along R.map C.map R'.map rfl J.line
  let E : (Scheme.Modules.pullback q).obj (coverLine J R') ≅
      (Scheme.Modules.pullback g).obj M :=
    ((Scheme.Modules.pullback q).mapIso a).symm ≪≫ along q R.map g hq M
  let e := E.inv.app ⊤ u
  have he : E.hom.app ⊤ e = u := iso_inv_hom_apply E.symm ⊤ u
  have hframe : IsFrame _ ⊤ e := frame_iso E.symm u hu
  let β : tensorPower R'.space (coverLine J R') 2 ≅
      (Scheme.Modules.pullback (R'.map ≫ inclusion ℂ L D X x)).obj H.line :=
    (tensorComparison R.map M (coverLine J R') a 2).symm ≪≫
      (Scheme.Modules.pullback R.map).mapIso (halfSquare ℂ L C) ≪≫
      along R.map (C.map ≫ inclusion ℂ L D X x)
        (R'.map ≫ inclusion ℂ L D X x) (by simp [R', Category.assoc]) H.line
  have hs : (squareOnDisk ℂ (R'.map ≫ inclusion ℂ L D X x) (coverLine J R') H.line
      β q V.disk hqd).hom.app ⊤
      (tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback q).obj (coverLine J R')) 2 ⊤ e) = η := by
    have hc := square_comparison ℂ R.map (C.map ≫ inclusion ℂ L D X x)
      M (coverLine J R') H.line hM a (halfSquare ℂ L C) q g hq V.disk hgp
      (by simpa only [R', Category.assoc] using hqd)
    change squareOnDisk ℂ (R'.map ≫ inclusion ℂ L D X x) (coverLine J R') H.line
      β q V.disk hqd = powerCongr (Disk ℂ) E 2 ≪≫
        squareOnDisk ℂ (C.map ≫ inclusion ℂ L D X x) M H.line
          (halfSquare ℂ L C) g V.disk hgp at hc
    rw [hc]
    change (squareOnDisk ℂ (C.map ≫ inclusion ℂ L D X x) M H.line
      (halfSquare ℂ L C) g V.disk hgp).hom.app ⊤
      ((powerCongr (Disk ℂ) E 2).hom.app ⊤ (tensorPowerSection _ _ 2 ⊤ e)) = η
    rw [powerCongr_section, he]
    exact hsquare
  let t' : Fin U.count → Sections R'.space (coverLine J R') := fun j => a.hom.app ⊤ (t j)
  have ht' : ∀ j, t' j ≠ 0 ∧ pullbackGlobalSection q (coverLine J R') (t' j) =
      scalar (PowerSeries ℂ) (unarySeries ℂ (commonN A) (U.pair j).1 (U.pair j).2) • e := by
    intro j
    constructor
    · intro hz
      apply (ht j).1
      have hz' := congrArg (fun v => a.inv.app ⊤ v) hz
      simpa only [t', iso_inv_hom_apply, map_zero] using hz'
    · have hv : E.hom.app ⊤ (pullbackGlobalSection q (coverLine J R') (t' j)) =
          scalar (PowerSeries ℂ) (unarySeries ℂ (commonN A) (U.pair j).1 (U.pair j).2) • u := by
        dsimp only [t']
        rw [pullback_global_app]
        change (along q R.map g hq M).hom.app ⊤
          (((Scheme.Modules.pullback q).mapIso a).inv.app ⊤
            (((Scheme.Modules.pullback q).mapIso a).hom.app ⊤ _)) = _
        rw [iso_inv_hom_apply]
        exact (ht j).2.2
      have hv' := congrArg (fun v => E.inv.app ⊤ v) hv
      simpa only [iso_inv_hom_apply, Scheme.Modules.Hom.app_smul] using hv'
  let σ : Fin h → Sections R'.space (tensorPower R'.space (coverLine J R') n) :=
    fun i => ∑ a : Cosets A i, tensorProductSection R'.space (coverLine J R') n ⊤
      (fun j => t' (U.index i a j))
  have hL : 0 < L := by dsimp [L, ArithmeticThetaCompactUnaryR0183.level]; positivity
  have h24 : 24 ∣ L := dvd_mul_right 24 _
  refine ⟨J, hJ, R', cusp_half_line_cover_degree ℂ L hL h24 D X x J hJ _ n R',
    q, hqd, hdom, β, η, e, hη, hframe, hs, t', σ, ht', (fun _ => rfl), ?_⟩
  intro c
  exact linear_expansion A U hformal (R'.map ≫ projection ℂ L D X x) q hqb
    (coverLine J R') e hframe t' (fun j => (ht' j).2) c

#print axioms matrix_family_global_sections

end ArithmeticThetaLatticeSectionsR0188
