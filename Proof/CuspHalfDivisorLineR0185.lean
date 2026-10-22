module

public import CommonHalfHodgeDefinitionsR0185
public import EffectiveDivisorLine
public import ComponentDiscriminantDivisorR0184

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
namespace ArithmeticThetaCommonHalfHodgeR0185
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaRelativeDiscriminantR0171
open CompactHodgeLatticeExtensionR0182

namespace CuspHalfDivisorLineR0185
attribute [local instance] Classical.propDecidable

lemma invertible_of_lineBundle (Y : Scheme) (M : Y.Modules) (hM : IsLineBundle Y M) :
    Scheme.Modules.IsInvertible M := by
  constructor
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hM y
  exact ⟨U, hy, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (frameRestrictIso Y M U (localFrameOfIso Y M U e)).symm⟩⟩

variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

lemma cusp_coheight (hL : 3 ≤ L) (heven : Even L)
    (y : Component k L D X x) (hy : y ∈ cuspSet k L D X x) :
    Order.coheight y = 1 := by
  letI := X.openImmersion
  letI := (component_curve_frames k L hL heven D X x).2.1
  apply ArithmeticThetaGeometricNormR0150.NormOrders.smooth_coheight_one_of_ne_generic
    k (projection k L D X x)
  intro heq
  have hgen : genericPoint (Component k L D X x) ∈
      inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange :=
    ((genericPoint_spec (Component k L D X x)).mem_open_set_iff
      (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange).isOpen).mpr
        (by simpa using ComponentDiscriminantDivisorR0184.component_interior_nonempty k L D X x)
  rw [← heq] at hgen
  exact hy hgen

/-- The finite divisor is supported on the actual reduced cusp locus. -/
def halfDivisor : Component k L D X x →₀ ℤ := by
  classical
  exact Finsupp.onFinset
    (ComponentDiscriminantDivisorR0184.cuspSet_finite k L D X x).toFinset
    (fun y => if y ∈ cuspSet k L D X x then ((L / 24 : ℕ) : ℤ) else 0)
    (by intro y hy; simpa using (show y ∈ cuspSet k L D X x from by
      by_contra hn; simp [hn] at hy))

omit [IsAlgClosed k] in
lemma halfDivisor_apply (y : Component k L D X x) :
    halfDivisor k L D X x y =
      if y ∈ cuspSet k L D X x then ((L / 24 : ℕ) : ℤ) else 0 := by
  classical
  rfl

/-- The accepted effective-divisor construction, with all-frame order invariance. -/
lemma exists_cusp_half_line (hL : 3 ≤ L) (heven : Even L) :
    ∃ A : DivisorLine (Component k L D X x), IsCuspHalfLine k L D X x A := by
  classical
  let Y := Component k L D X x
  let E := halfDivisor k L D X x
  have hg := component_curve_frames k L hL heven D X x
  have hE : ∀ y, 0 ≤ E y := by
    intro y
    dsimp [E]
    rw [halfDivisor_apply]
    split_ifs <;> positivity
  have hc : ∀ y, E y ≠ 0 → Order.coheight y = 1 := by
    intro y hy
    apply cusp_coheight k L D X x hL heven y
    by_contra hn
    exact hy (by simp [E, halfDivisor_apply, hn])
  obtain ⟨M, hM, ι, C, s, hs, hCs⟩ :=
    ArithmeticThetaGeometricPrerequisites.effective_divisor_line_realization
      Y hg.2.2.1 hg.2.2.2.1 E hE hc
  refine ⟨⟨M, s⟩, E, ⟨invertible_of_lineBundle Y M hM, hs, ⟨ι, ⟨C⟩⟩, ?_⟩, ?_⟩
  · intro κ B j y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (Set.mem_univ y))
    exact (hCs i y hi).trans
      (ArithmeticThetaDegreeAssembly.section_order_frame_invariant
        Y M (C.opens i) (B.opens j) (C.frame i) (B.frame j) s y hi hy)
  · intro y
    constructor <;> intro hy <;> simp [E, halfDivisor_apply, hy]

omit [IsAlgClosed k] in
/-- The specified completion retains orders after factoring through the component. -/
lemma component_disk_order (hL : 3 ≤ L) (heven : Even L)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk)
    (a : (Component k L D X x).presheaf.stalk (f (closedPoint k))) :
    ((Scheme.stalkClosedPointTo f).hom a).order =
      Ring.ord ((Component k L D X x).presheaf.stalk (f (closedPoint k))) a := by
  let p := inclusion k L D X x
  have ho : ∀ b : X.space.presheaf.stalk ((f ≫ p) (closedPoint k)),
      ((Scheme.stalkClosedPointTo (f ≫ p)).hom b).order =
        Ring.ord (X.space.presheaf.stalk ((f ≫ p) (closedPoint k))) b := by
    change ∀ b : X.space.presheaf.stalk ((f ≫ inclusion k L D X x) (closedPoint k)), _
    rw [hf]
    exact disk_localMap_order k L hL heven D X V
  let e := (asIso (p.stalkMap (f (closedPoint k)))).commRingCatIsoToRingEquiv
  have h := ho (e.symm a)
  rw [Scheme.stalkClosedPointTo_comp] at h
  change ((Scheme.stalkClosedPointTo f).hom (e (e.symm a))).order = _ at h
  rw [e.apply_symm_apply] at h
  exact h.trans (ArithmeticThetaGeometricNormR0150.NormOrders.ord_ringEquiv e.symm a).symm


lemma frame_generator (Y : Scheme) (M : Y.Modules) (U : Y.Opens)
    (e : LocalFrame Y M U) : IsFrame M U (e.equiv U le_rfl 1) := by
  intro W h
  have hr : res M h (e.equiv U le_rfl 1) = e.equiv W h 1 := by
    simpa only [res, map_one] using e.naturality U W h le_rfl 1
  rw [hr]
  simpa only [← map_smul, smul_eq_mul, mul_one] using (e.equiv W h).bijective

lemma lineBundle_of_cover (Y : Scheme) (M : Y.Modules) (ι : Type)
    (C : NormalFrameCover Y M ι) : IsLineBundle Y M := by
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (Set.mem_univ y))
  exact ⟨C.opens i, hi, ⟨localFrameIso Y M _ (C.frame i)⟩⟩

omit [CharZero k] [IsAlgClosed k] in
lemma series_factor (q : PowerSeries k) (n : ℕ) (hn : 0 < n)
    (hq : q.order.toNat = n) : ∃ u : (PowerSeries k)ˣ,
      q = PowerSeries.X ^ n * (u : PowerSeries k) := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
    omega
  refine ⟨PowerSeries.Unit_of_divided_by_X_pow_order q, ?_⟩
  rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hq0, ← hq]
  exact (PowerSeries.X_pow_order_mul_divXPowOrder (f := q)).symm


/-- Complete-disk normalization for the actual represented cusp divisor. -/
lemma cusp_half_line_disk (hL : 3 ≤ L) (heven : Even L) (hn : 0 < L / 24)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk) :
    ∃ a : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
      IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ a ∧
      ArithmeticThetaPullback.pullbackGlobalSection f A.line A.section_ =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
          (PowerSeries.X ^ (L / 24)) • a := by
  let Y := Component k L D X x
  let y : Y := f (closedPoint k)
  obtain ⟨E, hrep, hE⟩ := hA
  obtain ⟨ι, ⟨C⟩⟩ := hrep.2.2.1
  have hM : IsLineBundle Y A.line := lineBundle_of_cover Y A.line ι C
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (Set.mem_univ y))
  let U := C.opens i
  let e := C.frame i
  let η := e.equiv U le_rfl 1
  let c := sectionCoordinate Y A.line U e A.section_
  have hη : IsFrame A.line U η := frame_generator Y A.line U e
  have hc : res A.line (show U ≤ ⊤ from le_top) A.section_ = c • η := by
    change _ = c • e.equiv U le_rfl 1
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (e.equiv U le_rfl).apply_symm_apply _ |>.symm
  have hy : y ∈ cuspSet k L D X x := by
    change inclusion k L D X x (f (closedPoint k)) ∈ boundary k L D X
    rw [← Scheme.Hom.comp_apply, hf]
    exact V.extends_eq.2.2
  have ho : ((Ring.ord (Y.presheaf.stalk y) (Y.presheaf.germ U y hi c)).toNat : ℤ) =
      (L / 24 : ℕ) := by
    rw [← ArithmeticThetaDegreeAssembly.section_order_eq_stalk_length
      Y A.line hM U e A.section_ hrep.2.1 y hi (cusp_coheight k L D X x hL heven y hy)]
    exact (hrep.2.2.2 ι C i y hi).symm.trans ((hE y).1 hy)
  let hd : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hi).ge
  let b := res ((Scheme.Modules.pullback f).obj A.line) hd
    (Scheme.Modules.pullbackLocalSection f η)
  have hb : IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ b :=
    HodgeBaseChange.frame_restrict _ _ _ (HodgeBaseChange.pullback_frame f A.line η hη)
  let q : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    (f.appLE U ⊤ hd c)
  have hqg : (Scheme.stalkClosedPointTo f).hom (Y.presheaf.germ U y hi c) = q := by
    exact ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo f U hi) c
  have hq : q.order.toNat = L / 24 := by
    rw [← hqg, component_disk_order k L D X x hL heven V f hf]
    exact_mod_cast ho
  obtain ⟨u, hu⟩ := series_factor k q (L / 24) hn hq
  let u' : Γ(Disk k, ⊤)ˣ :=
    u.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom.toMonoidHom
  refine ⟨(u' : Γ(Disk k, ⊤)) • b, InitialHodgeSection.unit_frame _ b hb u', ?_⟩
  have hp : ArithmeticThetaPullback.pullbackGlobalSection f A.line A.section_ =
      f.appLE U ⊤ hd c • b := by
    calc
      ArithmeticThetaPullback.pullbackGlobalSection f A.line A.section_ =
          res ((Scheme.Modules.pullback f).obj A.line) hd
            (res ((Scheme.Modules.pullback f).obj A.line)
              (f.preimage_mono (show U ≤ ⊤ from le_top))
              (Scheme.Modules.pullbackLocalSection f A.section_)) := by
        rw [InitialHodgeSection.res_res, InitialHodgeSection.res_self]
        rfl
      _ = _ := by
        rw [InitialSectionNaturality.pullback_res f A.line (show U ≤ ⊤ from le_top) A.section_, hc,
          Scheme.Modules.pullbackLocalSection_smul, InitialHodgeSection.res_smul]
        rfl

  rw [hp, smul_smul]
  congr 1
  have hscalar : f.appLE U ⊤ hd c =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) q :=
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))) _).symm
  rw [hscalar, hu]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom _ _


end CuspHalfDivisorLineR0185

/-- The actual half-cusp divisor line and its complete Tate-disk normalization. -/
theorem cusp_half_divisor_line :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D :
      ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X :
      ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∃ A :
      ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X
      x), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A ∧ ∀ (V :
      ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk
      k) (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (hf : CategoryTheory.CategoryStruct.comp f
      (ArithmeticThetaComponentDegreeR0184.inclusion k L D X x) = V.disk), ∃ a :
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj A.line).presheaf.obj (Opposite.op ⊤),
      ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
      A.line) ⊤ a ∧ ArithmeticThetaPullback.pullbackGlobalSection f A.line A.section_ =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (PowerSeries.X ^ (L / 24)) • a := by
  intro k _ _ _ L hpos hdiv D X x
  have h24 : 24 ≤ L := Nat.le_of_dvd hpos hdiv
  have hL : 3 ≤ L := by omega
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) hdiv)
  have hn : 0 < L / 24 := Nat.div_pos h24 (by decide)
  obtain ⟨A, hA⟩ := CuspHalfDivisorLineR0185.exists_cusp_half_line k L D X x hL heven
  exact ⟨A, hA, fun V f hf =>
    CuspHalfDivisorLineR0185.cusp_half_line_disk k L D X x hL heven hn A hA V f hf⟩

end ArithmeticThetaCommonHalfHodgeR0185
#print axioms ArithmeticThetaCommonHalfHodgeR0185.CuspHalfDivisorLineR0185.exists_cusp_half_line

#print axioms ArithmeticThetaCommonHalfHodgeR0185.cusp_half_divisor_line
