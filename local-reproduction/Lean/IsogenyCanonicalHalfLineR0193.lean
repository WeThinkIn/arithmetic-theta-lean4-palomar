import CompactIsogenyAlphaR0193

/-! Canonical half-divisor line of the actual isogeny-normalized compact section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

namespace ArithmeticThetaIsogenyHalfLinesR0193.IsogenyCanonicalHalfLine
open ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaPullback
open CompactHodgeLatticeExtensionR0182 ComponentDiscriminantDivisorR0184

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D)
    (H : Extension k L D X) (m : ℕ) (hm : 0 < m) (A : OpenAlpha k L m D)

include hm

local instance : IsOpenImmersion X.inclusion := X.openImmersion

lemma ambient_frame :
    IsFrame (ArithmeticThetaOpenHodgeR0180.hodge D.atlas.descent.family) ⊤
      (ambientAlpha k L m D A) := by
  letI := A.quotient.etale
  letI : IsIso (ArithmeticThetaOpenHodgeR0180.familyHodgeMap A.quotient.arrow) :=
    ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180.family_hodge_isIso
      A.quotient.arrow
  have hf := frame_iso (asIso (ArithmeticThetaOpenHodgeR0180.familyHodgeMap A.quotient.arrow))
    A.alpha A.intrinsic.1
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hu : IsUnit (ArithmeticThetaOpenHodgeR0180.scalar D.atlas.quotient.ring
      (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)) :=
    ((isUnit_iff_ne_zero.mpr (inv_ne_zero hm0)).map
      (algebraMap k D.atlas.quotient.ring)).map
      (Scheme.ΓSpecIso (CommRingCat.of D.atlas.quotient.ring)).inv.hom
  exact InitialHodgeSection.unit_frame _ _ hf hu.unit

lemma open_frame : IsFrame (openHodge k L D) ⊤ (openAlpha k L m D A) := by
  simpa only [openAlpha, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top] using
    pullback_frame D.quotient.inclusion _ _ (ambient_frame k L D m hm A)

lemma compact_interior_frame (a : Γ(H.line, ⊤)) (ha : CompactRealizes k L m D X H A a) :
    IsFrame H.line X.inclusion.opensRange (res H.line le_top a) := by
  letI := X.openImmersion
  apply frame_of_pullback_open X.inclusion _ _ le_rfl
  rw [← InitialSectionNaturality.pullback_res]
  apply frame_restrict
  apply (frame_iso_iff H.onOpen _).mp
  simpa only [restrictAlpha, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top] using (show IsFrame (openHodge k L D) ⊤ (restrictAlpha L k D X H a) from
      by rw [ha.1]; exact open_frame k L D m hm A)

lemma component_interior_frame (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) :
    IsFrame (hodge k L D X x H) (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange)
      (res _ le_top (componentAlpha k L D X H x a)) := by
  have hh := pullback_frame (inclusion k L D X x) H.line _
    (compact_interior_frame k L D X H m hm A a ha)
  rw [← InitialSectionNaturality.pullback_res] at hh
  exact hh

lemma component_ne_zero (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) : componentAlpha k L D X H x a ≠ 0 := by
  letI := component_interior_nonempty k L D X x
  have hn := frame_ne_zero _ (component_interior_frame k L D X H m hm A x a ha)
  intro hz
  apply hn
  simp [hz, res]

/-- Completion of an ambient frame coefficient preserves the allowed orders.
The transition from the canonical differential frame is an actual unit. -/
lemma scalar_stalk_order (hL : 3 ≤ L) (heven : Even L)
    (hH : Canonical k L H) (a : Γ(H.line, ⊤)) (ha : CompactRealizes k L m D X H A a)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (η : Γ(H.line, U)) (hη : IsFrame H.line U η)
    (hU : T.disk (closedPoint k) ∈ U) (r : Γ(X.space, U))
    (hr : res H.line le_top a = r • η) :
    ∃ j : ℕ, Even j ∧
      ((Ring.ord (X.space.presheaf.stalk (T.disk (closedPoint k)))
        (X.space.presheaf.germ U _ hU r)).toNat : ℤ) = (j : ℤ) := by
  let hdisk := (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  let M := (Scheme.Modules.pullback T.disk).obj H.line
  let η' : Γ(M, ⊤) := res M hdisk (Scheme.Modules.pullbackLocalSection T.disk η)
  have hη' : IsFrame M ⊤ η' := frame_restrict _ _ _ (pullback_frame _ _ _ hη)
  obtain ⟨ξ, hξ⟩ := (hH T).exists
  obtain ⟨c, hc⟩ := (hη' ⊤ le_rfl).2 ξ
  rw [InitialHodgeSection.res_self] at hc
  change c • η' = ξ at hc
  have hcu : IsUnit c := frame_coefficient_unit η' hη' c (by rw [hc]; exact hξ.1)
  obtain ⟨i, z, j, v, _, hj, hseries⟩ := ha.2.1 T ξ hξ
  have ht := CompactFullLevelAlpha.transport_local_scalar T.disk H.line M (Iso.refl M)
    a U η r hr hdisk
  have ht' : pullbackGlobalSection T.disk H.line a = T.disk.appLE U ⊤ hdisk r • η' := by
    change res M (show (⊤ : (Disk k).Opens) ≤ ⊤ from le_rfl)
      (pullbackGlobalSection T.disk H.line a) = _ at ht
    rwa [InitialHodgeSection.res_self] at ht
  rw [← hc, smul_smul] at hseries
  have he : T.disk.appLE U ⊤ hdisk r =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (PowerSeries.X^j * (v : PowerSeries k)) * c := by
    apply (hη' ⊤ le_rfl).1
    simpa only [InitialHodgeSection.res_self] using ht'.symm.trans hseries
  let b : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom c
  have hb : IsUnit b := hcu.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
  have hg := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo T.disk U hU) r
  change CompletedLocalParameter.localMap k L D X T.disk
      (X.space.presheaf.germ U _ hU r) =
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
      (T.disk.appLE U ⊤ hdisk r) at hg
  have hscalar : CompletedLocalParameter.localMap k L D X T.disk
      (X.space.presheaf.germ U _ hU r) = (PowerSeries.X^j * (v : PowerSeries k)) * b := by
    rw [hg, he, map_mul]
    simp only [ArithmeticThetaOpenHodgeR0180.scalar, Iso.inv_hom_id_apply]
    rfl
  have ho : Ring.ord (X.space.presheaf.stalk (T.disk (closedPoint k)))
      (X.space.presheaf.germ U _ hU r) = (j : ℕ∞) := by
    rw [← disk_localMap_order k L hL heven D X T, hscalar,
      PowerSeries.order_mul, PowerSeries.order_mul,
      PowerSeries.order_zero_of_unit hb, PowerSeries.order_zero_of_unit v.isUnit,
      PowerSeries.order_X_pow, add_zero, add_zero]
  exact ⟨j, hj.2.2.2.2.1, by rw [ho]; simp⟩

/-- Orders vanish off the actual cusp locus. -/
lemma order_interior (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hint : y ∉ cuspSet k L D X x) :
    localOrder _ _ C (componentAlpha k L D X H x a) i y = 0 := by
  apply order_zero_of_frame _ _ (C.opens i)
    (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange) (C.frame i) y hy
  · change ¬ ¬ inclusion k L D X x y ∈ Set.range X.inclusion at hint
    exact not_not.mp hint
  · exact component_interior_frame k L D X H m hm A x a ha

/-- Every cusp order is transported along the actual open-and-closed inclusion. -/
lemma order_cusp [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    (hH : Canonical k L H) (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hcusp : y ∈ cuspSet k L D X x) :
    ∃ j : ℕ, Even j ∧
      localOrder _ _ C (componentAlpha k L D X H x a) i y = (j : ℤ) := by
  have hgeom := component_curve_frames k L hL heven D X x
  letI := hgeom.2.1
  have hco : Order.coheight y = 1 := by
    apply ArithmeticThetaGeometricNormR0150.NormOrders.smooth_coheight_one_of_ne_generic
      k (projection k L D X x)
    intro heq
    have hgen : genericPoint (Component k L D X x) ∈
        inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange :=
      ((genericPoint_spec (Component k L D X x)).mem_open_set_iff
        (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange).isOpen).mpr
          (by simpa using component_interior_nonempty k L D X x)
    rw [← heq] at hgen
    exact hcusp hgen
  obtain ⟨T, hTy⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X
    (inclusion k L D X x y) hcusp
  obtain ⟨U, η, hyU, hη⟩ := local_frame_exists H.invertible (inclusion k L D X x y)
  obtain ⟨r, hr⟩ := (hη U le_rfl).2 (res H.line le_top a)
  rw [InitialHodgeSection.res_self] at hr
  let p := inclusion k L D X x
  have ht : componentAlpha k L D X H x a =
      OpenDiscriminantFullTateExpansionR0182.transportSection p H.line
        (hodge k L D X x H) (Iso.refl _) a := by
    simp only [OpenDiscriminantFullTateExpansionR0182.transportSection,
      Iso.refl_hom, Scheme.Modules.Hom.id_app, InitialHodgeSection.res_self]
    rfl
  have ho := order_pullback_scalar p H.line _ (Iso.refl _) a _ ht
    (ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C)
    (component_ne_zero k L D X H m hm A x a ha) U η hη r hr.symm
    (C.opens i) (C.frame i) y hy hyU hco
  change localOrder _ _ C (componentAlpha k L D X H x a) i y = _ at ho
  rw [ho]
  have hTU : T.disk (closedPoint k) ∈ U := hTy.symm ▸ hyU
  have hord := scalar_stalk_order k L D X H m hm A hL heven hH a ha T U η hη hTU r hr.symm
  have hpoint : (⟨T.disk (closedPoint k), hTU⟩ : U) = ⟨p y, hyU⟩ := Subtype.ext hTy
  have horder := congrArg (fun z : U =>
    ((Ring.ord (X.space.presheaf.stalk z.1)
      (X.space.presheaf.germ U z.1 z.2 r)).toNat : ℤ)) hpoint
  rwa [horder] at hord


lemma half_divisor [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    (hH : Canonical k L H) (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) :
    ∃ E : Component k L D X x →₀ ℤ, HalfDivisor k L D X H x a E := by
  classical
  have hgeom := component_curve_frames k L hL heven D X x
  letI := hgeom.1
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hgeom.2.2.2.1 (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  have hne := component_ne_zero k L D X H m hm A x a ha
  obtain ⟨B, hB⟩ := exists_section_divisor _ k (projection k L D X x)
    hgeom.2.2.1 _ _ C (componentAlpha k L D X H x a) hne
  have hvalues : ∀ y, ∃ j : ℕ, Even j ∧ B y = (j : ℤ) := by
    intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    by_cases hy : y ∈ cuspSet k L D X x
    · exact order_cusp k L D X H m hm A hL heven hH x a ha _ C i y hi hy
    · exact ⟨0, ⟨0, rfl⟩, by simpa using order_interior k L D X H m hm A x a ha _ C i y hi hy⟩
  have hoff : ∀ y, y ∉ cuspSet k L D X x → B y = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    exact order_interior k L D X H m hm A x a ha _ C i y hi hy
  let E : Component k L D X x →₀ ℤ := B.mapRange (fun z => z / 2) (by simp)
  have hE (y : Component k L D X x) : E y = B y / 2 := rfl
  have hdouble : 2 • E = B := by
    ext y
    simp only [Finsupp.smul_apply, hE, nsmul_eq_mul]
    obtain ⟨j, ⟨r, hr⟩, hj⟩ := hvalues y
    rw [hj]
    omega
  refine ⟨E, ?_, ?_, hne, ⟨Component k L D X x, ⟨C⟩⟩, ?_⟩
  · intro y
    obtain ⟨j, _, hj⟩ := hvalues y
    rw [hE, hj]
    positivity
  · intro y hy
    simp [hE, hoff y hy]
  · intro ι C' i y hy
    rw [hdouble]
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB j y hj]
    exact ArithmeticThetaDegreeAssembly.section_order_frame_invariant _ _
      (C.opens j) (C'.opens i) (C.frame j) (C'.frame i) _ y hj hy

end ArithmeticThetaIsogenyHalfLinesR0193.IsogenyCanonicalHalfLine

namespace ArithmeticThetaIsogenyHalfLinesR0193.IsogenyCanonicalHalfLine
open ArithmeticThetaSquareLinesR0192
open ArithmeticThetaSquareLinesR0192.CompactAlphaCanonicalHalfLine
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaPullback ArithmeticThetaTensorPower
open ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaGeometricPrerequisites
open ArithmeticThetaDegreeAssembly

variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D)
    (H : Extension k L D X) (x : X.space)

lemma canonical_square (hL : 3 ≤ L) (heven : Even L)
    (a : Γ(H.line, ⊤)) (E : Component k L D X x →₀ ℤ)
    (hE : HalfDivisor k L D X H x a E)
    (hN : NormalAffine (Component k L D X x)) :
    Scheme.Modules.IsInvertible (canonicalDivisorData k L D X x E hE.1 hN).line ∧
    ∃ β : tensorPower (Component k L D X x)
        (canonicalDivisorData k L D X x E hE.1 hN).line 2 ≅ hodge k L D X x H,
      β.hom.app ⊤ (tensorPowerSection (Component k L D X x)
        (canonicalDivisorData k L D X x E hE.1 hN).line 2 ⊤
        (canonicalDivisorData k L D X x E hE.1 hN).section_) =
          componentAlpha k L D X H x a := by
  let Y := Component k L D X x
  have hg := component_curve_frames k L hL heven D X x
  have hco : ∀ y, E y ≠ 0 → Order.coheight y = 1 := by
    intro y hy
    apply CuspHalfDivisorLineR0185.cusp_coheight k L D X x hL heven y
    by_contra hn
    exact hy (hE.2.1 y hn)
  have hline := ArithmeticThetaCoverComparison.signed_divisor_line Y hg.2.2.1 hN E hco
  have hi := CuspHalfDivisorLineR0185.invertible_of_lineBundle Y _ hline
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible Y hN _ hi
  have horders := DiscriminantTwistUnitR0185.canonical_divisor_orders Y hg.2.2.1 hN E hE.1 hco Y C
  have hs := divisorCanonicalSection_ne_zero Y hN E hE.1
  obtain ⟨hsq, hsqorder⟩ := tensor_power_divisor Y _ hline Y C 2 _ E hs horders
  obtain ⟨ι, ⟨B⟩⟩ := hE.2.2.2.1
  obtain ⟨β, hβ, _⟩ := equal_divisor_rigidified_isomorphism Y hg.2.2.1 hN _ _
    (tensorPower_isLineBundle Y _ C 2)
    (isLineBundle_of_normalFrameCover Y _ B) Y ι (powerCover Y _ C 2) B _ _
    (2 • E) hsq hE.2.2.1 hsqorder (hE.2.2.2.2 ι B)
  exact ⟨hi, β, hβ⟩

open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open OpenDiscriminantFullTateExpansionR0182
open CompactHodgeLatticeExtensionR0182

lemma normalized_branch (m : ℕ) (O : OpenAlpha k L m D) (a : Γ(H.line, ⊤)) (ha : CompactRealizes k L m D X H O a)
    (A : DivisorLine (Component k L D X x)) (hA : Scheme.Modules.IsInvertible A.line)
    (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H)
    (hβ : β.hom.app ⊤ (tensorPowerSection (Component k L D X x) A.line 2 ⊤ A.section_) =
      componentAlpha k L D X H x a) : HalfBranch k L m D X H x A β := by
  intro V ζ hζ hmark f hf η hη
  let M := (Scheme.Modules.pullback f).obj A.line
  let s : Γ(M, ⊤) := pullbackGlobalSection f A.line A.section_
  let e : tensorPower (Disk k) M 2 ≅ (Scheme.Modules.pullback V.disk).obj H.line :=
    (pullback_tensorPower_iso _ _ f A.line 2).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ diskHodgeIso k L D X x H V f hf
  have he : e.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤ s) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k (L*m) ^ 2) • η := by
    have ht : (pullback_tensorPower_iso _ _ f A.line 2).hom.app ⊤
        (pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_)) =
        tensorPowerSection (Disk k) M 2 ⊤ s := by
      simpa only [Scheme.Hom.preimage_top] using
        pullback_tensorPower_section (Disk k) (Component k L D X x) f A.line 2 A.section_
    have ht' : (pullback_tensorPower_iso _ _ f A.line 2).inv.app ⊤
        (tensorPowerSection (Disk k) M 2 ⊤ s) =
        pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_) := by
      rw [← ht]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => q.app ⊤) (pullback_tensorPower_iso _ _ f A.line 2).hom_inv_id) _
    change (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      (((Scheme.Modules.pullback f).map β.hom).app ⊤
        ((pullback_tensorPower_iso _ _ f A.line 2).inv.app ⊤
          (tensorPowerSection (Disk k) M 2 ⊤ s))) = _
    rw [ht']
    have hmap := Scheme.Modules.pullbackLocalSection_app f β.hom
      (tensorPowerSection _ A.line 2 ⊤ A.section_)
    have hmap' : pullbackGlobalSection f _ (β.hom.app ⊤
        (tensorPowerSection _ A.line 2 ⊤ A.section_)) =
        ((Scheme.Modules.pullback f).map β.hom).app ⊤
          (pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_)) := by
      simpa only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
        Scheme.Hom.preimage_top] using hmap
    rw [← hmap', hβ, disk_component_alpha k L D X H x a V f hf]
    exact ha.2.2 V ζ hζ hmark η hη
  obtain ⟨v, hv⟩ := FourTorsionTateBehavior.thetaAt_unit k (L*m)
  let u : Γ(Disk k, ⊤)ˣ :=
    v.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom.toMonoidHom
  have hu : (u : Γ(Disk k, ⊤)) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k (L*m)) := by
    change (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (v : PowerSeries k) = _
    rw [hv]
    rfl
  have hu2 : ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k (L*m) ^ 2) =
      (u : Γ(Disk k, ⊤)) ^ 2 := by
    rw [hu]
    exact map_pow (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom _ _
  rw [hu2] at he
  have hs : IsFrame M ⊤ s := by
    apply disk_frame_of_square k M (hA.pullback f) s
    apply (ComponentDiscriminantDivisorR0184.frame_iso_iff e _).mp
    rw [he]
    exact InitialHodgeSection.unit_frame _ η hη.1 (u^2)
  refine ⟨(↑(u⁻¹) : Γ(Disk k, ⊤)) • s,
    InitialHodgeSection.unit_frame M s hs u⁻¹, ?_, ?_⟩
  · rw [← hu, smul_smul, Units.mul_inv, one_smul]
  · change e.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤
      ((↑(u⁻¹) : Γ(Disk k, ⊤)) • s)) = η
    rw [InitialHodgeSection.tensor_smul, Scheme.Modules.Hom.app_smul, he, smul_smul]
    have huinv : (↑(u⁻¹) : Γ(Disk k, ⊤)) ^ 2 * (u : Γ(Disk k, ⊤)) ^ 2 = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [huinv, one_smul]


end ArithmeticThetaIsogenyHalfLinesR0193.IsogenyCanonicalHalfLine

namespace ArithmeticThetaIsogenyHalfLinesR0193
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaComponentDegreeR0184
/-- The canonical effective half-divisor line and its prescribed isogeny theta frame. -/
theorem isogeny_canonical_half_line :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D, ∀ a : (H.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes k L m D X H A a → ∀ x : X.space, ∃ (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ) (hE : ∀ y, 0 ≤ E y) (hN : ArithmeticThetaNormalizedSections.NormalAffine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaIsogenyHalfLinesR0193.HalfDivisor k L D X H x a E ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line ∧ ∃ β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H), β.hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2 ⊤ (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).section_) = ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ∧ ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch k L m D X H x (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN) β := by
  intro k _ _ _ L m hL hm hmEven hdiv D X H hH A a ha x
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  obtain ⟨E, hE⟩ := IsogenyCanonicalHalfLine.half_divisor k L D X H m hm A
    hb.1 hb.2.1 hH x a ha
  have hN := (component_curve_frames k L hb.1 hb.2.1 D X x).2.2.2.1
  obtain ⟨hi, β, hβ⟩ := IsogenyCanonicalHalfLine.canonical_square k L D X H x
    hb.1 hb.2.1 a E hE hN
  exact ⟨E, hE.1, hN, hE, hi, β, hβ,
    IsogenyCanonicalHalfLine.normalized_branch k L D X H x m A a ha _ hi β hβ⟩

#print axioms IsogenyCanonicalHalfLine.ambient_frame
#print axioms IsogenyCanonicalHalfLine.scalar_stalk_order
#print axioms IsogenyCanonicalHalfLine.half_divisor
#print axioms IsogenyCanonicalHalfLine.canonical_square
#print axioms IsogenyCanonicalHalfLine.normalized_branch
#print axioms isogeny_canonical_half_line
end ArithmeticThetaIsogenyHalfLinesR0193
