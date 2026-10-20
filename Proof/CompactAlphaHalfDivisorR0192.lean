module

public import SquareLineComparisonDefinitionsR0192
public import ComponentDiscriminantDivisorR0184

@[expose] public section

/-! The effective half-divisor of the specified compact alpha on every component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

namespace ArithmeticThetaSquareLinesR0192.CompactAlphaHalfDivisor
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
    (H : Extension k L D X)

local instance : IsOpenImmersion X.inclusion := X.openImmersion

lemma compact_interior_frame (a : Γ(H.line, ⊤)) (ha : IsCompactAlpha k L D X H a) :
    IsFrame H.line X.inclusion.opensRange (res H.line le_top a) := by
  letI := X.openImmersion
  apply frame_of_pullback_open X.inclusion _ _ le_rfl
  rw [← InitialSectionNaturality.pullback_res]
  apply frame_restrict
  apply (frame_iso_iff H.onOpen _).mp
  simpa only [restrictAlpha, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top] using ha.1.1

lemma component_interior_frame (x : X.space) (a : Γ(H.line, ⊤))
    (ha : IsCompactAlpha k L D X H a) :
    IsFrame (hodge k L D X x H) (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange)
      (res _ le_top (componentAlpha k L D X H x a)) := by
  have hh := pullback_frame (inclusion k L D X x) H.line _
    (compact_interior_frame k L D X H a ha)
  rw [← InitialSectionNaturality.pullback_res] at hh
  exact hh

lemma component_ne_zero (x : X.space) (a : Γ(H.line, ⊤))
    (ha : IsCompactAlpha k L D X H a) : componentAlpha k L D X H x a ≠ 0 := by
  letI := component_interior_nonempty k L D X x
  have hn := frame_ne_zero _ (component_interior_frame k L D X H x a ha)
  intro hz
  apply hn
  simp [hz, res]

/-- Completion of an ambient frame coefficient preserves the allowed orders.
The transition from the canonical differential frame is an actual unit. -/
lemma scalar_stalk_order (hL : 3 ≤ L) (heven : Even L)
    (hH : Canonical k L H) (a : Γ(H.line, ⊤)) (ha : IsCompactAlpha k L D X H a)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (η : Γ(H.line, U)) (hη : IsFrame H.line U η)
    (hU : T.disk (closedPoint k) ∈ U) (r : Γ(X.space, U))
    (hr : res H.line le_top a = r • η) :
    ((Ring.ord (X.space.presheaf.stalk (T.disk (closedPoint k)))
      (X.space.presheaf.germ U _ hU r)).toNat : ℤ) = 0 ∨
    ((Ring.ord (X.space.presheaf.stalk (T.disk (closedPoint k)))
      (X.space.presheaf.germ U _ hU r)).toNat : ℤ) = (L/4 : ℕ) := by
  let hdisk := (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  let M := (Scheme.Modules.pullback T.disk).obj H.line
  let η' : Γ(M, ⊤) := res M hdisk (Scheme.Modules.pullbackLocalSection T.disk η)
  have hη' : IsFrame M ⊤ η' := frame_restrict _ _ _ (pullback_frame _ _ _ hη)
  obtain ⟨ξ, hξ⟩ := (hH T).exists
  obtain ⟨c, hc⟩ := (hη' ⊤ le_rfl).2 ξ
  rw [InitialHodgeSection.res_self] at hc
  change c • η' = ξ at hc
  have hcu : IsUnit c := frame_coefficient_unit η' hη' c (by rw [hc]; exact hξ.1)
  obtain ⟨v, j, hj, _, hseries⟩ := ha.2.1 T ξ hξ
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
  rw [ho]
  rcases hj with rfl | rfl
  · simp
  · simp

/-- Orders vanish off the actual cusp locus. -/
lemma order_interior (x : X.space) (a : Γ(H.line, ⊤))
    (ha : IsCompactAlpha k L D X H a) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hint : y ∉ cuspSet k L D X x) :
    localOrder _ _ C (componentAlpha k L D X H x a) i y = 0 := by
  apply order_zero_of_frame _ _ (C.opens i)
    (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange) (C.frame i) y hy
  · change ¬ ¬ inclusion k L D X x y ∈ Set.range X.inclusion at hint
    exact not_not.mp hint
  · exact component_interior_frame k L D X H x a ha

/-- Every cusp order is transported along the actual open-and-closed inclusion. -/
lemma order_cusp [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    (hH : Canonical k L H) (x : X.space) (a : Γ(H.line, ⊤))
    (ha : IsCompactAlpha k L D X H a) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hcusp : y ∈ cuspSet k L D X x) :
    localOrder _ _ C (componentAlpha k L D X H x a) i y = 0 ∨
    localOrder _ _ C (componentAlpha k L D X H x a) i y = (L/4 : ℕ) := by
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
    (component_ne_zero k L D X H x a ha) U η hη r hr.symm
    (C.opens i) (C.frame i) y hy hyU hco
  change localOrder _ _ C (componentAlpha k L D X H x a) i y = _ at ho
  rw [ho]
  have hTU : T.disk (closedPoint k) ∈ U := hTy.symm ▸ hyU
  have hord := scalar_stalk_order k L D X H hL heven hH a ha T U η hη hTU r hr.symm
  have hpoint : (⟨T.disk (closedPoint k), hTU⟩ : U) = ⟨p y, hyU⟩ := Subtype.ext hTy
  have horder := congrArg (fun z : U =>
    ((Ring.ord (X.space.presheaf.stalk z.1)
      (X.space.presheaf.germ U z.1 z.2 r)).toNat : ℤ)) hpoint
  rwa [horder] at hord

end ArithmeticThetaSquareLinesR0192.CompactAlphaHalfDivisor

namespace ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open CompactAlphaHalfDivisor

/-- On every actual component, the divisor of the specified compact alpha is
an effective integral double; the identity holds in every normal frame. -/
theorem compact_alpha_half_divisor :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
      (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D)
      (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X),
    ArithmeticThetaBoundaryHodgeR0182.Canonical k L H →
    ∀ (a : (H.line).presheaf.obj (Opposite.op ⊤)),
    ArithmeticThetaSquareLinesR0192.IsCompactAlpha k L D X H a →
    ∀ x : X.space, ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ,
      ArithmeticThetaSquareLinesR0192.HalfAlphaDivisor k L D X H x a E := by
  intro k _ _ _ L hL h8 D X H hH a ha x
  classical
  have h3 : 3 ≤ L := le_trans (by norm_num) (Nat.le_of_dvd hL h8)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hquarter : (2 : ℤ) * (L / 8 : ℕ) = (L / 4 : ℕ) := by
    obtain ⟨n, rfl⟩ := h8
    omega
  have hgeom := component_curve_frames k L h3 heven D X x
  letI := hgeom.1
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hgeom.2.2.2.1 (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  have hne := component_ne_zero k L D X H x a ha
  obtain ⟨B, hB⟩ := exists_section_divisor _ k (projection k L D X x)
    hgeom.2.2.1 _ _ C (componentAlpha k L D X H x a) hne
  have hvalues : ∀ y, B y = 0 ∨ B y = (L/4 : ℕ) := by
    intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    by_cases hy : y ∈ cuspSet k L D X x
    · exact order_cusp k L D X H h3 heven hH x a ha _ C i y hi hy
    · exact Or.inl (order_interior k L D X H x a ha _ C i y hi hy)
  have hoff : ∀ y, y ∉ cuspSet k L D X x → B y = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    exact order_interior k L D X H x a ha _ C i y hi hy
  let E : Component k L D X x →₀ ℤ := Finsupp.onFinset B.support
    (fun y => if B y = 0 then (0 : ℤ) else ((L/8 : ℕ) : ℤ)) (by
      intro y hy
      exact Finsupp.mem_support_iff.mpr (by intro hz; simp [hz] at hy))
  have hE (y : Component k L D X x) : E y = if B y = 0 then (0 : ℤ) else ((L/8 : ℕ) : ℤ) := rfl
  have hdouble : 2 • E = B := by
    ext y
    simp only [Finsupp.smul_apply, hE, nsmul_eq_mul]
    rcases hvalues y with hz | hq
    · simp [hz]
    · split_ifs with hz
      · simp [hz]
      · exact hquarter.trans hq.symm
  refine ⟨E, ?_, ?_, ?_, hne, ⟨Component k L D X x, ⟨C⟩⟩, ?_⟩
  · intro y
    rw [hE]
    split_ifs <;> positivity
  · intro y
    rw [hE]
    split_ifs <;> simp
  · intro y hy
    simp [hE, hoff y hy]
  · intro ι C' i y hy
    rw [hdouble]
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB j y hj]
    exact ArithmeticThetaDegreeAssembly.section_order_frame_invariant _ _
      (C.opens j) (C'.opens i) (C.frame j) (C'.frame i) _ y hj hy

#print axioms compact_alpha_half_divisor
end ArithmeticThetaSquareLinesR0192
