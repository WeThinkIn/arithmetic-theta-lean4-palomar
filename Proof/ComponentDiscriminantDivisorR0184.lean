module

public import ComponentCurveFramesR0184

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaComponentDegreeR0184.ComponentDiscriminantDivisorR0184
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaTateCuspsR0181
open CompactHodgeLatticeExtensionR0182 CompactDiscriminantSectionR0182

lemma frame_iso_iff {Y : Scheme} {M N : Y.Modules} (e : M ≅ N)
    {U : Y.Opens} (s : Γ(M, U)) :
    IsFrame N U (e.hom.app U s) ↔ IsFrame M U s := by
  constructor
  · intro hs
    have h := frame_iso e.symm _ hs
    have he : e.inv.app U (e.hom.app U s) = s := by
      exact ConcreteCategory.congr_hom
        (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) s
    change IsFrame M U (e.inv.app U (e.hom.app U s)) at h
    rwa [he] at h
  · exact frame_iso e s

lemma frame_ne_zero {Y : Scheme} {M : Y.Modules} {U : Y.Opens}
    [Nonempty U] (s : Γ(M, U)) (hs : IsFrame M U s) : s ≠ 0 := by
  intro hz
  have h := (hs U le_rfl).1 (a₁ := (1 : Γ(Y, U))) (a₂ := 0)
  apply one_ne_zero (h ?_)
  simp [hz, InitialHodgeSection.res_self]

/-- A frame section has order zero in every other actual local frame. -/
lemma order_zero_of_frame {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (M : Y.Modules) (s : Γ(M, ⊤)) (U V : Y.Opens) [Nonempty U]
    (e : LocalFrame Y M U) (y : Y) (hyU : y ∈ U) (hyV : y ∈ V)
    (hs : IsFrame M V (res M le_top s)) :
    Scheme.ord (sectionCoefficient Y M U e s) y = 0 := by
  letI : Nonempty V := ⟨⟨y, hyV⟩⟩
  let e' := InitialHodgeSection.frame M (res M le_top s) hs
  rw [ArithmeticThetaDegreeAssembly.section_order_frame_invariant
    Y M U V e e' s y hyU hyV]
  have hc : sectionCoordinate Y M V e' s = 1 := by
    apply (e'.equiv V le_rfl).injective
    rw [sectionCoordinate, LinearEquiv.apply_symm_apply]
    change res M (show V ≤ ⊤ from le_top) s =
      (1 : Γ(Y, V)) • res M (show V ≤ V from le_rfl)
        (res M (show V ≤ ⊤ from le_top) s)
    rw [InitialHodgeSection.res_self, one_smul]
  unfold sectionCoefficient
  rw [hc]
  exact Scheme.ord_of_isUnit isUnit_one hyV

/-- For an open immersion, the actual local scalar has the same quotient
length before and after pullback. The module comparison is retained explicitly. -/
lemma order_pullback_scalar {Y Z : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (p : Y ⟶ Z) [IsOpenImmersion p] (M : Z.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (s : Γ(M, ⊤)) (t : Γ(N, ⊤))
    (ht : t = OpenDiscriminantFullTateExpansionR0182.transportSection p M N e s)
    (hN : IsLineBundle Y N) (ht0 : t ≠ 0)
    (U : Z.Opens) (η : Γ(M, U)) (hη : IsFrame M U η)
    (a : Γ(Z, U)) (ha : res M le_top s = a • η)
    (V : Y.Opens) [Nonempty V] (f : LocalFrame Y N V)
    (y : Y) (hyV : y ∈ V) (hyU : p y ∈ U) (hco : Order.coheight y = 1) :
    Scheme.ord (sectionCoefficient Y N V f t) y =
      ((Ring.ord (Z.presheaf.stalk (p y)) (Z.presheaf.germ U _ hyU a)).toNat : ℤ) := by
  let W := p ⁻¹ᵁ U
  letI : Nonempty W := ⟨⟨y, hyU⟩⟩
  let η' : Γ(N, W) := e.hom.app W (Scheme.Modules.pullbackLocalSection p η)
  have hη' : IsFrame N W η' := frame_iso e _ (pullback_frame p M η hη)
  let f' := InitialHodgeSection.frame N η' hη'
  have hr : res N (show W ≤ ⊤ from le_top) t = p.app U a • η' := by
    rw [ht, OpenDiscriminantFullTateExpansionR0182.transportSection_restrict
      p M N e s U W le_rfl, InitialHodgeSection.res_self, ha,
      Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  have hc : sectionCoordinate Y N W f' t = p.app U a := by
    apply (f'.equiv W le_rfl).injective
    rw [sectionCoordinate, LinearEquiv.apply_symm_apply]
    change res N (show W ≤ ⊤ from le_top) t =
      p.app U a • res N (show W ≤ W from le_rfl) η'
    rw [InitialHodgeSection.res_self]
    exact hr
  rw [ArithmeticThetaDegreeAssembly.section_order_frame_invariant
    Y N V W f f' t y hyV hyU,
    ArithmeticThetaDegreeAssembly.section_order_eq_stalk_length Y N hN W f' t ht0 y hyU hco,
    hc, ← Scheme.Hom.germ_stalkMap_apply p U y hyU a]
  let e' := (asIso (p.stalkMap y)).commRingCatIsoToRingEquiv
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (ArithmeticThetaGeometricNormR0150.NormOrders.ord_ringEquiv e'
      (Z.presheaf.germ U _ hyU a)).symm

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

local instance : IsOpenImmersion X.inclusion := X.openImmersion

/-- The actual cusp set on the specified open-and-closed component is finite. -/
lemma cuspSet_finite : (cuspSet k L D X x).Finite := by
  apply (BoundaryGeometry.boundary_finite k L D X).preimage
  exact (inclusion k L D X x).isOpenEmbedding.injective.injOn

/-- Intrinsic open D2 is a frame after the specified base pullback. -/
lemma open_discriminant_frame (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : IsCompactD2 k L D X H s) :
    IsFrame (openPower k L D 24) ⊤ (restrictPower k L H 24 s) := by
  obtain ⟨d, hd, heq⟩ := hs
  rw [heq]
  exact frame_restrict _ _ _ (frame_iso _ _
    (pullback_frame D.quotient.inclusion _ d hd.1))

/-- The same compact section is a frame on the actual interior open. -/
lemma compact_interior_frame (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : IsCompactD2 k L D X H s) :
    IsFrame (tensorPower X.space H.line 24) X.inclusion.opensRange
      (res _ le_top s) := by
  letI := X.openImmersion
  apply frame_of_pullback_open X.inclusion _ _ le_rfl
  rw [← InitialSectionNaturality.pullback_res]
  apply frame_restrict
  apply (frame_iso_iff (tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen 24) _).mp
  simpa only [restrictPower, InitialHodgeSection.res_self, Scheme.Hom.preimage_top] using
    open_discriminant_frame k L D X H s hs

/-- Pulling to the actual component preserves the interior frame property. -/
lemma component_interior_frame (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : IsCompactD2 k L D X H s) :
    IsFrame (power k L D X x H 24)
      (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange)
      (res _ le_top (restrict k L D X x H 24 s)) := by
  let p := inclusion k L D X x
  let e := ArithmeticThetaPullback.pullback_tensorPower_iso _ _ p H.line 24
  have heq : restrict k L D X x H 24 s =
      OpenDiscriminantFullTateExpansionR0182.transportSection p _ _ e s := by
    change e.hom.app _ _ = res _ _ (e.hom.app _ _)
    rw [InitialHodgeSection.res_self]
    rfl
  rw [heq, OpenDiscriminantFullTateExpansionR0182.transportSection_restrict
    p _ _ e s X.inclusion.opensRange _ le_rfl]
  exact frame_restrict _ _ _ (frame_iso _ _ (pullback_frame p _ _
    (compact_interior_frame k L D X H s hs)))

/-- Every geometric component meets the actual dense interior. -/
lemma component_interior_nonempty :
    Nonempty (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange) := by
  obtain ⟨y, hy, hz⟩ := X.dense.inter_open_nonempty
    (componentOpen k L D X x) (componentOpen k L D X x).isOpen
    ⟨x, mem_irreducibleComponent⟩
  exact ⟨⟨⟨y, hy⟩, hz⟩⟩

/-- Nonvanishing is established separately on each specified component. -/
lemma component_discriminant_ne_zero (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : IsCompactD2 k L D X H s) : restrict k L D X x H 24 s ≠ 0 := by
  letI := component_interior_nonempty k L D X x
  have hn := frame_ne_zero _ (component_interior_frame k L D X x H s hs)
  intro hz
  apply hn
  simp [hz, res]

/-- No interior zero, including the generic point, in every normal frame. -/
lemma component_discriminant_order_interior (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : IsCompactD2 k L D X H s) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (power k L D X x H 24) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hint : y ∉ cuspSet k L D X x) :
    localOrder _ _ C (restrict k L D X x H 24 s) i y = 0 := by
  apply order_zero_of_frame _ _ (C.opens i)
    (inclusion k L D X x ⁻¹ᵁ X.inclusion.opensRange) (C.frame i) y hy
  · change ¬ ¬ inclusion k L D X x y ∈ Set.range X.inclusion at hint
    exact not_not.mp hint
  · exact component_interior_frame k L D X x H s hs

/-- Naturality retains the local scalar of the very same compact section. -/
lemma compact_scalar_on_open (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (U : X.space.Opens) (η : Γ(H.line, U)) (a : Γ(X.space, U))
    (ha : res (tensorPower X.space H.line 24) le_top s =
      a • tensorPowerSection X.space H.line 24 U η) :
    res (openPower k L D 24) le_top (restrictPower k L H 24 s) =
      X.inclusion.app U a • tensorPowerSection (OpenBase k L D) (openHodge k L D) 24
        (X.inclusion ⁻¹ᵁ U)
        (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion η)) := by
  change res _ le_top (OpenDiscriminantFullTateExpansionR0182.transportSection
    X.inclusion _ _ (tensorComparison X.inclusion H.line _ H.onOpen 24) s) = _
  rw [OpenDiscriminantFullTateExpansionR0182.transportSection_restrict
    X.inclusion _ _ _ s U _ le_rfl, InitialHodgeSection.res_self, ha,
    Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    tensorComparison_section]

/-- The actual compact stalk coefficient, measured through its specified disk,
has the full discriminant order; this is not an arbitrary expansion map. -/
lemma compact_scalar_laurent_order (hL : 3 ≤ L) (heven : Even L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (η : Γ(H.line, U)) (hη : IsFrame H.line U η)
    (hU : T.disk (closedPoint k) ∈ U) (a : Γ(X.space, U))
    (ha : res (tensorPower X.space H.line 24) le_top s =
      a • tensorPowerSection X.space H.line 24 U η) :
    (algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk
        (X.space.presheaf.germ U _ hU a))).order = (2 * L : ℕ) := by
  obtain ⟨d, hd, hs⟩ := hs
  have hdU := (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  have hoU : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z _
    change X.inclusion (T.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hdU (Set.mem_univ _)
  have hr := compact_scalar_on_open k L D X H s U η a ha
  rw [hs] at hr
  have ho := canonical_local_scalar_order k L hL heven H hH T U η hη hU
    d hd (X.inclusion.app U a) hr hoU
  rw [generic_open_scalar_eq_disk k L T U hdU hoU a] at ho
  have hg := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo T.disk U hU) a
  change CompletedLocalParameter.localMap k L D X T.disk
      (X.space.presheaf.germ U _ hU a) =
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
      (T.disk.appLE U ⊤ hdU a) at hg
  rw [hg]
  let b := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    (T.disk.appLE U ⊤ hdU a)
  have hb : T.disk.appLE U ⊤ hdU a = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) b := by
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))) _).symm
  rw [hb] at ho
  change ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    ((ArithmeticThetaProjectiveEffectivityR0135.genericBase k).app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv b))).order = _ at ho
  rw [ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.scalar_restriction,
    Iso.inv_hom_id_apply] at ho
  exact ho

lemma compact_scalar_stalk_order (hL : 3 ≤ L) (heven : Even L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (η : Γ(H.line, U)) (hη : IsFrame H.line U η)
    (hU : T.disk (closedPoint k) ∈ U) (a : Γ(X.space, U))
    (ha : res (tensorPower X.space H.line 24) le_top s =
      a • tensorPowerSection X.space H.line 24 U η) :
    ((Ring.ord (X.space.presheaf.stalk (T.disk (closedPoint k)))
      (X.space.presheaf.germ U _ hU a)).toNat : ℤ) = (2 * L : ℕ) := by
  have ho := compact_scalar_laurent_order k L D X hL heven H hH s hs T U η hη hU a ha
  have ha0 : X.space.presheaf.germ U _ hU a ≠ 0 := by
    intro hz
    rw [hz, map_zero, map_zero, HahnSeries.order_zero] at ho
    have hp : (0 : ℤ) < (2 * L : ℕ) := by omega
    omega
  rw [disk_localMap_laurent_order k L hL heven D X T _ ha0] at ho
  exact ho

/-- Exact order at every geometric cusp in every actual component frame. -/
lemma component_discriminant_order_cusp [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (ι : Type) (C : NormalFrameCover (Component k L D X x) (power k L D X x H 24) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hcusp : y ∈ cuspSet k L D X x) :
    localOrder _ _ C (restrict k L D X x H 24 s) i y = (2 * L : ℕ) := by
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
  let η24 := tensorPowerSection X.space H.line 24 U η
  have hη24 : IsFrame (tensorPower X.space H.line 24) U η24 := tensorPower_frame _ η hη 24
  obtain ⟨a, ha⟩ := (hη24 U le_rfl).2 (res (tensorPower X.space H.line 24) le_top s)
  rw [InitialHodgeSection.res_self] at ha
  let p := inclusion k L D X x
  let e := ArithmeticThetaPullback.pullback_tensorPower_iso _ _ p H.line 24
  have ht : restrict k L D X x H 24 s =
      OpenDiscriminantFullTateExpansionR0182.transportSection p _ _ e s := by
    change e.hom.app _ _ = res _ _ (e.hom.app _ _)
    rw [InitialHodgeSection.res_self]
    rfl
  have ho := order_pullback_scalar p _ _ e s (restrict k L D X x H 24 s) ht
    (hgeom.2.2.2.2.1 H 24).1 (component_discriminant_ne_zero k L D X x H s hs)
    U η24 hη24 a ha.symm (C.opens i) (C.frame i) y hy hyU hco
  change localOrder _ _ C (restrict k L D X x H 24 s) i y = _ at ho
  rw [ho]
  have hTU : T.disk (closedPoint k) ∈ U := hTy.symm ▸ hyU
  have hord := compact_scalar_stalk_order k L D X hL heven H hH s hs T U η hη hTU a ha.symm
  have hpoint : (⟨T.disk (closedPoint k), hTU⟩ : U) = ⟨p y, hyU⟩ :=
    Subtype.ext hTy
  have horder := congrArg (fun z : U =>
    ((Ring.ord (X.space.presheaf.stalk z.1)
      (X.space.presheaf.germ U z.1 z.2 a)).toNat : ℤ)) hpoint
  exact horder.symm.trans hord

/-- The accepted proper-curve theorem constructs the finite divisor once
nonvanishing has been established on this particular component. -/
lemma component_section_divisor [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    (H : Extension k L D X) (n : ℕ)
    (s : Γ(power k L D X x H n, ⊤)) (hs : s ≠ 0)
    (ι : Type) (C : NormalFrameCover (Component k L D X x)
      (power k L D X x H n) ι) :
    ∃ E : (Component k L D X x) →₀ ℤ,
      MatchesSectionOrder (Component k L D X x) (power k L D X x H n) C s E := by
  have hg := component_curve_frames k L hL heven D X x
  letI := hg.1
  exact exists_section_divisor _ k (projection k L D X x) hg.2.2.1 _ ι C s hs

end ArithmeticThetaComponentDegreeR0184.ComponentDiscriminantDivisorR0184

namespace ArithmeticThetaComponentDegreeR0184
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTensorPower ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ComponentDiscriminantDivisorR0184

/-- The intrinsic compact discriminant has divisor exactly twice the level
times the reduced actual cusp divisor on each geometric component. -/
theorem component_discriminant_divisor
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s) :
    restrict k L D X x H 24 s ≠ 0 ∧
    ∀ (ι : Type) (C : NormalFrameCover (Component k L D X x) (power k L D X x H 24) ι),
      ∃ E : (Component k L D X x) →₀ ℤ,
        MatchesSectionOrder (Component k L D X x) (power k L D X x H 24) C
          (restrict k L D X x H 24 s) E ∧
        ∀ y : Component k L D X x,
          (y ∈ cuspSet k L D X x → E y = (2 * L : ℕ)) ∧
          (y ∉ cuspSet k L D X x → E y = 0) := by
  have hs0 := component_discriminant_ne_zero k L D X x H s hs
  refine ⟨hs0, ?_⟩
  intro ι C
  obtain ⟨E, hE⟩ := component_section_divisor k L D X x hL heven H 24 _ hs0 ι C
  refine ⟨E, hE, ?_⟩
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
  rw [hE i y hi]
  exact ⟨component_discriminant_order_cusp k L D X x hL heven H hH s hs ι C i y hi,
    component_discriminant_order_interior k L D X x H s hs ι C i y hi⟩

#print axioms component_discriminant_divisor
end ArithmeticThetaComponentDegreeR0184
