module

public import ComponentDiscriminantDivisorR0184
public import FieldComponentGeometryR0237
public import GeometricCanonicalHodgeDescentR0235

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaCyclotomicModularityR0239
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot ArithmeticThetaSectionOrder ArithmeticThetaTateCuspsR0181
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaComponentDegreeR0184.ComponentDiscriminantDivisorR0184
open CompactHodgeLatticeExtensionR0182 CompactDiscriminantSectionR0182

namespace SplitDiscriminantDivisor
variable (k : Type) [Field k] [CharZero k] (L : ℕ)

private lemma split_local_lifts (hL : 3 ≤ L) (heven : Even L)
    (A : TateLevel k L) (D : LevelData k L) (X : Compactification k L D)
    (H : Extension k L D X) (hH : Canonical k L H)
    (d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤)) (hd : ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d) :
    ∀ x : X.space, ∃ (V : X.space.Opens) (s : Γ(tensorPower X.space H.line 24, V)), x ∈ V ∧
      (tensorComparison X.inclusion H.line (openHodge k L D) H.onOpen 24).hom.app _
        (Scheme.Modules.pullbackLocalSection X.inclusion s) =
      res (openPower k L D 24) (show X.inclusion ⁻¹ᵁ V ≤ ⊤ from le_top) (pullToOpen k L 24 d) := by
  letI := X.openImmersion
  intro x
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨s, hs⟩ := section_lift_open X.inclusion (tensorPower X.space H.line 24)
      (openPower k L D 24) (tensorComparison X.inclusion H.line _ H.onOpen 24) (pullToOpen k L 24 d)
    exact ⟨X.inclusion.opensRange, s, hx, hs⟩
  · obtain ⟨T, hTx⟩ := ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent.tests_cover_of_tateLevel
      k L hL heven A D X x hx
    obtain ⟨U, e, hxU, he, hUI⟩ := integral_frame_neighborhood k L H x
    letI := hUI
    have hTU : T.disk (closedPoint k) ∈ U := hTx ▸ hxU
    let σ := H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)
    have hσ : IsFrame (openHodge k L D) (X.inclusion ⁻¹ᵁ U) σ :=
      frame_iso H.onOpen _ (pullback_frame _ _ _ he)
    obtain ⟨r, hr⟩ := (tensorPower_frame _ σ hσ 24 (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (res (openPower k L D 24) le_top (pullToOpen k L 24 d))
    rw [InitialHodgeSection.res_self] at hr
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    obtain ⟨β, hβU, hβ, a, ha⟩ := canonical_scalar_stalk_integral
      k L hL heven H hH T U e he hTU d hd r hr.symm
    obtain ⟨V, hTV, hVU, q, hq⟩ := local_scalar_lift X.inclusion
      (T.disk (closedPoint k)) U hTU β hβ hβU r a ha
    refine ⟨V, q • tensorPowerSection X.space H.line 24 V (res H.line hVU e),
      hTx ▸ hTV, ?_⟩
    exact tensor_lift_of_scalar X.inclusion H.line (openHodge k L D) H.onOpen 24
      (pullToOpen k L 24 d) U e r hr.symm V hVU q hq


variable (D : LevelData k L) (X : Compactification k L D) (x : X.space)

private lemma split_power_line (H : Extension k L D X) (n : ℕ)
    (hn : NormalAffine (Component k L D X x)) :
    IsLineBundle (Component k L D X x) (power k L D X x H n) := by
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hn (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  exact ArithmeticThetaDegreeAssembly.tensorPower_isLineBundle _ _ C n

private lemma split_cusp_order (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (ι : Type) (C : NormalFrameCover (Component k L D X x) (power k L D X x H 24) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hcusp : y ∈ cuspSet k L D X x) :
    localOrder _ _ C (restrict k L D X x H 24 s) i y = (2 * L : ℕ) := by
  letI := X.openImmersion
  have hgeom := ArithmeticThetaArithmeticHalfLinesR0237.field_component_geometry k L hL heven D X x
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
  obtain ⟨T, hTy⟩ := ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent.tests_cover_of_tateLevel
    k L hL heven A D X (inclusion k L D X x y) hcusp
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
    (split_power_line k L D X x H 24 hgeom.2.2.2) (component_discriminant_ne_zero k L D X x H s hs)
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

end SplitDiscriminantDivisor

theorem split_compact_discriminant :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k), IsPrimitiveRoot ζ L → 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∃ s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s := by
  intro k _ _ L ζ hζ hL heven D X x H hH
  obtain ⟨A, _⟩ := tate_full_level_marking k L hL heven ζ hζ
  obtain ⟨d, hd, _⟩ := ArithmeticThetaOpenHodgeR0180.global_family_discriminant
    k D.atlas.quotient.ring D.atlas.quotient.smooth D.atlas.descent.family
  letI := X.openImmersion
  letI := compact_noetherian k L D X
  letI := inclusion_schematic k L D X
  obtain ⟨s, hs, _⟩ := existsUnique_extension_of_local_lifts X.inclusion
    (tensorPower X.space H.line 24) (tensorPower_invertible H.line H.invertible 24)
    (openPower k L D 24) (tensorComparison X.inclusion H.line _ H.onOpen 24)
    (pullToOpen k L 24 d) (SplitDiscriminantDivisor.split_local_lifts k L hL heven A D X H hH d hd)
  exact ⟨s, d, hd, hs⟩

theorem split_component_discriminant_divisor :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) ≠ 0 ∧ ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) ι), ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) C (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) E ∧ ∀ y : ArithmeticThetaComponentDegreeR0184.Component k L D X x, (y ∈ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = (2*L : ℕ)) ∧ (y ∉ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = 0) := by
  intro k _ _ L ζ hζ hL heven D X x H hH s hs
  obtain ⟨A, _⟩ := tate_full_level_marking k L hL heven ζ hζ
  have hg := ArithmeticThetaArithmeticHalfLinesR0237.field_component_geometry k L hL heven D X x
  letI := hg.1
  have hs0 := component_discriminant_ne_zero k L D X x H s hs
  refine ⟨hs0, ?_⟩
  intro ι C
  obtain ⟨E, hE⟩ := exists_section_divisor _ k (projection k L D X x) hg.2.2.1 _ ι C _ hs0
  refine ⟨E, hE, ?_⟩
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
  rw [hE i y hi]
  exact ⟨SplitDiscriminantDivisor.split_cusp_order k L D X x hL heven A H hH s hs ι C i y hi,
    component_discriminant_order_interior k L D X x H s hs ι C i y hi⟩

#print axioms split_compact_discriminant
#print axioms split_component_discriminant_divisor
end ArithmeticThetaCyclotomicModularityR0239
