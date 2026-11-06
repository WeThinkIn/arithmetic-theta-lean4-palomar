module

public import FieldCompactIsogenyAlphaR0237
public import FieldComponentGeometryR0237
public import IsogenyCanonicalHalfLineR0193

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticHalfLinesR0237
namespace FieldIsogenyHalfDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaPullback ArithmeticThetaSquareLinesR0192
open ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaArithmeticSectionsR0236
open ArithmeticThetaBoundaryConstantsR0235
open CompactHodgeLatticeExtensionR0182 ComponentDiscriminantDivisorR0184
open OpenDiscriminantFullTateExpansionR0182

/-- A flat local map between DVRs with radical residue ideal has ramification
index one. This statement uses the given ring map and its actual quotient length. -/
lemma flat_local_order (R S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (f : R →+* S)
    [IsLocalHom f] (hf : @Module.Flat R S _ _ f.toAlgebra.toModule)
    (hrad : ((IsLocalRing.maximalIdeal R).map f).IsRadical) (a : R) :
    Ring.ord S (f a) = Ring.ord R a := by
  letI := f.toAlgebra
  letI : Module.Flat R S := hf
  letI : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective R S
  have hJ : (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
    apply ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.radical_eq_maximal_of_dvr
      S _ hrad
    · exact (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr
        (IsDiscreteValuationRing.not_a_field R)
    · apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      exact ((IsLocalRing.local_hom_TFAE f).out 1 3 rfl rfl).mp inferInstance
  have h := ArithmeticThetaDegreeAssembly.ring_ord_flat_local R S a
  change Ring.ord S (f a) = Ring.ord R a *
    Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map f) at h
  rw [hJ, ← pow_one (IsLocalRing.maximalIdeal S),
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at h
  simpa using h

/-- Order is unchanged along the actual coefficient-comparison stalk map,
including at boundary points with nontrivial residue fields. -/
lemma boundary_stalk_order {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    {ι : k →+* l} {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C : Comparison k L ι D E X Y) (y : Y.space)
    (hy : y ∈ boundary l L E Y) (hx : C.compactMap y ∈ boundary k L D X)
    (r : X.space.presheaf.stalk (C.compactMap y)) :
    Ring.ord (Y.space.presheaf.stalk y) (C.compactMap.stalkMap y r) =
      Ring.ord (X.space.presheaf.stalk (C.compactMap y)) r := by
  obtain ⟨_, hdom, hdvr, _⟩ := (level_boundary_geometry k L hL heven D X).2.2 _ hx
  obtain ⟨_, hdom', hdvr', _⟩ := (level_boundary_geometry l L hL heven E Y).2.2 _ hy
  letI := hdom
  letI := hdvr
  letI := hdom'
  letI := hdvr'
  have hc := (CompactPowerExtensionDescent.coefficient_cartesian C hL heven).1
  letI : Flat C.compactMap := MorphismProperty.of_isPullback (P := @Flat) hc.flip inferInstance
  exact flat_local_order _ _ (C.compactMap.stalkMap y).hom (Flat.stalkMap _ _) 
    (ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.basechange_residue_radical
      k l X.projection Y.projection ι C.compactMap hc y) r

/-- Transfer an actual local frame coefficient to an algebraic closure and
back through the comparison stalk map. The upstairs disk represents the
chosen geometric boundary point; downstairs need not admit a rational disk. -/
lemma scalar_stalk_even (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (hH : Canonical k L H) (hgH : GeometricallyCanonical H)
    (A : OpenAlpha k L m D) (a : Γ(H.line, ⊤)) (ha : CompactRealizes k L m D X H A a)
    (U : X.space.Opens) (η : Γ(H.line, U)) (hη : IsFrame H.line U η)
    (r : Γ(X.space, U)) (hr : res H.line le_top a = r • η)
    (x : X.space) (hx : x ∈ boundary k L D X) (hxU : x ∈ U) :
    ∃ j : ℕ, Even j ∧
      ((Ring.ord (X.space.presheaf.stalk x)
        (X.space.presheaf.germ U x hxU r)).toNat : ℤ) = (j : ℤ) := by
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  obtain ⟨T⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l L hb.1
  obtain ⟨B, hB, V, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l L hb.1 hb.2.1 T
  let E : LevelData l L := ⟨T, B, hB, V, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l L hb.1 hb.2.1 E
  let C := GeometricCanonicalHodgeDescent.coefficientMap k L ι hb.1 hb.2.1 D E X Y
  obtain ⟨J, hJ, hgJ⟩ := geometric_canonical_hodge_descent l L hb.1 hb.2.1 E Y
  obtain ⟨A', _⟩ := field_open_isogeny_alpha l L m hL hm hmeven hdiv E
  obtain ⟨b, hbReal, _⟩ := compact_isogeny_alpha l L m hL hm hmeven hdiv E Y J hJ A'
  obtain ⟨e, _, he⟩ := compact_isogeny_alpha_constant_naturality k l ι L m hL hm hmeven hdiv
    D E X Y C H J hH hgH hJ hgJ A A' a b ha hbReal
  have hc := (CompactPowerExtensionDescent.coefficient_cartesian C hb.1 hb.2.1).1
  letI : Surjective C.compactMap :=
    MorphismProperty.of_isPullback (P := @Surjective) hc.flip inferInstance
  obtain ⟨y, hy⟩ := Surjective.surj (f := C.compactMap) x
  have hyc : y ∈ boundary l L E Y := by
    rintro ⟨z, hz⟩
    apply hx
    refine ⟨C.openMap z, ?_⟩
    have h := congrArg (fun f => f z) C.extendsOpen.2
    simpa only [Scheme.Hom.comp_apply, hz, hy] using h.symm
  have hyU : C.compactMap y ∈ U := hy.symm ▸ hxU
  let U' := C.compactMap ⁻¹ᵁ U
  let η' : Γ(J.line, U') := e.hom.app U' (Scheme.Modules.pullbackLocalSection C.compactMap η)
  have hη' : IsFrame J.line U' η' := frame_iso e _ (pullback_frame _ _ _ hη)
  have hr' : res J.line le_top b = C.compactMap.app U r • η' := by
    rw [← he, transportSection_restrict C.compactMap H.line J.line e a U U' le_rfl,
      InitialHodgeSection.res_self, hr, Scheme.Modules.pullbackLocalSection_smul,
      Scheme.Modules.Hom.app_smul]
  obtain ⟨W, hWy⟩ := (tate_hodge_comparison_tests l L hb.1 hb.2.1 E).2 Y y hyc
  have hWU : W.disk (closedPoint l) ∈ U' := hWy.symm ▸ hyU
  obtain ⟨j, hj, ho⟩ := IsogenyCanonicalHalfLine.scalar_stalk_order l L E Y J m hm A'
    hb.1 hb.2.1 hJ b hbReal W U' η' hη' hWU (C.compactMap.app U r) hr'
  have hpoint : (⟨W.disk (closedPoint l), hWU⟩ : U') = ⟨y, hyU⟩ := Subtype.ext hWy
  have hp := congrArg (fun z : U' =>
    ((Ring.ord (Y.space.presheaf.stalk z.1)
      (Y.space.presheaf.germ U' z.1 z.2 (C.compactMap.app U r))).toNat : ℤ)) hpoint
  rw [hp, ← Scheme.Hom.germ_stalkMap_apply C.compactMap U y hyU r,
    boundary_stalk_order hb.1 hb.2.1 C y hyc (hy.symm ▸ hx)] at ho
  have hpoint' : (⟨C.compactMap y, hyU⟩ : U) = ⟨x, hxU⟩ := Subtype.ext hy
  have hp' := congrArg (fun z : U =>
    ((Ring.ord (X.space.presheaf.stalk z.1)
      (X.space.presheaf.germ U z.1 z.2 r)).toNat : ℤ)) hpoint'
  exact ⟨j, hj, hp'.symm.trans ho⟩

/-- Evenness at every cusp of the original component. -/
lemma order_cusp (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (hH : Canonical k L H) (hgH : GeometricallyCanonical H)
    (A : OpenAlpha k L m D) (x : X.space) (a : Γ(H.line, ⊤))
    (ha : CompactRealizes k L m D X H A a) (ι : Type)
    (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)
    (i : ι) (y : Component k L D X x) (hy : y ∈ C.opens i)
    (hcusp : y ∈ cuspSet k L D X x) :
    ∃ j : ℕ, Even j ∧
      localOrder _ _ C (componentAlpha k L D X H x a) i y = (j : ℤ) := by
  letI := X.openImmersion
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  have hgeom := field_component_geometry k L hb.1 hb.2.1 D X x
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
  obtain ⟨U, η, hyU, hη⟩ := local_frame_exists H.invertible (inclusion k L D X x y)
  obtain ⟨r, hr⟩ := (hη U le_rfl).2 (res H.line le_top a)
  rw [InitialHodgeSection.res_self] at hr
  let p := inclusion k L D X x
  have ht : componentAlpha k L D X H x a =
      transportSection p H.line (hodge k L D X x H) (Iso.refl _) a := by
    simp only [transportSection, Iso.refl_hom, Scheme.Modules.Hom.id_app,
      InitialHodgeSection.res_self]
    rfl
  have ho := order_pullback_scalar p H.line _ (Iso.refl _) a _ ht
    (ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C)
    (IsogenyCanonicalHalfLine.component_ne_zero k L D X H m hm A x a ha) U η hη r hr.symm
    (C.opens i) (C.frame i) y hy hyU hco
  change localOrder _ _ C (componentAlpha k L D X H x a) i y = _ at ho
  rw [ho]
  exact scalar_stalk_even k L m hL hm hmeven hdiv D X H hH hgH A a ha
    U η hη r hr.symm (p y) hcusp hyU

end FieldIsogenyHalfDivisor

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaIsogenyHalfLinesR0193
open ArithmeticThetaBoundaryConstantsR0235

/-- The effective integral half-divisor of the normalized compact isogeny
section over its original characteristic-zero coefficient field. -/
theorem field_isogeny_half_divisor :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D, ∀ a : (H.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes k L m D X H A a → ∀ x : X.space, ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaIsogenyHalfLinesR0193.HalfDivisor k L D X H x a E := by
  intro k _ _ L m hL hm hmeven hdiv D X H hH hgH A a ha x
  classical
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  have hgeom := field_component_geometry k L hb.1 hb.2.1 D X x
  letI := hgeom.1
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hgeom.2.2.2 (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  have hne := IsogenyCanonicalHalfLine.component_ne_zero k L D X H m hm A x a ha
  obtain ⟨B, hB⟩ := exists_section_divisor _ k (projection k L D X x)
    hgeom.2.2.1 _ _ C (componentAlpha k L D X H x a) hne
  have hvalues : ∀ y, ∃ j : ℕ, Even j ∧ B y = (j : ℤ) := by
    intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    by_cases hy : y ∈ cuspSet k L D X x
    · exact FieldIsogenyHalfDivisor.order_cusp k L m hL hm hmeven hdiv
        D X H hH hgH A x a ha _ C i y hi hy
    · exact ⟨0, ⟨0, rfl⟩, by simpa using
        IsogenyCanonicalHalfLine.order_interior k L D X H m hm A x a ha _ C i y hi hy⟩
  have hoff : ∀ y, y ∉ cuspSet k L D X x → B y = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers (show y ∈ (⊤ : (Component k L D X x).Opens) by trivial))
    rw [hB i y hi]
    exact IsogenyCanonicalHalfLine.order_interior k L D X H m hm A x a ha _ C i y hi hy
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

#print axioms FieldIsogenyHalfDivisor.flat_local_order
#print axioms FieldIsogenyHalfDivisor.boundary_stalk_order
#print axioms FieldIsogenyHalfDivisor.scalar_stalk_even
#print axioms field_isogeny_half_divisor
end ArithmeticThetaArithmeticHalfLinesR0237
