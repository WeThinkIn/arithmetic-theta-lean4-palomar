module

public import RationalMorphismOpenR0266
public import LegendreLevelFamilyConstructionR0176
public import ArithmeticInvariantRatioRealizationR0265

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaInvariantRatiosR0265
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
namespace GlobalArithmeticProjectiveRatios
open Arithmetic

lemma geometric_data (k : Type) [Field k] [CharZero k] (m : ℕ)
    (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m)) :
    ∃ (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
      (Vd : DiskTest k (2*m) D X), CanonicalMarking k (2*m) (ζ : k) Vd.level := by
  have hL : 3 ≤ 2*m := by obtain ⟨r, hr⟩ := he; omega
  have heven : Even (2*m) := even_two_mul m
  obtain ⟨atlas⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction k (2*m) hL
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction k (2*m) hL heven atlas
  let D : LevelData k (2*m) := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨X⟩ := smooth_projective_level_completion k (2*m) hL heven D
  obtain ⟨E, hE⟩ := tate_full_level_marking k (2*m) hL heven (ζ : k) hζ
  obtain ⟨b, hb, _⟩ := TateLevelClassifyingParameter.classifying_exists_unique k (2*m) hL heven D E
  obtain ⟨T, hTE, hTb⟩ := (tate_hodge_comparison_tests k (2*m) hL heven D).1 E b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension k (2*m) hL heven D E X b hb
  let Vd : DiskTest k (2*m) D X := { toTest := T, disk := disk, extends_eq := hTb.symm ▸ hdisk }
  refine ⟨D, X, Vd, ?_⟩
  change CanonicalMarking k (2*m) (ζ : k) T.level
  rwa [hTE]

variable (k : Type) [Field k] [CharZero k] (m : ℕ)
  (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (Vd : DiskTest k (2*m) D X)

lemma tate_pointed : (ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level).zero ≫ Vd.map =
    tateBase k m D X Vd ≫ (globalFamily k m D).zero := by
  rw [ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero]
  exact Vd.classifies.2.2.1

lemma interior_chart : ∃ C : GenericChart (compactComponent k m D X Vd)
    (globalBase k m D) (genericBase k m D X Vd), IsInteriorChart k m D X Vd C := by
  let Z := compactComponent k m D X Vd
  let inc := inclusion k (2*m) D X (Vd.disk (closedPoint k))
  letI := X.openImmersion
  let U : Z.Opens := inc ⁻¹ᵁ X.inclusion.opensRange
  let j : U.toScheme ⟶ OpenBase k (2*m) D :=
    IsOpenImmersion.lift X.inclusion (U.ι ≫ inc) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)
  have hj : j ≫ X.inclusion = U.ι ≫ inc := IsOpenImmersion.lift_fac _ _ _
  let η := Z.fromSpecStalk (genericPoint Z)
  let q := GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X (Vd.disk (closedPoint k))
  have hq : q ≫ X.inclusion = η ≫ inc :=
    GeometricComponentCuspBoundR0184.componentGenericOpen_inclusion k (2*m) D X (Vd.disk (closedPoint k))
  have hr : Set.range η ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change inc (η x) ∈ Set.range X.inclusion
    exact ⟨q x, congrArg (fun f => f x) hq⟩
  let ηU := IsOpenImmersion.lift U.ι η hr
  have hη : ηU ≫ U.ι = η := IsOpenImmersion.lift_fac _ _ _
  have hηj : ηU ≫ j = q := by
    apply (cancel_mono X.inclusion).mp
    rw [Category.assoc, hj, ← Category.assoc, hη, hq]
  let C : GenericChart Z (globalBase k m D) (genericBase k m D X Vd) := {
    domain := U
    nonempty := ⟨ηU (Classical.arbitrary (Spec (CommRingCat.of Z.functionField)))⟩
    map := j ≫ D.quotient.inclusion
    generic := ηU
    generic_eq := hη
    map_eq := by rw [← Category.assoc, hηj]; rfl }
  exact ⟨C, j, hj, rfl⟩

lemma interior_refines {C C' : GenericChart (compactComponent k m D X Vd)
    (globalBase k m D) (genericBase k m D X Vd)}
    (hC : IsInteriorChart k m D X Vd C)
    (h : Refines (genericBase k m D X Vd) C C') : IsInteriorChart k m D X Vd C' := by
  obtain ⟨j, hj, hmap⟩ := hC
  obtain ⟨i, _, hi, himap, _⟩ := h
  refine ⟨i ≫ j, ?_, ?_⟩
  · rw [Category.assoc, hj, ← Category.assoc, hi]
  · rw [Category.assoc, hmap, himap]

open InvariantRatioFieldDescent
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

/-- Descent concerns the pullback of the original global morphisms. -/
lemma generic_denominator {F K : Type} [Field F] [Field K] {S : Scheme}
    (g : Base F ⟶ S) (θ : F →+* K) (t : Base K ⟶ S)
    (ht : Spec.map (CommRingCat.ofHom θ) ≫ g = t)
    {M N : S.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) (d : M ⟶ N)
    (hd : IsIso ((Scheme.Modules.pullback t).map d)) :
    IsIso ((Scheme.Modules.pullback g).map d) := by
  let b := Spec.map (CommRingCat.ofHom θ)
  have hiter : IsIso ((Scheme.Modules.pullback b).map ((Scheme.Modules.pullback g).map d)) := by
    apply (RationalMorphismOpen.pullback_comp_iso b g d).mpr
    rwa [ht]
  apply line_nonzero_iso (hM.pullback g) (hN.pullback g)
  intro hz
  letI := hiter
  apply iso_ne_zero ((hM.pullback g).pullback b)
    ((Scheme.Modules.pullback b).map ((Scheme.Modules.pullback g).map d))
  rw [hz, Functor.map_zero]

lemma generic_scalar_image {F K : Type} [Field F] [Field K] {S : Scheme}
    (g : Base F ⟶ S) (θ : F →+* K) (t : Base K ⟶ S)
    (ht : Spec.map (CommRingCat.ofHom θ) ≫ g = t)
    {M N : S.Modules} (hN : Scheme.Modules.IsInvertible N) (d v : M ⟶ N)
    (hd : IsIso ((Scheme.Modules.pullback t).map d)) (r : F) (s : K)
    (hr : (Scheme.Modules.pullback g).map v =
      (Scheme.Modules.pullback g).map d ≫ scalarEnd ((Scheme.Modules.pullback g).obj N) r)
    (hs : (Scheme.Modules.pullback t).map v =
      (Scheme.Modules.pullback t).map d ≫ scalarEnd ((Scheme.Modules.pullback t).obj N) s) :
    θ r = s := by
  let b := Spec.map (CommRingCat.ofHom θ)
  have hi := congrArg (fun f => (Scheme.Modules.pullback b).map f) hr
  rw [Functor.map_comp, scalar_pullback] at hi
  have hh := RationalMorphismOpen.transport_scalar_equation b g d v
    ((Scheme.ΓSpecIso (.of K)).inv.hom (θ r)) hi
  rw [ht] at hh
  letI := hd
  apply scalar_injective (hN.pullback t)
  apply (cancel_epi ((Scheme.Modules.pullback t).map d)).mp
  exact hh.symm.trans hs

open ArithmeticInvariantRatioRealization SchemeDoubledTorsionLift

lemma realization (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) Vd.level) :
    GlobalRealization k m D X Vd hm he ζ hζ := by
  let E := globalFamily k m D
  let F := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let M := globalLevel k m D
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := tateBase k m D X Vd
  have hc : IsPullback Vd.map F.p E.p t := Vd.classifies.2.1
  have hz : F.zero ≫ Vd.map = t ≫ E.zero := tate_pointed k m D X Vd
  have hmul : Multiplicative E F t Vd.map :=
    pointed_cartesian_group_law k _ _ σ E F t Vd.map hc hz
  obtain ⟨Q, _, _, _, i, a, b, _, ha, hb, _, _, hglobal⟩ :=
    ArithmeticThetaTateSchemeMarkingR0263.global_literal_tate_marking k m hm he Vd.level ζ hζ hmark
  obtain ⟨I, α₀, β₀, hI, hα₀, hβ₀, hsα₀, hsβ₀, signs, hsigns, _⟩ :=
    hglobal _ σ E M t Vd.map hc hz hmul Vd.classifies.2.2.2.1 Vd.classifies.2.2.2.2
  let α := scaled E m (signUnit _ signs.1) α₀
  let β := scaled E m (signUnit _ signs.2) β₀
  let A := ActionRelations.thetaAction E m M.x α
  let B := ActionRelations.thetaAction E m M.y β
  let A' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level) a
  let B' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level) b
  have hA : IsAction E m (translation E M.x) α A :=
    ⟨translation_over E M.x, PushforwardAction.formula _ _ _ _ _⟩
  have hB : IsAction E m (translation E M.y) β B :=
    ⟨translation_over E M.y, PushforwardAction.formula _ _ _ _ _⟩
  have hA' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hB' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hpA : A ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_x α₀ hα₀ signs.1
  have hpB : B ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_y β₀ hβ₀ signs.2
  obtain ⟨c, hcmt, _⟩ := scheme_primitive_theta_commutator k _ σ E m hm he M α β
  have hrel : Relations m A B c := ⟨hpA, hpB, action_commutator E m _ _ α β c hcmt.1⟩
  have hline := scheme_invariant_theta_line k _ σ E m hm A B c hrel hcmt.2
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  have horbit := scheme_schrodinger_orbit k _ σ (V E m) m hm A B c hrel hcmt.2
  have hvalue : Scheme.Modules.IsInvertible (commonValueLine E m A) :=
    hline.dual.1.tensor_monoidalV2 hfiber
  have hpush := scheme_pushforward_intertwining k _ σ E _ F t Vd.map hc hz m hm
  have hAA := hpush.2 _ _ α a A A' hsigns.1 hA hA'
  have hBB := hpush.2 _ _ β b B B' hsigns.2 hB hB'
  have hcmp := scheme_invariant_component_naturality k _ σ E _ F t Vd.map hc hz
    m hm A B A' B' hpA hAA hBB
  have hrat := tate_invariant_component_ratios k m hm he Vd.level ζ hζ Q a b ha hb A' B' hA' hB'
  obtain ⟨test⟩ := test_exists k m D X Vd
  let g := genericBase k m D X Vd
  have ht : Spec.map (CommRingCat.ofHom test.scalar) ≫ g = t := by
    change Spec.map (CommRingCat.ofHom test.scalar) ≫
      (GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X (Vd.disk (closedPoint k)) ≫
        D.quotient.inclusion) = _
    rw [← Category.assoc, test.base_eq]
  let P := Scheme.Modules.pullback t
  let z : Fin m := ⟨0, hm⟩
  let d := component E m A B z
  let d' := component F m A' B' z
  let eN := fiberComparison E F t Vd.map hc hz m
  have hcomparison := hcmp
  obtain ⟨e, heq, _⟩ := hcomparison
  have H (j : Fin m) : P.map (component E m A B j) ≫ eN.hom =
      e.hom ≫ component F m A' B' j := heq.2.2 j
  have hdT : IsIso (P.map d) := by
    letI : IsIso d' := hrat.1
    have hdEq : P.map d = e.hom ≫ d' ≫ eN.inv := by
      rw [← Category.assoc, ← H z, Category.assoc, eN.hom_inv_id, Category.comp_id]
    rw [hdEq]
    infer_instance
  have hsT (j : Fin m) : P.map (component E m A B j) =
      P.map d ≫ scalarEnd (P.obj ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)))
        (unaryRatio k m hm j) := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, scalar_natural, ← Category.assoc, H z, Category.assoc, ← hrat.2 j]
    exact H j
  have hdG := generic_denominator g test.scalar t ht hline hfiber d hdT
  obtain ⟨C, hC⟩ := interior_chart k m D X Vd
  obtain ⟨r, ⟨hr, C', hCC', hreg⟩, _⟩ := rational_morphism_open
    (compactComponent k m D X Vd) (globalBase k m D) g C
    (fixed A) ((Scheme.Modules.pullback E.zero).obj (thetaLine E m))
    d m (fun j => component E m A B j) hline hfiber hdG
  have himage (j : Fin m) : test.scalar (r j) = unaryRatio k m hm j :=
    generic_scalar_image g test.scalar t ht hfiber d (component E m A B j)
      hdT (r j) (unaryRatio k m hm j) (hr.2 j) (hsT j)
  refine ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsigns.1, hsigns.2, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hcmt.2, hline, horbit, hvalue, hcmp, hrat,
    C', r, test, interior_refines k m D X Vd hC hCC', hr, hreg, himage, ?_⟩
  intro j
  exact (rationalExpansion_iff k (compactComponent k m D X Vd) (genericInclusion k ≫ test.disk)
    test.scalar test.generic_eq (r j) (unaryRatio k m hm j)).mpr (himage j)

end GlobalArithmeticProjectiveRatios

/-- Global arithmetic quotients on the original selected compact component,
with their regular representatives and full canonical Tate expansions. -/
theorem global_arithmetic_projective_ratios :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := by
  intro k _ _ m hm he ζ hζ
  obtain ⟨D, X, Vd, hmark⟩ := GlobalArithmeticProjectiveRatios.geometric_data k m hm he ζ hζ
  exact ⟨D, X, Vd, hmark, GlobalArithmeticProjectiveRatios.realization k m D X Vd hm he ζ hζ hmark⟩

#print axioms global_arithmetic_projective_ratios
end ArithmeticThetaGlobalProjectiveRatiosR0266
