module

public import NormalLineFrames
public import NormalOrderCriterion
public import SectionOrderDefinitions
public import AffineOrderRegularity
public import CurveDegreeDefinitions
public import ResidueDegrees

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaCurveDegree

universe u
noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ArithmeticThetaGeometricPrerequisites

/-- A codimension-one point has a rational uniformizer induced by its actual stalk map. -/
theorem exists_rational_uniformizer
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (x : X) (hx : Order.coheight x = 1) :
    ∃ r : X.functionField, r ≠ 0 ∧ Scheme.ord r x = 1 := by
  letI := ArithmeticThetaSectionCompletion.normal_stalk_dvr X hN x hx
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hr : algebraMap (X.presheaf.stalk x) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  refine ⟨algebraMap (X.presheaf.stalk x) X.functionField t, hr, ?_⟩
  rw [Scheme.ord_eq_iff hx hr]
  exact Ring.ordFrac_irreducible ht

/-- The rational uniformizer is represented by a regular function near its point. -/
theorem exists_regular_uniformizer
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (x : X) (hx : Order.coheight x = 1) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U)),
      a ≠ 0 ∧ @Scheme.ord X _ _
        (@Scheme.germToFunctionField X _ U ⟨⟨x, hxU⟩⟩ a) x = 1 := by
  letI := ArithmeticThetaSectionCompletion.normal_stalk_dvr X hN x hx
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨U, hxU, a, ha⟩ := X.presheaf.exists_germ_eq t
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have ha0 : a ≠ 0 := by
    intro h
    apply ht.ne_zero
    rw [← ha, h, map_zero]
  refine ⟨U, hxU, a, ha0, ?_⟩
  have hr : X.germToFunctionField U a ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective U)).mpr ha0
  rw [Scheme.ord_eq_iff hx hr, ← Scheme.algebraMap_germ_eq_germToFunctionField X hxU a, ha]
  exact Ring.ordFrac_irreducible ht

set_option linter.style.haveILetI false
/-- Rational sections are rational functions on nonempty opens and the zero module on the empty open. -/
abbrev RationalSections (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :=
  PLift (Nonempty U) → X.functionField

def rationalScalars (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    Γ(X, U) →+* RationalSections X U where
  toFun a h := @Scheme.germToFunctionField X _ U h.down a
  map_one' := by ext h; exact map_one _
  map_zero' := by ext h; exact map_zero _
  map_add' a b := by ext h; exact map_add _ a b
  map_mul' a b := by ext h; exact map_mul _ a b

instance rationalSectionsModule (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    Module Γ(X, U) (RationalSections X U) :=
  Module.compHom _ (rationalScalars X U)

def rationalRestrict (X : Scheme.{u}) [IsIntegral X] {U V : X.Opens} (h : V ≤ U)
    (f : RationalSections X U) : RationalSections X V :=
  fun hV ↦ f ⟨⟨⟨(Classical.choice hV.down).1, h (Classical.choice hV.down).2⟩⟩⟩

def rationalPresheaf (X : Scheme.{u}) [IsIntegral X] :
    PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of Γ(X, U.unop) (RationalSections X U.unop)
  map {U V} h := by
    rcases U with ⟨U⟩
    rcases V with ⟨V⟩
    refine ModuleCat.semilinearMapAddEquiv (X.presheaf.map h).hom _ _ ?_
    exact
      { toFun := rationalRestrict X h.unop.le
        map_add' _ _ := rfl
        map_smul' a f := by
          ext hV
          letI : Nonempty V := hV.down
          letI : Nonempty U := ⟨⟨(Classical.choice hV.down).1, h.unop.le (Classical.choice hV.down).2⟩⟩
          change X.germToFunctionField U a * _ =
            X.germToFunctionField V (X.presheaf.map h a) * _
          have hh : h = (homOfLE h.unop.le).op := Subsingleton.elim _ _
          rw [hh, germ_restrict X U V h.unop.le]
          rfl }
  map_id U := by ext f; rfl
  map_comp f g := by ext a; rfl

/-- The ordinary bounded-pole submodule on an open, with the zero function included explicitly. -/
def boundedSections (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (U : X.Opens) :
    Submodule Γ(X, U) (RationalSections X U) where
  carrier := {f | ∀ (h : PLift (Nonempty U)) (x : X), x ∈ U →
    f h = 0 ∨ -D x ≤ Scheme.ord (f h) x}
  zero_mem' := by intro h x hx; exact Or.inl rfl
  add_mem' := by
    intro f g hf hg h x hx
    by_cases hfg : f h + g h = 0
    · exact Or.inl hfg
    right
    rcases hf h x hx with hf0 | hf0
    · simpa [hf0] using (hg h x hx).resolve_left (by simpa [hf0] using hfg)
    rcases hg h x hx with hg0 | hg0
    · simpa [hg0] using hf0
    by_cases hco : Order.coheight x = 1
    · letI := ArithmeticThetaSectionCompletion.normal_stalk_dvr X hN x hco
      exact (le_min hf0 hg0).trans (Scheme.ord_add hfg)
    · simpa [Scheme.ord_eq_zero_of_coheight_neq_one hco] using hf0
  smul_mem' := by
    intro a f hf h x hx
    letI : Nonempty U := h.down
    change X.germToFunctionField U a * f h = 0 ∨ _
    by_cases ha : a = 0
    · left; simp [ha]
    rcases hf h x hx with hf0 | hf0
    · left; simp [hf0]
    · right
      exact hf0.trans (Scheme.ord_le_smul hx ha (f h))

def divisorSubpresheaf (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) : (rationalPresheaf X).Submodule where
  obj U := boundedSections X hN D U.unop
  map f := by
    intro a ha h x hx
    exact ha ⟨⟨⟨x, f.unop.le hx⟩⟩⟩ x (f.unop.le hx)

abbrev divisorPresheaf (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) :=
  (divisorSubpresheaf X hN D).toPresheafOfModules

/-- Bounded-pole rational sections satisfy the actual sheaf condition. -/
theorem divisorPresheaf_isSheaf (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) :
    TopCat.Presheaf.IsSheaf (divisorPresheaf X hN D).presheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hc
  have hex (h : Nonempty (iSup U : X.Opens)) : ∃ i, Nonempty (U i) := by
    obtain ⟨x, hx⟩ := h
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x, hi⟩⟩⟩
  choose idx hidx using hex
  let value (h : PLift (Nonempty (iSup U : X.Opens))) : X.functionField :=
    (sf (idx h.down)).val ⟨hidx h.down⟩
  have heq (h : PLift (Nonempty (iSup U : X.Opens))) (j : ι) (hj : Nonempty (U j)) :
      value h = (sf j).val ⟨hj⟩ := by
    letI : Nonempty (U (idx h.down)) := hidx h.down
    letI : Nonempty (U j) := hj
    letI := overlap_nonempty X (U (idx h.down)) (U j)
    have hcomp := hc (idx h.down) j
    exact congrArg (fun s : boundedSections X hN D (U (idx h.down) ⊓ U j) ↦
      s.val ⟨inferInstance⟩) hcomp
  let s : boundedSections X hN D (iSup U) := ⟨value, by
    intro h x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    rw [heq h j ⟨⟨x, hj⟩⟩]
    exact (sf j).property _ x hj⟩
  refine ⟨s, ?_, ?_⟩
  · intro j
    apply Subtype.ext
    funext h
    exact heq ⟨⟨⟨(Classical.choice h.down).1, (le_iSup U j) (Classical.choice h.down).2⟩⟩⟩ j h.down
  · intro s' hs'
    apply Subtype.ext
    funext h
    have hj := hs' (idx h.down)
    exact congrArg (fun t : boundedSections X hN D (U (idx h.down)) ↦
      t.val ⟨hidx h.down⟩) hj

/-- The genuine module sheaf O(D), constructed as bounded-pole rational functions. -/
def divisorSheaf (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) : X.Modules where
  val := divisorPresheaf X hN D
  isSheaf := divisorPresheaf_isSheaf X hN D

theorem rational_order_one (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) : Scheme.ord (1 : X.functionField) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · simp [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, WithZero.unzeroD]
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx 1

/-- The canonical section of an effective divisor is the rational function one. -/
def divisorCanonicalSection (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (hD : ∀ x, 0 ≤ D x) :
    Γ(divisorSheaf X hN D, ⊤) :=
  ⟨fun _ ↦ 1, by
    intro h x hx
    right
    simpa [rational_order_one] using neg_nonpos.mpr (hD x)⟩

theorem divisorCanonicalSection_ne_zero
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (hD : ∀ x, 0 ≤ D x) :
    divisorCanonicalSection X hN D hD ≠ 0 := by
  intro h
  have h10 : (1 : X.functionField) = 0 :=
    congrArg (fun t : boundedSections X hN D ⊤ ↦
      t.val ⟨⟨⟨genericPoint X, by trivial⟩⟩⟩) h
  exact one_ne_zero h10

theorem regular_order_nonnegative (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (x : X) (hx : x ∈ U) :
    0 ≤ Scheme.ord (X.germToFunctionField U a) x := by
  by_cases ha : a = 0
  · simp [ha]
  have h := Scheme.ord_le_smul hx ha (1 : X.functionField)
  simpa only [rational_order_one, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one] using h

/-- Affine regularity glues to every nonempty open; no quasi-compactness is assumed. -/
theorem normal_open_order_criterion
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (U : X.Opens) [Nonempty U] (r : X.functionField) :
    (∀ x ∈ U, 0 ≤ Scheme.ord r x) ↔ ∃ a : Γ(X, U), X.germToFunctionField U a = r := by
  classical
  constructor
  · intro hr
    have hn (x : U) : ∃ V : X.Opens, x.1 ∈ V ∧ IsAffineOpen V ∧ V ≤ U := by
      obtain ⟨V, hV, hx, hVU⟩ := exists_isAffineOpen_mem_and_subset x.2
      exact ⟨V, hx, hV, hVU⟩
    choose V hx hV hVU using hn
    have hne (x : U) : Nonempty (V x) := ⟨⟨x.1, hx x⟩⟩
    have hsec (x : U) : ∃ a : Γ(X, V x), @Scheme.germToFunctionField X _ (V x) (hne x) a = r := by
      letI := hne x
      letI := hN (V x) (hV x)
      exact (ArithmeticThetaSectionCompletion.normal_affine_order_criterion X (V x) (hV x) r).mp
        (fun y hy ↦ hr y (hVU x hy))
    choose a ha using hsec
    have hc : TopCat.Presheaf.IsCompatible X.presheaf V a := by
      intro x y
      letI := hne x
      letI := hne y
      letI := overlap_nonempty X (V x) (V y)
      apply X.germToFunctionField_injective (V x ⊓ V y)
      exact (germ_restrict X (V x) (V x ⊓ V y) inf_le_left (a x)).trans
        ((ha x).trans ((ha y).symm.trans
          (germ_restrict X (V y) (V x ⊓ V y) inf_le_right (a y)).symm))
    have hcov : U ≤ iSup V := by
      intro x hxU
      exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
    obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf V U
      (fun x ↦ homOfLE (hVU x)) hcov a hc
    refine ⟨s, ?_⟩
    let x : U := Classical.choice ‹Nonempty (U : Set X)›
    letI := hne x
    have h := congrArg (X.germToFunctionField (V x)) (hs x)
    exact (germ_restrict X U (V x) (hVU x) s).symm.trans (h.trans (ha x))
  · rintro ⟨a, rfl⟩ x hx
    exact regular_order_nonnegative X U a x hx

/-- Multiplying by a local equation identifies bounded-pole rational sections with regular sections. -/
def equationFrameMap (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (U : X.Opens) (r : X.functionField)
    (hr : r ≠ 0) (hord : ∀ x ∈ U, Scheme.ord r x = D x)
    (V : X.Opens) (hVU : V ≤ U) :
    Γ(X, V) →ₗ[Γ(X, V)] boundedSections X hN D V where
  toFun a := ⟨fun h ↦ @Scheme.germToFunctionField X _ V h.down a / r, by
    intro h x hx
    letI : Nonempty V := h.down
    by_cases ha : a = 0
    · left; simp [ha]
    right
    have ha0 : X.germToFunctionField V a ≠ 0 :=
      (map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr ha
    have heq : (X.germToFunctionField V a / r) * r = X.germToFunctionField V a :=
      div_mul_cancel₀ _ hr
    have ho := congrArg (fun t : X.functionField ↦ Scheme.ord t x) heq
    rw [Scheme.ord_mul (div_ne_zero ha0 hr) hr, hord x (hVU hx)] at ho
    have hp := regular_order_nonnegative X V a x hx
    change -D x ≤ Scheme.ord (X.germToFunctionField V a / r) x
    omega⟩
  map_add' a b := by
    apply Subtype.ext
    funext h
    exact (congrArg (fun t : X.functionField ↦ t / r) (map_add _ a b)).trans (add_div _ _ _)
  map_smul' a b := by
    apply Subtype.ext
    funext h
    letI : Nonempty V := h.down
    change X.germToFunctionField V (a * b) / r = X.germToFunctionField V a *
      (X.germToFunctionField V b / r)
    rw [map_mul, mul_div_assoc]

theorem equationFrameMap_bijective (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (U : X.Opens) (r : X.functionField)
    (hr : r ≠ 0) (hord : ∀ x ∈ U, Scheme.ord r x = D x)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective (equationFrameMap X hN D U r hr hord V hVU) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    constructor
    · intro a b hab
      apply X.germToFunctionField_injective V
      apply (div_left_inj' hr).mp
      exact congrArg (fun t : boundedSections X hN D V ↦ t.val ⟨hV⟩) hab
    · intro t
      have ht : ∀ x ∈ V, 0 ≤ Scheme.ord (t.val ⟨hV⟩ * r) x := by
        intro x hx
        rcases t.property ⟨hV⟩ x hx with ht0 | htord
        · simp [ht0]
        by_cases ht0 : t.val ⟨hV⟩ = 0
        · simp [ht0]
        rw [Scheme.ord_mul ht0 hr, hord x (hVU hx)]
        omega
      obtain ⟨a, ha⟩ := (normal_open_order_criterion X hN V (t.val ⟨hV⟩ * r)).mp ht
      refine ⟨a, ?_⟩
      apply Subtype.ext
      funext h
      change X.germToFunctionField V a / r = t.val h
      rw [ha, mul_div_cancel_right₀ _ hr]
  · have hVbot : V = ⊥ := by
      ext x
      exact ⟨fun hx ↦ False.elim (hV ⟨⟨x, hx⟩⟩), False.elim⟩
    subst V
    letI : Subsingleton Γ(X, ⊥) := inferInstance
    haveI : Subsingleton (boundedSections X hN D ⊥) :=
      ⟨fun a b ↦ Subtype.ext (funext fun h ↦ False.elim (hV h.down))⟩
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun t ↦ ⟨0, Subsingleton.elim _ _⟩⟩

def equationFrame (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (U : X.Opens) (r : X.functionField)
    (hr : r ≠ 0) (hord : ∀ x ∈ U, Scheme.ord r x = D x) :
    LocalFrame X (divisorSheaf X hN D) U where
  equiv V hVU := LinearEquiv.ofBijective (equationFrameMap X hN D U r hr hord V hVU)
    (equationFrameMap_bijective X hN D U r hr hord V hVU)
  naturality V W hWV hVU a := by
    apply Subtype.ext
    funext h
    letI : Nonempty W := h.down
    letI : Nonempty V := ⟨⟨(Classical.choice h.down).1, hWV (Classical.choice h.down).2⟩⟩
    change X.germToFunctionField V a / r =
      X.germToFunctionField W (X.presheaf.map (homOfLE hWV).op a) / r
    rw [germ_restrict]

/-- A nonzero function has finitely many zeroes on a Noetherian affine curve. -/
theorem finite_affine_zero_locus
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] (a : R) (ha : a ≠ 0) :
    (PrimeSpectrum.zeroLocus ({a} : Set R)).Finite := by
  let I : Ideal R := Ideal.span ({a} : Set R)
  have hmin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  have hsub : PrimeSpectrum.zeroLocus ({a} : Set R) ⊆
      (fun p : I.minimalPrimes ↦ (⟨p.1, p.2.1.1⟩ : PrimeSpectrum R)) '' (Set.univ : Set I.minimalPrimes) := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
      (I := I) (J := p.asIdeal) (Ideal.span_le.mpr (by simpa [I] using hp))
    have haq : a ∈ q := Ideal.span_le.mp hq.1.2 (by simp)
    have hqne : q ≠ ⊥ := by
      intro hq0
      exact ha (by simpa [hq0] using haq)
    have hqmax : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hqne hq.1.1
    have hpeq : q = p.asIdeal := hqmax.eq_of_le p.isPrime.ne_top hqp
    exact ⟨⟨q, hq⟩, trivial, PrimeSpectrum.ext hpeq⟩
  letI : Finite I.minimalPrimes := hmin.to_subtype
  exact ((Set.toFinite (Set.univ : Set I.minimalPrimes)).image _).subset hsub

theorem order_zero_of_unit_germ
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (x : X) (hx : x ∈ U) (a : Γ(X, U))
    (ha : IsUnit (X.presheaf.germ U x hx a)) :
    Scheme.ord (X.germToFunctionField U a) x = 0 := by
  by_cases hco : Order.coheight x = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hco.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hco]
    have h1 : Scheme.ordHom x hco (X.germToFunctionField U a) = 1 := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx a]
      exact Ring.ordFrac_of_isUnit ha
    rw [h1]
    simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hco _

theorem finite_regular_order_support
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (a : Γ(X, U)) (ha : a ≠ 0) :
    Set.Finite {x : X | x ∈ U ∧ Scheme.ord (X.germToFunctionField U a) x ≠ 0} := by
  letI : Ring.DimensionLEOne Γ(X, U) := hcurve U hU
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f : U → PrimeSpectrum Γ(X, U) := hU.primeIdealOf
  have hf : Function.Injective f := hU.isoSpec.hom.injective
  have hz := finite_affine_zero_locus Γ(X, U) a ha
  have hnon : Set.Finite {x : U | ¬ IsUnit (X.presheaf.germ U x x.2 a)} := by
    apply Set.Finite.of_finite_image (f := f)
    · apply hz.subset
      rintro p ⟨x, hx, rfl⟩
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      by_contra hnot
      apply hx
      have hbasic : hU.fromSpec (f x) ∈ X.basicOpen a := by
        change f x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a
        rw [hU.fromSpec_preimage_basicOpen]
        exact hnot
      rw [hU.fromSpec_primeIdealOf x] at hbasic
      exact (Scheme.mem_basicOpen X a x.1 x.2).mp hbasic
    · intro x hx y hy hxy
      exact hf hxy
  apply (hnon.image (fun x : U ↦ (x : X))).subset
  rintro x ⟨hx, hord⟩
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  intro hunit
  exact hord (order_zero_of_unit_germ X U x hx a hunit)

theorem finite_codimension_one_set_closed
    (X : Scheme.{u}) [IsIntegral X] (hcurve : OneDimensionalCharts X)
    (S : Set X) (hS : S.Finite) (hcodim : ∀ x ∈ S, Order.coheight x = 1) : IsClosed S := by
  have heq : S = ⋃ x ∈ S, ({x} : Set X) := by ext x; simp
  rw [heq]
  exact hS.isClosed_biUnion (fun x hx ↦ isClosed_of_coheight_one X hcurve x (hcodim x hx))

/-- Every effective finite divisor is locally the order of an actual nonzero rational function. -/
theorem exists_local_divisor_equation
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X)
    (D : X →₀ ℤ) (hD : ∀ x, 0 ≤ D x)
    (hcodim : ∀ x, D x ≠ 0 → Order.coheight x = 1) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ r : X.functionField, r ≠ 0 ∧ ∀ y ∈ U, Scheme.ord r y = D y := by
  classical
  have hclosedD : IsClosed (D.support : Set X) :=
    finite_codimension_one_set_closed X hcurve _ D.support.finite_toSet
      (fun y hy ↦ hcodim y (Finsupp.mem_support_iff.mp hy))
  by_cases hxD : D x = 0
  · let W : X.Opens := ⟨(D.support : Set X)ᶜ, hclosedD.isOpen_compl⟩
    have hxW : x ∈ W := by simpa [W] using hxD
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
    refine ⟨U, hxU, hU, 1, one_ne_zero, ?_⟩
    intro y hy
    have hyD : D y = 0 := by simpa [W] using hUW hy
    rw [rational_order_one, hyD]
  · obtain ⟨W, hxW, a, ha, hordx⟩ := exists_regular_uniformizer X hN x (hcodim x hxD)
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    let b : Γ(X, V) := X.presheaf.map (homOfLE hVW).op a
    have hb : X.germToFunctionField V b = X.germToFunctionField W a :=
      germ_restrict X W V hVW a
    have hb0 : b ≠ 0 := by
      intro hb0
      have hh : X.germToFunctionField W a = 0 := by rw [← hb, hb0, map_zero]
      exact ha ((map_eq_zero_iff _ (X.germToFunctionField_injective W)).mp hh)
    let r : X.functionField := X.germToFunctionField V b
    have hr : r ≠ 0 := (map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb0
    have hrx : Scheme.ord r x = 1 := by simpa [r, hb] using hordx
    let Z : Set X := {y | y ∈ V ∧ Scheme.ord r y ≠ 0}
    have hZ : Z.Finite := finite_regular_order_support X hcurve V hV b hb0
    let S : Set X := ((D.support : Set X) ∪ Z) ∩ ({x} : Set X)ᶜ
    have hS : S.Finite := (D.support.finite_toSet.union hZ).inter_of_left _
    have hclosedS : IsClosed S := finite_codimension_one_set_closed X hcurve S hS (by
      intro y hy
      rcases hy.1 with hy | hy
      · exact hcodim y (Finsupp.mem_support_iff.mp hy)
      · by_contra hn
        exact hy.2 (Scheme.ord_eq_zero_of_coheight_neq_one hn r))
    let A : X.Opens := V ⊓ ⟨Sᶜ, hclosedS.isOpen_compl⟩
    have hxA : x ∈ A := ⟨hxV, by simp [S]⟩
    obtain ⟨U, hU, hxU, hUA⟩ := exists_isAffineOpen_mem_and_subset hxA
    refine ⟨U, hxU, hU, r ^ (D x).toNat, pow_ne_zero _ hr, ?_⟩
    intro y hy
    rw [ArithmeticThetaGeometry.function_order_pow X y r hr]
    by_cases hxy : y = x
    · subst y
      rw [hrx, mul_one, Int.toNat_of_nonneg (hD x)]
    · have hyA := hUA hy
      have hnot : y ∉ (D.support : Set X) ∪ Z := by
        intro hmem
        exact hyA.2 ⟨hmem, hxy⟩
      have hyD : D y = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hnot (Or.inl h))
      have hyord : Scheme.ord r y = 0 := by
        by_contra hn
        exact hnot (Or.inr ⟨hyA.1, hn⟩)
      rw [hyD, hyord, mul_zero]

/-- In the frame generated by the inverse equation, the canonical section has coefficient r. -/
theorem equationFrame_canonical_coefficient
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D : X →₀ ℤ) (hD : ∀ x, 0 ≤ D x)
    (U : X.Opens) [Nonempty U] (r : X.functionField)
    (hr : r ≠ 0) (hord : ∀ x ∈ U, Scheme.ord r x = D x) :
    sectionCoefficient X (divisorSheaf X hN D) U (equationFrame X hN D U r hr hord)
      (divisorCanonicalSection X hN D hD) = r := by
  let e := equationFrame X hN D U r hr hord
  let s := divisorCanonicalSection X hN D hD
  have he := (e.equiv U le_rfl).apply_symm_apply
    ((divisorSheaf X hN D).presheaf.map (homOfLE le_top).op s)
  have hratio := congrArg (fun t : boundedSections X hN D U ↦ t.val ⟨inferInstance⟩) he
  change sectionCoefficient X (divisorSheaf X hN D) U e s / r = 1 at hratio
  exact (div_eq_one_iff_eq hr).mp hratio

/-- Every effective finite codimension-one divisor on a normal integral locally
Noetherian curve is realized by the canonical section of its genuine line sheaf. -/
theorem effective_divisor_line_realization :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X],
    ArithmeticThetaCurveDegree.OneDimensionalCharts X →
    ArithmeticThetaNormalizedSections.NormalAffine X →
    ∀ D : X →₀ ℤ, (∀ x, 0 ≤ D x) →
      (∀ x, D x ≠ 0 → Order.coheight x = 1) →
    ∃ H : X.Modules, ArithmeticThetaNormalizedSections.IsLineBundle X H ∧
      ∃ (ι : Type u) (C : ArithmeticThetaLineRoot.NormalFrameCover X H ι)
        (s : H.presheaf.obj (Opposite.op ⊤)), s ≠ 0 ∧
          ArithmeticThetaSectionOrder.MatchesSectionOrder X H C s D := by
  intro X _ _ hcurve hN D hD hcodim
  classical
  choose U hxU hU r hr hord using
    exists_local_divisor_equation X hcurve hN D hD hcodim
  let H : X.Modules := divisorSheaf X hN D
  let e (x : X) : LocalFrame X H (U x) := equationFrame X hN D (U x) (r x) (hr x) (hord x)
  have hH : IsLineBundle X H := fun x ↦ ⟨U x, hxU x, ⟨localFrameIso X H (U x) (e x)⟩⟩
  let C : NormalFrameCover X H X :=
    { opens := U
      covers := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
      nonempty := fun x ↦ ⟨⟨x, hxU x⟩⟩
      affine := hU
      normal := fun x ↦ @hN (U x) (hU x) ⟨⟨x, hxU x⟩⟩
      frame := e }
  let s := divisorCanonicalSection X hN D hD
  refine ⟨H, hH, X, C, s, divisorCanonicalSection_ne_zero X hN D hD, ?_⟩
  intro i x hx
  letI : Nonempty (U i) := ⟨⟨i, hxU i⟩⟩
  change D x = Scheme.ord
    (sectionCoefficient X H (U i) (e i) s) x
  rw [equationFrame_canonical_coefficient X hN D hD (U i) (r i) (hr i) (hord i)]
  exact (hord i x hx).symm

end ArithmeticThetaGeometricPrerequisites

#print axioms ArithmeticThetaGeometricPrerequisites.effective_divisor_line_realization
