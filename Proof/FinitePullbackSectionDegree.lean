module

public import SectionDivisorComparison
public import PullbackLineFrames
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.RamificationInertia.Basic

import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaCurveDegree ArithmeticThetaSectionOrder ArithmeticThetaPullback

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ArithmeticThetaDegreeAssembly

/-- Naturality of the actual section pullback along restriction. -/
lemma pullbackGlobalSection_restrict
    {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (U : X.Opens)
    (s : Γ(H, ⊤)) :
    ((Scheme.Modules.pullback p).obj H).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op (pullbackGlobalSection p H s) =
      pullbackLocalSection p H U (H.presheaf.map (homOfLE le_top).op s) := by
  have h := (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H).mapPresheaf).naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  exact (ConcreteCategory.congr_hom h s).symm

/-- A compatible pullback frame carries the coordinate through the actual ring map. -/
lemma pullback_sectionCoordinate
    {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U))
    (he : FramePullbackCompatible p H U e eY) (s : Γ(H, ⊤)) :
    sectionCoordinate Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U) eY
      (pullbackGlobalSection p H s) = p.app U (sectionCoordinate X H U e s) := by
  apply (eY.equiv _ le_rfl).injective
  simp only [sectionCoordinate, LinearEquiv.apply_symm_apply]
  rw [pullbackGlobalSection_restrict]
  simpa only [LinearEquiv.apply_symm_apply] using (he U le_rfl ((e.equiv U le_rfl).symm
    (H.presheaf.map (homOfLE le_top).op s)))

/-- Dominant quasi-compact pullback is injective on sections of an actual line bundle. -/
theorem pullbackGlobalSection_injective
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsDominant p] [QuasiCompact p]
    (H : X.Modules) (hH : IsLineBundle X H) :
    Function.Injective (pullbackGlobalSection p H) := by
  letI : IsSchemeTheoreticallyDominant p := .of_isDominant p
  obtain ⟨U, hx, ⟨e⟩⟩ := hH (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  let eU := localFrameOfIso X H U e
  obtain ⟨eY, he⟩ := exists_pullbackFrame Y X p H U eU
  intro s t h
  apply sectionCoefficient_injective X H hH U eU
  apply congrArg (X.germToFunctionField U)
  apply p.app_injective U
  rw [← pullback_sectionCoordinate p H U eU eY he s,
    ← pullback_sectionCoordinate p H U eU eY he t, h]

/-- The nonvanishing conjunct required in the frozen pullback-degree theorem. -/
theorem pullbackGlobalSection_ne_zero
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsDominant p] [QuasiCompact p]
    (H : X.Modules) (hH : IsLineBundle X H) (s : Γ(H, ⊤)) (hs : s ≠ 0) :
    pullbackGlobalSection p H s ≠ 0 := by
  intro h
  apply hs
  apply pullbackGlobalSection_injective p H hH
  simpa only [pullbackGlobalSection, map_zero] using h

/-- Base scalars reach a pulled-back residue field through the actual residue map. -/
lemma baseToResidue_comp (k : Type u) [Field k] {Y X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (p : Y ⟶ X) (y : Y) :
    baseToResidue k (p ≫ f) y =
      (p.residueFieldMap y).hom.comp (baseToResidue k f (p y)) := by
  ext a
  exact (Scheme.Γevaluation_naturality_apply p y
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))).symm

/-- Residue-degree multiplication, with all scalar structures induced by the maps. -/
lemma placeDegree_comp (k : Type u) [Field k] {Y X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (p : Y ⟶ X) (y : Y) :
    placeDegree k (p ≫ f) y = placeDegree k f (p y) * p.residueDegree y := by
  letI : Algebra k (X.residueField (p y)) := (baseToResidue k f (p y)).toAlgebra
  letI : Algebra (X.residueField (p y)) (Y.residueField y) :=
    (p.residueFieldMap y).hom.toAlgebra
  letI : Algebra k (Y.residueField y) := (baseToResidue k (p ≫ f) y).toAlgebra
  letI : IsScalarTower k (X.residueField (p y)) (Y.residueField y) :=
    IsScalarTower.of_algebraMap_eq' (baseToResidue_comp k f p y)
  exact (Module.finrank_mul_finrank k (X.residueField (p y)) (Y.residueField y)).symm

/-- Order under a flat local algebra map is multiplied by the closed-fiber length. -/
lemma ring_ord_flat_local
    (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B] (a : A) :
    Ring.ord B (algebraMap A B a) = Ring.ord A a *
      Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  have h := IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {a})
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {a})).toLinearEquiv.length_eq] at h
  have hspan : Ideal.map (algebraMap A B) (Ideal.span {a}) =
      Ideal.span {algebraMap A B a} := by rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at h
  exact h

/-- Coordinates in arbitrary actual local frames differ by their transition unit. -/
lemma sectionCoefficient_transition_frames
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (U V : X.Opens) [Nonempty U] [Nonempty V] [Nonempty (U ⊓ V : X.Opens)]
    (e : LocalFrame X H U) (e' : LocalFrame X H V) (s : Γ(H, ⊤)) :
    sectionCoefficient X H U e s =
      X.germToFunctionField (U ⊓ V)
        (transitionUnit (e.equiv _ inf_le_left) (e'.equiv _ inf_le_right)) *
        sectionCoefficient X H V e' s := by
  have h : H.presheaf.map (homOfLE inf_le_left).op
      (e.equiv U le_rfl (sectionCoordinate X H U e s)) =
      H.presheaf.map (homOfLE inf_le_right).op
      (e'.equiv V le_rfl (sectionCoordinate X H V e' s)) := by
    simp only [sectionCoordinate, LinearEquiv.apply_symm_apply]
    simp only [← ConcreteCategory.comp_apply, ← H.presheaf.map_comp]
    rfl
  rw [e.naturality, e'.naturality,
    transition_apply (e.equiv _ inf_le_left) (e'.equiv _ inf_le_right)] at h
  have hc := congrArg (X.germToFunctionField (U ⊓ V))
    ((e.equiv _ inf_le_left).injective h)
  rw [map_mul, germ_restrict, germ_restrict] at hc
  exact hc

/-- Local section orders are invariant under any actual change of local frame. -/
lemma section_order_frame_invariant
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules)
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    (e : LocalFrame X H U) (e' : LocalFrame X H V) (s : Γ(H, ⊤))
    (x : X) (hU : x ∈ U) (hV : x ∈ V) :
    Scheme.ord (sectionCoefficient X H U e s) x =
      Scheme.ord (sectionCoefficient X H V e' s) x := by
  letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hU, hV⟩⟩
  rw [sectionCoefficient_transition_frames X H U V e e' s]
  let t := transitionUnit (e.equiv _ inf_le_left) (e'.equiv _ inf_le_right)
  by_cases hz : sectionCoefficient X H V e' s = 0
  · rw [hz, mul_zero]
  · rw [Scheme.ord_mul ((t.isUnit.map (X.germToFunctionField (U ⊓ V)).hom).ne_zero) hz,
      Scheme.ord_of_isUnit t.isUnit ⟨hU, hV⟩, zero_add]

/-- The closed-fiber length of the actual local homomorphism at a point. -/
def stalkFiberLength {Y X : Scheme.{u}} (p : Y ⟶ X) (y : Y) : ℕ :=
  (Module.length (Y.presheaf.stalk y)
    ((Y.presheaf.stalk y) ⧸
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (p y))).map (p.stalkMap y).hom)).toNat

/-- A nonzero section has a nonzero coordinate in every nonempty local frame. -/
lemma sectionCoordinate_ne_zero
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) : sectionCoordinate X H U e s ≠ 0 := by
  intro h
  apply hs
  apply sectionCoefficient_injective X H hH U e
  change X.germToFunctionField U (sectionCoordinate X H U e s) = _
  rw [h, map_zero]
  simp [sectionCoefficient, sectionCoordinate]

/-- A section's order at a codimension-one point is its actual coordinate quotient length. -/
lemma section_order_eq_stalk_length
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) (x : X) (hx : x ∈ U)
    (hco : Order.coheight x = 1) :
    Scheme.ord (sectionCoefficient X H U e s) x =
      ((Ring.ord (X.presheaf.stalk x)
        (X.presheaf.germ U x hx (sectionCoordinate X H U e s))).toNat : ℤ) := by
  have ha := sectionCoordinate_ne_zero X H hH U e s hs
  have hag : X.presheaf.germ U x hx (sectionCoordinate X H U e s) ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hx)).mpr ha
  simpa only [principalOrder, Scheme.algebraMap_germ_eq_germToFunctionField,
    sectionCoefficient, Ring.ord] using principalOrder_stalk_eq_length X x hco _ hag

/-- Flat pullback multiplies the actual local section order by closed-fiber length. -/
lemma pullback_section_order_eq
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [Flat p] [IsDominant p] [QuasiCompact p]
    (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U))
    (he : FramePullbackCompatible p H U e eY)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) (y : Y) (hy : p y ∈ U)
    (hxco : Order.coheight (p y) = 1) (hyco : Order.coheight y = 1) :
    letI : Nonempty (p ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
    Scheme.ord (sectionCoefficient Y ((Scheme.Modules.pullback p).obj H)
      (p ⁻¹ᵁ U) eY (pullbackGlobalSection p H s)) y =
      Scheme.ord (sectionCoefficient X H U e s) (p y) * (stalkFiberLength p y : ℤ) := by
  letI : Nonempty (p ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  letI : IsSchemeTheoreticallyDominant p := .of_isDominant p
  letI : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  letI : Module.Flat (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) := Flat.stalkMap p y
  letI : IsLocalHom (algebraMap (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)) :=
    (inferInstance : IsLocalHom (p.stalkMap y).hom)
  let a := sectionCoordinate X H U e s
  have ha : a ≠ 0 := sectionCoordinate_ne_zero X H hH U e s hs
  have hag : X.presheaf.germ U (p y) hy a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X (p y) hy)).mpr ha
  have hay : Y.presheaf.germ (p ⁻¹ᵁ U) y hy (p.app U a) ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral Y y hy)).mpr
      ((map_ne_zero_iff _ (p.app_injective U)).mpr ha)
  have hxord := principalOrder_stalk_eq_length X (p y) hxco _ hag
  have hyord := principalOrder_stalk_eq_length Y y hyco _ hay
  simp only [principalOrder, Scheme.algebraMap_germ_eq_germToFunctionField] at hxord hyord
  simp only [sectionCoefficient, pullback_sectionCoordinate p H U e eY he]
  rw [hyord, hxord]
  have hflat := ring_ord_flat_local (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)
    (X.presheaf.germ U (p y) hy a)
  change Ring.ord (Y.presheaf.stalk y)
      (p.stalkMap y (X.presheaf.germ U (p y) hy a)) = _ at hflat
  rw [Scheme.Hom.germ_stalkMap_apply] at hflat
  have ht := congrArg ENat.toNat hflat
  simp only [ENat.toNat_mul, Ring.ord, RingHom.algebraMap_toAlgebra] at ht
  exact_mod_cast ht

/-- The stalk-length formula also holds at the generic point and in dimension zero. -/
lemma section_order_eq_stalk_length_all
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hX : OneDimensionalCharts X) (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) (x : X) (hx : x ∈ U) :
    Scheme.ord (sectionCoefficient X H U e s) x =
      ((Ring.ord (X.presheaf.stalk x)
        (X.presheaf.germ U x hx (sectionCoordinate X H U e s))).toNat : ℤ) := by
  by_cases hco : Order.coheight x = 1
  · exact section_order_eq_stalk_length X H hH U e s hs x hx hco
  · have hz : Order.coheight x = 0 :=
      (Order.le_one_iff.mp (DegreeCohomology.coheight_le_one X hX x)).resolve_right hco
    haveI : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hz.le
    letI : Field (X.presheaf.stalk x) := Ring.KrullDimLE.isField_of_isDomain.toField
    have ha := sectionCoordinate_ne_zero X H hH U e s hs
    have hag : X.presheaf.germ U x hx (sectionCoordinate X H U e s) ≠ 0 :=
      (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hx)).mpr ha
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hco, Ring.ord_of_isUnit (isUnit_iff_ne_zero.mpr hag)]
    rfl

/-- The actual pullback divisor has the flat local multiplicity at every point. -/
theorem pullback_divisor_local_multiplicity
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [Flat p] [IsDominant p] [QuasiCompact p]
    (hX : OneDimensionalCharts X) (hY : OneDimensionalCharts Y)
    (H : X.Modules) (hH : IsLineBundle X H)
    {ι : Type v} {κ : Type w}
    (C : NormalFrameCover X H ι)
    (E : NormalFrameCover Y ((Scheme.Modules.pullback p).obj H) κ)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) (D : X →₀ ℤ) (DY : Y →₀ ℤ)
    (hD : MatchesSectionOrder X H C s D)
    (hDY : MatchesSectionOrder Y ((Scheme.Modules.pullback p).obj H) E
      (pullbackGlobalSection p H s) DY) (y : Y) :
    DY y = D (p y) * (stalkFiberLength p y : ℤ) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (C.covers (show p y ∈ (⊤ : X.Opens) by trivial))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp
    (E.covers (show y ∈ (⊤ : Y.Opens) by trivial))
  letI : Nonempty (p ⁻¹ᵁ C.opens i) := ⟨⟨y, hi⟩⟩
  obtain ⟨eY, he⟩ := exists_pullbackFrame Y X p H (C.opens i) (C.frame i)
  rw [hDY j y hj, hD i (p y) hi]
  unfold localOrder
  rw [section_order_frame_invariant Y _ (E.opens j) (p ⁻¹ᵁ C.opens i)
    (E.frame j) eY _ y hj hi]
  rw [section_order_eq_stalk_length_all X hX H hH _ _ s hs _ hi,
    section_order_eq_stalk_length_all Y hY _ (pullback_isLineBundle Y X p H hH)
      _ eY _ (pullbackGlobalSection_ne_zero p H hH s hs) y hi,
    pullback_sectionCoordinate p H _ _ eY he]
  letI : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  letI : Module.Flat (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) := Flat.stalkMap p y
  letI : IsLocalHom (algebraMap (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)) :=
    (inferInstance : IsLocalHom (p.stalkMap y).hom)
  have hflat := ring_ord_flat_local (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)
    (X.presheaf.germ (C.opens i) (p y) hi (sectionCoordinate X H _ (C.frame i) s))
  change Ring.ord _ (p.stalkMap y _) = _ at hflat
  rw [Scheme.Hom.germ_stalkMap_apply] at hflat
  have ht := congrArg ENat.toNat hflat
  simp only [ENat.toNat_mul, RingHom.algebraMap_toAlgebra] at ht
  exact_mod_cast ht

/-- Ramification length is independent of the chosen realization of a localization. -/
lemma ramificationIdx_eq_local_length
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime T q] :
    q.ramificationIdx R =
      (Module.length T (T ⧸ (q.under R).map (algebraMap R T))).toNat := by
  rw [Ideal.ramificationIdx_def]
  let e := Localization.algEquiv q.primeCompl T
  have hmap : ((q.under R).map (algebraMap R T)).comap e.toRingHom =
      (q.under R).map (algebraMap R (Localization.AtPrime q)) := by
    have he : (algebraMap R T) =
        e.toRingHom.comp (algebraMap R (Localization.AtPrime q)) := by
      ext a
      change algebraMap R T a = e (algebraMap R (Localization.AtPrime q) a)
      rw [IsScalarTower.algebraMap_apply R S T,
        IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
      exact (e.commutes _).symm
    rw [he, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  rw [Module.length_quotient, Module.length_quotient, ← hmap]
  exact congrArg ENat.toNat (Ideal.coheight_comap_of_surjective
    e.toRingHom e.surjective _)

/-- On affine charts the actual stalk fiber length is the algebraic ramification index. -/
lemma stalkFiberLength_eq_affine_ramification
    {Y X : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) (y : Y) (hy : p y ∈ U) :
    letI := (p.app U).hom.toAlgebra
    stalkFiberLength p y =
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.ramificationIdx Γ(X, U) := by
  letI := (p.app U).hom.toAlgebra
  letI := X.presheaf.algebra_section_stalk ⟨p y, hy⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : p ⁻¹ᵁ U)
  haveI := hU.isLocalization_stalk ⟨p y, hy⟩
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  letI : Algebra Γ(X, U) (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ (p ⁻¹ᵁ U) y hy).hom.comp (p.app U).hom).toAlgebra
  letI : IsScalarTower Γ(X,U) Γ(Y,p ⁻¹ᵁ U) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hq : (hV.primeIdealOf ⟨y,hy⟩).asIdeal.under Γ(X,U) =
      (hU.primeIdealOf ⟨p y,hy⟩).asIdeal := by
    simpa only [Ideal.under, RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app,
      PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU (p ⁻¹ᵁ U) hV le_rfl hy)
  rw [ramificationIdx_eq_local_length Γ(X,U) Γ(Y,p ⁻¹ᵁ U) (Y.presheaf.stalk y), hq]
  unfold stalkFiberLength
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (hU.primeIdealOf ⟨p y,hy⟩).asIdeal (X.presheaf.stalk (p y)), Ideal.map_map]
  have he : (p.stalkMap y).hom.comp (algebraMap Γ(X,U) (X.presheaf.stalk (p y))) =
      algebraMap Γ(X,U) (Y.presheaf.stalk y) := by
    ext a
    exact Scheme.Hom.germ_stalkMap_apply p U y hy a
  rw [he]

/-- Affine inertia degrees use exactly the residue-field homomorphism of the scheme map. -/
lemma residueDegree_eq_affine_inertia
    {Y X : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) (y : Y) (hy : p y ∈ U)
    [(hU.primeIdealOf ⟨p y,hy⟩).asIdeal.IsMaximal]
    [(hV.primeIdealOf ⟨y,hy⟩).asIdeal.IsMaximal] :
    letI := (p.app U).hom.toAlgebra
    p.residueDegree y = (hV.primeIdealOf ⟨y,hy⟩).asIdeal.inertiaDeg Γ(X,U) := by
  letI := (p.app U).hom.toAlgebra
  let P := (hU.primeIdealOf ⟨p y,hy⟩).asIdeal
  let Q := (hV.primeIdealOf ⟨y,hy⟩).asIdeal
  have hq : Q.under Γ(X,U) = P := by
    simpa only [Ideal.under, RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app,
      PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU (p ⁻¹ᵁ U) hV le_rfl hy)
  letI : Q.LiesOver P := ⟨hq.symm⟩
  letI := X.presheaf.algebra_section_stalk ⟨p y,hy⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y,hy⟩ : p ⁻¹ᵁ U)
  haveI := hU.isLocalization_stalk ⟨p y,hy⟩
  haveI := hV.isLocalization_stalk ⟨y,hy⟩
  letI := (p.residueFieldMap y).hom.toAlgebra
  letI : Field (Γ(X,U) ⧸ P) := Ideal.Quotient.field P
  letI : Field (Γ(Y,p ⁻¹ᵁ U) ⧸ Q) := Ideal.Quotient.field Q
  rw [Ideal.inertiaDeg_eq_of_isMaximal P]
  symm
  let eX : (Γ(X,U) ⧸ P) ≃+* X.residueField (p y) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (X.presheaf.stalk (p y))).toRingEquiv
  let eY : (Γ(Y,p ⁻¹ᵁ U) ⧸ Q) ≃+* Y.residueField y :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Y.presheaf.stalk y)).toRingEquiv
  apply Algebra.finrank_eq_of_equiv_equiv eX eY
  ext a
  exact Scheme.evaluation_naturality_apply p y hy a

/-- A geometric fiber point determines its actual affine prime above the base point. -/
def affineFiberPrime {Y X : Scheme.{u}} (p : Y ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U))
    (x : X) (hx : x ∈ U) :
    letI := (p.app U).hom.toAlgebra
    {y : Y // p y = x} → (hU.primeIdealOf ⟨x,hx⟩).asIdeal.primesOver Γ(Y,p ⁻¹ᵁ U) := by
  letI := (p.app U).hom.toAlgebra
  intro y
  have hy : p y.1 ∈ U := by rw [y.2]; exact hx
  refine ⟨(hV.primeIdealOf ⟨y.1,hy⟩).asIdeal, inferInstance, ⟨?_⟩⟩
  have h := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U hU (p ⁻¹ᵁ U) hV le_rfl hy)
  simpa only [Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal, Ideal.under,
    RingHom.algebraMap_toAlgebra, y.2] using h.symm

/-- The affine description includes every geometric point in the finite fiber, exactly once. -/
lemma affineFiberPrime_bijective {Y X : Scheme.{u}} (p : Y ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U))
    (x : X) (hx : x ∈ U) : Function.Bijective (affineFiberPrime p U hU hV x hx) := by
  letI := (p.app U).hom.toAlgebra
  constructor
  · intro y z h
    apply Subtype.ext
    have hp := congrArg Subtype.val h
    have hs := hV.isoSpec.hom.injective (PrimeSpectrum.ext hp)
    exact congrArg (fun t : p ⁻¹ᵁ U => (t : Y)) hs
  · intro q
    let z : p ⁻¹ᵁ U := hV.isoSpec.inv (⟨q.1,q.2.1⟩ : PrimeSpectrum Γ(Y,p ⁻¹ᵁ U))
    have hz : hV.primeIdealOf z = (⟨q.1,q.2.1⟩ : PrimeSpectrum Γ(Y,p ⁻¹ᵁ U)) := by
      change hV.isoSpec.hom (hV.isoSpec.inv _) = _
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hpz : p z.1 = x := by
      suffices hh : (⟨p z.1,z.2⟩ : U) = ⟨x,hx⟩ from congrArg Subtype.val hh
      apply hU.isoSpec.hom.injective
      change hU.primeIdealOf ⟨p z.1,z.2⟩ = hU.primeIdealOf ⟨x,hx⟩
      rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU (p ⁻¹ᵁ U) hV le_rfl z.2,
        Scheme.Hom.appLE_eq_app]
      change PrimeSpectrum.comap (p.app U).hom (hV.primeIdealOf z) = _
      rw [hz]
      apply PrimeSpectrum.ext
      exact (Ideal.over_def q.1 (hU.primeIdealOf ⟨x,hx⟩).asIdeal).symm
    refine ⟨⟨z.1,hpz⟩, ?_⟩
    apply Subtype.ext
    exact congrArg PrimeSpectrum.asIdeal hz

private lemma affine_finrank_eq_module {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [Flat f] [IsFinite f]
    [IsDomain Γ(S, ⊤)] (s : S) [IsAffine X] :
    letI := f.appTop.hom.toAlgebra
    f.finrank s = Module.finrank Γ(S, ⊤) Γ(X, ⊤) := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := f.flat_appTop
  letI : Module.Finite Γ(S, ⊤) Γ(X, ⊤) := f.finite_appTop
  have h0 : f.finrank s = f.appTop.hom.finrank (S.isoSpec.hom s) := by
    unfold Scheme.Hom.finrank
    change (Limits.pullback.snd f (S.affineOpenCover.f (S.affineOpenCover.idx s))).appTop.hom.finrank _ = _
    have hpb : IsPullback (Limits.pullback.fst f (S.affineOpenCover.f (S.affineOpenCover.idx s)))
        (Limits.pullback.snd f (S.affineOpenCover.f (S.affineOpenCover.idx s))) f
        (S.affineOpenCover.f (S.affineOpenCover.idx s)) :=
      IsPullback.of_hasPullback _ _
    have hp : IsPushout f.appTop (S.affineOpenCover.f (S.affineOpenCover.idx s)).appTop
        (Limits.pullback.fst f (S.affineOpenCover.f (S.affineOpenCover.idx s))).appTop
        (Limits.pullback.snd f (S.affineOpenCover.f (S.affineOpenCover.idx s))).appTop :=
      isPushout_appTop_of_isPullback hpb
    have hrw := CommRingCat.finrank_eq_of_isPushout hp f.flat_appTop f.finite_appTop
      ((Spec (S.affineOpenCover.X (S.affineOpenCover.idx s))).isoSpec.hom
        (S.affineOpenCover.covers s).choose)
    have heq : PrimeSpectrum.comap (CommRingCat.Hom.hom
        (Scheme.Hom.appTop (S.affineOpenCover.f (S.affineOpenCover.idx s))))
        ((Spec (S.affineOpenCover.X (S.affineOpenCover.idx s))).isoSpec.hom
          (S.affineOpenCover.covers s).choose) = S.isoSpec.hom s := by
      rw [← AlgebraicGeometry.Spec.map_apply]
      have hn := congrArg (fun q => q (S.affineOpenCover.covers s).choose)
        (Scheme.isoSpec_hom_naturality (S.affineOpenCover.f
          (S.affineOpenCover.idx s)))
      simp only [Scheme.Hom.comp_apply] at hn
      rw [(S.affineOpenCover.covers s).choose_spec] at hn
      exact hn
    rw [heq] at hrw
    exact hrw
  rw [h0]
  change Module.rankAtStalk Γ(X, ⊤) (S.isoSpec.hom s : PrimeSpectrum Γ(S, ⊤)) = _
  have hrank := Module.rankAtStalk_eq (M := Γ(X, ⊤))
    (S.isoSpec.hom s : PrimeSpectrum Γ(S, ⊤))
  rw [hrank]
  let p : PrimeSpectrum Γ(S, ⊤) := (S.isoSpec.hom s : PrimeSpectrum Γ(S, ⊤))
  letI : p.asIdeal.IsPrime := p.isPrime
  exact Ideal.finrank_fiber_eq_finrank p.asIdeal

/-- The rank of the actual finite flat map is computed by its affine section algebra. -/
lemma finrank_eq_affine_module
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsFinite p] [Flat p]
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    letI := (p.app U).hom.toAlgebra
    p.finrank x.1 = Module.finrank Γ(X,U) Γ(Y,p ⁻¹ᵁ U) := by
  letI : Nonempty U := ⟨x⟩
  letI : IsAffine U := hU
  letI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  let V := p ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage p
  letI : IsAffine V := hV
  let g := p ∣_ U
  letI := (p.app U).hom.toAlgebra
  have hg : g.finrank x = Module.finrank Γ(X,U) Γ(Y,V) := by
    letI := g.appTop.hom.toAlgebra
    have hga := affine_finrank_eq_module g x
    have hc := (arrowResLEAppIso p U V le_rfl).inv.w
    simp only [arrowResLEAppIso, Arrow.isoMk_inv_left, Arrow.isoMk_inv_right, Arrow.mk_hom] at hc
    have hfin : Module.finrank Γ(X,U) Γ(Y,V) = Module.finrank Γ(U,⊤) Γ(V,⊤) := by
      apply Algebra.finrank_eq_of_equiv_equiv
        U.topIso.symm.commRingCatIsoToRingEquiv V.topIso.symm.commRingCatIsoToRingEquiv
      ext z
      have hz := congr($(hc) z)
      dsimp only [Arrow.mk] at hz
      change g.appTop (U.topIso.inv z) = V.topIso.inv (p.app U z)
      simpa only [V,g,Scheme.Hom.resLE,Scheme.homOfLE_rfl,Category.id_comp,
        Scheme.Hom.appLE_eq_app,ConcreteCategory.comp_apply] using hz
    exact hga.trans hfin.symm
  have hpull := Scheme.Hom.finrank_pullback_snd p U.ι x
  have hrestrict := Scheme.Hom.finrank_comp_left_of_isIso
    (pullbackRestrictIsoRestrict p U).inv (Limits.pullback.snd p U.ι)
  calc
    _ = Scheme.Hom.finrank (Limits.pullback.snd p U.ι) x := hpull.symm
    _ = g.finrank x := by simpa [g,morphismRestrict] using (hrestrict x).symm
    _ = _ := hg

/-- Every nonempty affine chart computes the generic geometric degree. -/
lemma affine_module_rank_eq_generic
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsFinite p] [Flat p]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (p.app U).hom.toAlgebra
    Module.finrank Γ(X,U) Γ(Y,p ⁻¹ᵁ U) = p.finrank (genericPoint X) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  exact (finrank_eq_affine_module p U hU ⟨genericPoint X,hx⟩).symm

/-- The geometric ramification--residue sum equals the actual generic map rank. -/
theorem fiber_length_residue_sum
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsFinite p] [Flat p]
    (hX : OneDimensionalCharts X) (x : X) (hco : Order.coheight x = 1) :
    ∑ᶠ y : {y : Y // p y = x}, stalkFiberLength p y.1 * p.residueDegree y.1 =
      p.finrank (genericPoint X) := by
  classical
  obtain ⟨U,hU,hx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  obtain ⟨U,hU,rfl⟩ := hU
  letI : Nonempty U := ⟨⟨x,hx.1⟩⟩
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  letI := (p.app U).hom.toAlgebra
  letI : Module.Finite Γ(X,U) Γ(Y,p ⁻¹ᵁ U) := p.finite_app U hU
  letI : Module.Flat Γ(X,U) Γ(Y,p ⁻¹ᵁ U) := by
    have hp : (p.app U).hom.Flat := by
      simpa only [Scheme.Hom.appLE_eq_app] using p.flat_appLE hU hV le_rfl
    exact hp
  let P := (hU.primeIdealOf ⟨x,hx.1⟩).asIdeal
  letI : P.IsPrime := inferInstance
  letI : Ring.DimensionLEOne Γ(X,U) := hX U hU
  have hP1 : P.height = 1 := (DegreeCohomology.coheight_eq_affine_height X U hU ⟨x,hx.1⟩).symm.trans hco
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (Ideal.ne_bot_of_height_eq_one hP1) inferInstance
  let e := Equiv.ofBijective (affineFiberPrime p U hU hV x hx.1)
    (affineFiberPrime_bijective p U hU hV x hx.1)
  letI : Finite {y : Y // p y = x} := (p.finite_preimage_singleton x).to_subtype
  letI : Finite (P.primesOver Γ(Y,p ⁻¹ᵁ U)) := Finite.of_surjective e e.surjective
  letI : Fintype (P.primesOver Γ(Y,p ⁻¹ᵁ U)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P Γ(Y,p ⁻¹ᵁ U)
  rw [← affine_module_rank_eq_generic p U hU, ← hsum]
  rw [← finsum_eq_sum_of_fintype, ← finsum_comp_equiv e]
  apply finsum_congr
  intro y
  have hy : p y.1 ∈ U := by rw [y.2]; exact hx.1
  have hmax : (hU.primeIdealOf ⟨p y.1,hy⟩).asIdeal.IsMaximal := by
    simpa only [y.2] using (inferInstance : P.IsMaximal)
  letI := hmax
  have heq : (e y).1 = (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal := rfl
  have hqmax : (e y).1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (e y).1 P
  letI : (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal.IsMaximal := heq ▸ hqmax
  rw [stalkFiberLength_eq_affine_ramification p U hU hV y.1 hy,
    residueDegree_eq_affine_inertia p U hU hV y.1 hy]
  rfl

/-- Degree of the divisor of the actual pulled-back nonzero section. -/
theorem finite_pullback_section_degree
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (p : Y ⟶ X) [IsFinite p] [Flat p] [IsDominant p]
    (hX : OneDimensionalCharts X) (hY : OneDimensionalCharts Y)
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v) (κ : Type w)
    (C : NormalFrameCover X H ι)
    (E : NormalFrameCover Y ((Scheme.Modules.pullback p).obj H) κ)
    (s : Γ(H,⊤)) (D : X →₀ ℤ) (DY : Y →₀ ℤ) :
    s ≠ 0 → MatchesSectionOrder X H C s D →
    MatchesSectionOrder Y ((Scheme.Modules.pullback p).obj H) E
      (pullbackGlobalSection p H s) DY →
    pullbackGlobalSection p H s ≠ 0 ∧
      weightedDegree k (p ≫ f) DY = (p.finrank (genericPoint X) : ℤ) * weightedDegree k f D := by
  classical
  intro hs hD hDY
  refine ⟨pullbackGlobalSection_ne_zero p H hH s hs, ?_⟩
  have hlocal := pullback_divisor_local_multiplicity p hX hY H hH C E s hs D DY hD hDY
  let t := (p.finite_preimage D.support.finite_toSet).toFinset
  have ht (y : Y) : y ∈ t ↔ p y ∈ D.support := by simp [t]
  have hsupp : DY.support ⊆ t := by
    intro y hy
    apply (ht y).mpr
    rw [Finsupp.mem_support_iff]
    intro hz
    exact (Finsupp.mem_support_iff.mp hy) (by rw [hlocal y,hz,zero_mul])
  have hsumY : weightedDegree k (p ≫ f) DY =
      ∑ y ∈ t, (placeDegree k (p ≫ f) y : ℤ) * DY y := by
    unfold weightedDegree Finsupp.sum
    apply Finset.sum_subset hsupp
    intro y _ hy
    simp only [Finsupp.notMem_support_iff.mp hy, mul_zero]
  rw [hsumY, ← Finset.sum_fiberwise_of_maps_to
    (g := fun y : Y => p y) (t := D.support) (fun y hy => (ht y).mp hy)]
  unfold weightedDegree Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hco := section_divisor_support_coheight_one X H ι C s D hD x hx
  letI : Finite {y : Y // p y = x} := (p.finite_preimage_singleton x).to_subtype
  letI : Fintype {y : Y // p y = x} := Fintype.ofFinite _
  have hfiber : ∑ y : {y : Y // p y = x}, stalkFiberLength p y.1 * p.residueDegree y.1 =
      p.finrank (genericPoint X) := by
    simpa only [finsum_eq_sum_of_fintype] using fiber_length_residue_sum p hX x hco
  have hfilter : ∑ y ∈ t with p y = x, (placeDegree k (p ≫ f) y : ℤ) * DY y =
      ∑ y : {y : Y // p y = x}, (placeDegree k (p ≫ f) y.1 : ℤ) * DY y.1 := by
    apply Finset.sum_subtype
    intro y
    simp only [Finset.mem_filter, ht]
    exact ⟨And.right, fun hy => ⟨hy ▸ hx,hy⟩⟩
  rw [hfilter]
  calc
    _ = ((placeDegree k f x : ℤ) * D x) *
        ∑ y : {y : Y // p y = x}, ((stalkFiberLength p y.1 * p.residueDegree y.1 : ℕ) : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [hlocal y.1, placeDegree_comp k f p y.1, y.2]
      push_cast
      ring
    _ = _ := by
      rw [← Nat.cast_sum, hfiber]
      ring

end ArithmeticThetaDegreeAssembly

#print axioms ArithmeticThetaDegreeAssembly.pullbackGlobalSection_ne_zero
#print axioms ArithmeticThetaDegreeAssembly.placeDegree_comp
#print axioms ArithmeticThetaDegreeAssembly.ring_ord_flat_local
#print axioms ArithmeticThetaDegreeAssembly.pullback_divisor_local_multiplicity
#print axioms ArithmeticThetaDegreeAssembly.fiber_length_residue_sum
#print axioms ArithmeticThetaDegreeAssembly.finite_pullback_section_degree
