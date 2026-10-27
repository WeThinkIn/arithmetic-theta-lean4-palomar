import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import SharpCoverRatiosDefinitionsR0194
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2

/-! Arithmetic projective unary ratios on the original full 2m-level component.
The actual theta line, symmetric lifts, finite signs, equivariant arithmetic
basis and identity-fiber evaluation prove the exact punctured-disk expansions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184

section FieldExpansion
variable (k : Type) [Field k] (Z : Scheme) [IsIntegral Z]
    (f : Puncture k ⟶ Z) (θ : Z.functionField →+* LaurentSeries k)
    (hf : Spec.map (CommRingCat.ofHom θ) ≫ Z.fromSpecStalk (genericPoint Z) = f)

include hf

/-- The image of the puncture is the generic point for the specified geometric
factorization, so every nonempty open has the whole puncture as preimage. -/
lemma preimage_nonempty_open (U : Z.Opens) [Nonempty U] : f ⁻¹ᵁ U = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  rw [← hf, Scheme.Hom.comp_apply, Spec_closedPoint]
  erw [Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- Actual pullback on an open is identified with the puncture's scalar field. -/
def punctureSectionsIso (U : Z.Opens) [Nonempty U] :
    (Puncture k).presheaf.obj (Opposite.op (f ⁻¹ᵁ U)) ≅
      CommRingCat.of (LaurentSeries k) :=
  (Puncture k).presheaf.mapIso
    (eqToIso (preimage_nonempty_open k Z f θ hf U).symm).op ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))

lemma pullback_germ (U : Z.Opens) [Nonempty U] :
    f.app U ≫ (punctureSectionsIso k Z f θ hf U).hom =
      Z.germToFunctionField U ≫ CommRingCat.ofHom θ := by
  subst f
  have hU : (Spec.map (CommRingCat.ofHom θ) ≫ Z.fromSpecStalk (genericPoint Z))
      (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint]
    erw [Scheme.fromSpecStalk_closedPoint]
    exact ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  exact (Scheme.germ_stalkClosedPointTo _ U hU).symm.trans
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU)

lemma punctureSectionsIso_scalar (U : Z.Opens) [Nonempty U] (a : LaurentSeries k) :
    (punctureSectionsIso k Z f θ hf U).hom
      ((Puncture k).presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (scalar (LaurentSeries k) a)) = a := by
  change (punctureSectionsIso k Z f θ hf U).hom
    ((punctureSectionsIso k Z f θ hf U).inv a) = a
  exact (punctureSectionsIso k Z f θ hf U).commRingCatIsoToRingEquiv.apply_symm_apply a

/-- The genuine-open predicate is exactly evaluation under the field map
induced by the punctured disk. This is an equivalence, not an algebraicity claim. -/
theorem rationalExpansion_iff (r : Z.functionField) (a : LaurentSeries k) :
    RationalExpansion k Z f r a ↔ θ r = a := by
  constructor
  · rintro ⟨U, hU, v, hv, _, he⟩
    letI := hU
    have hg := ConcreteCategory.congr_hom (pullback_germ k Z f θ hf U) v
    change (punctureSectionsIso k Z f θ hf U).hom (f.app U v) =
      θ (Z.germToFunctionField U v) at hg
    rw [he, punctureSectionsIso_scalar, hv] at hg
    exact hg.symm
  · intro hr
    obtain ⟨U, hxU, v, hv⟩ := Z.presheaf.exists_germ_eq r
    letI : Nonempty U := ⟨⟨genericPoint Z, hxU⟩⟩
    refine ⟨U, inferInstance, v, hv, preimage_nonempty_open k Z f θ hf U, ?_⟩
    apply (punctureSectionsIso k Z f θ hf U).commRingCatIsoToRingEquiv.injective
    change (punctureSectionsIso k Z f θ hf U).hom (f.app U v) =
      (punctureSectionsIso k Z f θ hf U).hom _
    rw [punctureSectionsIso_scalar]
    have hg := ConcreteCategory.congr_hom (pullback_germ k Z f θ hf U) v
    change (punctureSectionsIso k Z f θ hf U).hom (f.app U v) =
      θ (Z.germToFunctionField U v) at hg
    exact hg.trans ((congrArg θ hv).trans hr)

/-- Uniqueness is geometric: the actual field map is injective. -/
theorem rationalExpansion_unique (r s : Z.functionField) (a : LaurentSeries k)
    (hr : RationalExpansion k Z f r a) (hs : RationalExpansion k Z f s a) : r = s := by
  apply θ.injective
  exact ((rationalExpansion_iff k Z f θ hf r a).mp hr).trans
    ((rationalExpansion_iff k Z f θ hf s a).mp hs).symm

#print axioms rationalExpansion_iff
#print axioms rationalExpansion_unique

end FieldExpansion

section ArithmeticComponent

variable (k : Type) [Field k] [CharZero k]

/-- No parameter extension is involved in selecting the actual component and
the embedding of its function field determined by the original Tate disk. -/
theorem component_field_factor (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (V : DiskTest k L D X) :
    ∃ (f : Disk k ⟶ Component k L D X (V.disk (closedPoint k)))
      (θ : (Component k L D X (V.disk (closedPoint k))).functionField →+* LaurentSeries k),
      f ≫ inclusion k L D X (V.disk (closedPoint k)) = V.disk ∧
      IsDominant (genericInclusion k ≫ f) ∧
      Spec.map (CommRingCat.ofHom θ) ≫
        (Component k L D X (V.disk (closedPoint k))).fromSpecStalk
          (genericPoint (Component k L D X (V.disk (closedPoint k)))) =
        genericInclusion k ≫ f := by
  let x := V.disk (closedPoint k)
  have hx : V.disk (closedPoint k) ∈ componentOpen k L D X x :=
    mem_irreducibleComponent
  let f := GeometricComponentCuspBoundR0184.componentDisk k L D X x V.disk hx
  have hfac : f ≫ inclusion k L D X x = V.disk :=
    GeometricComponentCuspBoundR0184.componentDisk_inclusion k L D X x V.disk hx
  obtain ⟨θ, hθ⟩ := GeometricComponentCuspBoundR0184.generic_field_factor
    (genericInclusion k ≫ f)
    (GeometricComponentCuspBoundR0184.componentDisk_generic k L D X x V.base V.disk
      V.extends_eq hx)
  letI := X.smooth
  letI : SmoothOfRelativeDimension 1 (projection k L D X x) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  exact ⟨f, θ, hfac,
    ArithmeticThetaSimultaneousUnaryR0187.SimultaneousUnaryCommonCoverR0187.disk_dominant
      k L D X V (projection k L D X x) (inclusion k L D X x) f hfac, hθ⟩

omit [CharZero k] in
lemma levelUnary_minimal (m : ℕ) (hm : 0 < m) (ν : Fin m) :
    levelUnary k (2*m) m ν = ArithmeticThetaSchrodingerR0119.unary k m ν := by
  have hpos : 0 < 2*m := Nat.mul_pos (by decide) hm
  rw [levelUnary, Nat.div_self hpos, pow_one, PowerSeries.X_subst]

lemma minimal_denominator_ne_zero (m : ℕ) (hm : 0 < m) :
    algebraMap (PowerSeries k) (LaurentSeries k)
      (levelUnary k (2*m) m ⟨0, hm⟩) ≠ 0 := by
  rw [levelUnary_minimal k m hm]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))).mpr
    (ArithmeticThetaGenericEvaluationR0140.GenericProjectiveEvaluationR0140.unary_zero_nonzero
      k m hm)

/-- The remaining arithmetic claim is membership in the image of the actual
component function field. This equivalence preserves all coefficients, the
original disk, and the normalization at residue zero. It does not assert that
the image membership holds. -/
theorem projectiveRatios_iff_field_range (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
    (V : DiskTest k (2*m) D X)
    (f : Disk k ⟶ Component k (2*m) D X (V.disk (closedPoint k)))
    (hfac : f ≫ inclusion k (2*m) D X (V.disk (closedPoint k)) = V.disk)
    (hdom : IsDominant (genericInclusion k ≫ f))
    (θ : (Component k (2*m) D X (V.disk (closedPoint k))).functionField →+* LaurentSeries k)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫
      (Component k (2*m) D X (V.disk (closedPoint k))).fromSpecStalk
        (genericPoint (Component k (2*m) D X (V.disk (closedPoint k)))) =
      genericInclusion k ≫ f) :
    ProjectiveRatios k (2*m) m hm D X V ↔
      ∀ ν : Fin m, ∃ r : (Component k (2*m) D X (V.disk (closedPoint k))).functionField,
        θ r = algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m ν) /
          algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m ⟨0, hm⟩) := by
  constructor
  · rintro ⟨g, hg, _, r, _, hr⟩
    have hgf : g = f := (cancel_mono (inclusion k (2*m) D X
      (V.disk (closedPoint k)))).mp (hg.trans hfac.symm)
    subst g
    intro ν
    exact ⟨r ν, (rationalExpansion_iff k _ (genericInclusion k ≫ f) θ hθ _ _).mp (hr ν)⟩
  · intro h
    choose r hr using h
    refine ⟨f, hfac, hdom, r, ?_, ?_⟩
    · apply θ.injective
      rw [hr, map_one, div_self (minimal_denominator_ne_zero k m hm)]
    · intro ν
      exact (rationalExpansion_iff k _ (genericInclusion k ≫ f) θ hθ _ _).mpr (hr ν)

#print axioms component_field_factor
#print axioms minimal_denominator_ne_zero
#print axioms projectiveRatios_iff_field_range

/-- The function-field embedding uses the given structural map and the actual
classifying map of the family; it is not an arbitrary Laurent-series map. -/
theorem component_field_map_over (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X (V.disk (closedPoint k)))
    (hfac : f ≫ inclusion k L D X (V.disk (closedPoint k)) = V.disk)
    (θ : (Component k L D X (V.disk (closedPoint k))).functionField →+* LaurentSeries k)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫
      (Component k L D X (V.disk (closedPoint k))).fromSpecStalk
        (genericPoint (Component k L D X (V.disk (closedPoint k)))) =
      genericInclusion k ≫ f) :
    θ.comp (AlgebraicCurve.baseToFunctionField
      (projection k L D X (V.disk (closedPoint k)))) = algebraMap k (LaurentSeries k) ∧
    Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X
        (V.disk (closedPoint k)) = V.base := by
  letI := X.openImmersion
  have hbase : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X
        (V.disk (closedPoint k)) = V.base := by
    apply (cancel_mono X.inclusion).mp
    rw [Category.assoc, GeometricComponentCuspBoundR0184.componentGenericOpen_inclusion,
      ← Category.assoc, hθ, Category.assoc, hfac]
    exact V.extends_eq.2.1
  refine ⟨?_, hbase⟩
  have he : CommRingCat.ofHom (θ.comp (AlgebraicCurve.baseToFunctionField
      (projection k L D X (V.disk (closedPoint k))))) =
      CommRingCat.ofHom (algebraMap k (LaurentSeries k)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp,
      ← GeometricComponentCuspBoundR0184.componentGenericOpen_over,
      ← Category.assoc, hbase]
    exact V.classifies.1
  exact congrArg CommRingCat.Hom.hom he

#print axioms component_field_map_over

end ArithmeticComponent

namespace ArithmeticFamily
open CategoryTheory.Limits
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- The base map to the given descended elliptic family, over the actual
function field of the specified arithmetic component. -/
def base : Spec (Component k L D X x).functionField ⟶
    Spec (CommRingCat.of D.atlas.quotient.ring) :=
  GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x ≫ D.quotient.inclusion

abbrev curve : Scheme := pullback D.atlas.descent.family.projection (base k L D X x)
abbrev map : curve k L D X x ⟶ D.atlas.descent.family.curve := pullback.fst _ _
abbrev structureMap : curve k L D X x ⟶ Spec (Component k L D X x).functionField :=
  pullback.snd _ _

instance smooth : SmoothOfRelativeDimension 1 (structureMap k L D X x) := by
  letI := D.atlas.descent.family.smooth
  infer_instance

instance proper : IsProper (structureMap k L D X x) := by
  letI := D.atlas.descent.family.proper
  infer_instance

/-- The identity is obtained by pulling back the actual family identity. -/
def origin : Spec (Component k L D X x).functionField ⟶ curve k L D X x :=
  pullback.lift (base k L D X x ≫ zero D.atlas.descent.family) (𝟙 _) (by
    rw [Category.assoc, (D.atlas.descent.family.law.one (𝟙 _)).property]
    simp)

lemma origin_map : origin k L D X x ≫ map k L D X x =
    base k L D X x ≫ zero D.atlas.descent.family := pullback.lift_fst _ _ _

lemma origin_structure : origin k L D X x ≫ structureMap k L D X x = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance origin_closed : IsClosedImmersion (origin k L D X x) := by
  letI : IsClosedImmersion (origin k L D X x ≫ structureMap k L D X x) := by
    rw [origin_structure]
    infer_instance
  exact IsClosedImmersion.of_comp (origin k L D X x) (structureMap k L D X x)

lemma origin_cartier : (origin k L D X x).ker.IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (origin k L D X x)
    (origin_structure k L D X x)

/-- O(m[0]) on the actual arithmetic generic elliptic curve. -/
def originLine (m : ℕ) : (curve k L D X x).Modules :=
  Scheme.Modules.dual (((origin k L D X x).ker ^ m).module)

lemma originLine_invertible (m : ℕ) :
    Scheme.Modules.IsInvertible (originLine k L D X x m) :=
  ((origin_cartier k L D X x).pow m).isInvertible_module.dual.1

/-- The Hodge line defined by the differential sheaf of this precise family. -/
def hodgeLine : (Spec (Component k L D X x).functionField).Modules :=
  (Scheme.Modules.pullback (origin k L D X x)).obj (structureMap k L D X x).kaehler

lemma hodgeLine_invertible : Scheme.Modules.IsInvertible (hodgeLine k L D X x) :=
  Scheme.Modules.IsInvertible.pullback (origin k L D X x)
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap k L D X x).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1)

/-- The source's actual Hodge-twisted origin line O(m[0]) tensor omega^m.
Its conormal rigidification is constructed below; the symmetric theta lifts
and their Tate normalization remain to be proved. -/
def thetaLine (m : ℕ) : (curve k L D X x).Modules :=
  MonoidalCategory.tensorObj (originLine k L D X x m)
    ((Scheme.Modules.pullback (structureMap k L D X x)).obj
      ((hodgeLine k L D X x).tensorPow m))

lemma thetaLine_invertible (m : ℕ) :
    Scheme.Modules.IsInvertible (thetaLine k L D X x m) :=
  (originLine_invertible k L D X x m).tensor_monoidalV2
    (((hodgeLine_invertible k L D X x).tensorPow m).pullback (structureMap k L D X x))

/-- Pull back a specified family-valued section, retaining its geometric map. -/
def label (P : NeronModelInfra.SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    Spec (Component k L D X x).functionField ⟶ curve k L D X x :=
  pullback.lift (base k L D X x ≫ P.val) (𝟙 _) (by
    rw [Category.assoc, P.property]
    simp)

lemma label_map (P : NeronModelInfra.SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    label k L D X x P ≫ map k L D X x = base k L D X x ≫ P.val :=
  pullback.lift_fst _ _ _

lemma label_structure (P : NeronModelInfra.SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    label k L D X x P ≫ structureMap k L D X x = 𝟙 _ := pullback.lift_snd _ _ _

variable (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

/-- The canonical map from the specified Tate cubic to this arithmetic family. -/
def tateMap : Curve (LaurentSeries k) (TateCurve k L) ⟶ curve k L D X x :=
  pullback.lift V.map
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L) ≫
      Spec.map (CommRingCat.ofHom θ)) (by
    rw [Category.assoc, base, ← Category.assoc (Spec.map _), hb]
    exact V.classifies.2.1.w)

lemma tateMap_map : tateMap k L D X x V θ hb ≫ map k L D X x = V.map :=
  pullback.lift_fst _ _ _

lemma tateMap_structure : tateMap k L D X x V θ hb ≫ structureMap k L D X x =
    ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L) ≫
      Spec.map (CommRingCat.ofHom θ) := pullback.lift_snd _ _ _

lemma tateMap_cartesian : IsPullback (tateMap k L D X x V θ hb)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap k L D X x) (Spec.map (CommRingCat.ofHom θ)) := by
  have houter : IsPullback (tateMap k L D X x V θ hb ≫ map k L D X x)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
      D.atlas.descent.family.projection (Spec.map (CommRingCat.ofHom θ) ≫ base k L D X x) := by
    rw [tateMap_map, base, ← Category.assoc, hb]
    exact V.classifies.2.1
  exact houter.of_right (tateMap_structure k L D X x V θ hb)
    (IsPullback.of_hasPullback _ _)

lemma tateMap_origin :
    ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L) ≫
      tateMap k L D X x V θ hb = Spec.map (CommRingCat.ofHom θ) ≫ origin k L D X x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tateMap_map, origin_map]
    rw [← Category.assoc, base, ← Category.assoc (Spec.map _), hb]
    exact V.classifies.2.2.1
  · have hz : ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L) ≫
        ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L) = 𝟙 _ :=
      (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (TateCurve k L)).property
    simp only [Category.assoc, tateMap_structure, origin_structure]
    rw [← Category.assoc, hz, Category.id_comp]
    exact (Category.comp_id _).symm

lemma tateOrigin_cartesian : IsPullback
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L))
    (Spec.map (CommRingCat.ofHom θ)) (tateMap k L D X x V θ hb) (origin k L D X x) := by
  have houter : IsPullback
      (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L) ≫
        ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
      (Spec.map (CommRingCat.ofHom θ)) (Spec.map (CommRingCat.ofHom θ))
      (origin k L D X x ≫ structureMap k L D X x) := by
    have hz : ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L) ≫
        ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L) = 𝟙 _ :=
      (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (TateCurve k L)).property
    rw [origin_structure, hz]
    exact IsPullback.id_horiz _
  exact houter.of_right (tateMap_origin k L D X x V θ hb)
    (tateMap_cartesian k L D X x V θ hb).flip

/-- The actual arithmetic origin ideal pulls back to the given Tate origin
ideal, as ideal sheaves rather than merely as supports or divisors. -/
lemma originIdeal_tate : (origin k L D X x).ker.comap (tateMap k L D X x V θ hb) =
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L)).ker :=
  ker_baseChange (tateOrigin_cartesian k L D X x V θ hb)

/-- Both full-level labels are inherited from the specified family, and agree
with the prescribed Tate marking under the same Cartesian comparison. -/
lemma label_tate
    (P : NeronModelInfra.SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : NeronModelInfra.SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val) :
    Q.val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ label k L D X x P := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tateMap_map, label_map]
    rw [← Category.assoc, base, ← Category.assoc (Spec.map _), hb]
    exact hQ
  · simp only [Category.assoc, tateMap_structure, label_structure]
    rw [← Category.assoc, Q.property, Category.id_comp]
    exact (Category.comp_id _).symm

lemma full_labels_tate :
    V.level.marking.x.val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ label k L D X x D.atlas.marking.x ∧
    V.level.marking.y.val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ label k L D X x D.atlas.marking.y :=
  ⟨label_tate k L D X x V θ hb _ _ V.classifies.2.2.2.1,
    label_tate k L D X x V θ hb _ _ V.classifies.2.2.2.2⟩

open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open MonoidalCategory

include hb in
lemma tateOrigin_cartier :
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L)).ker.IsInvertible := by
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  letI : SmoothOfRelativeDimension 1
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)) :=
    MorphismProperty.of_isPullback (tateMap_cartesian k L D X x V θ hb) inferInstance
  letI : IsProper
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)) :=
    MorphismProperty.of_isPullback (tateMap_cartesian k L D X x V θ hb) inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L))
    (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (TateCurve k L)).property

/-- Comparison of ideal powers, using the scheme-theoretic equality of the
actual origin ideals and the canonical module pullback comparison. -/
def originPower_tateIso (m : ℕ) :
    (Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj
      (((origin k L D X x).ker ^ m).module) ≅
    (((ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L)).ker ^ m).module) :=
  idealPullbackIso (tateMap k L D X x V θ hb) _ _
    ((origin_cartier k L D X x).pow m) ((tateOrigin_cartier k L D X x V θ hb).pow m)
    (by rw [comap_power, originIdeal_tate])

/-- Base change of O(m[0]) is the actual O(m[0]) on the given Tate cubic;
the isomorphism is built from pullback evaluation and ideal comparison. -/
def originLine_tateIso (m : ℕ) :
    (Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (originLine k L D X x m) ≅
    Scheme.Modules.dual
      (((ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L)).ker ^ m).module) := by
  letI := dualComparison_isIso (tateMap k L D X x V θ hb)
    (((origin k L D X x).ker ^ m).module)
    ((origin_cartier k L D X x).pow m).isInvertible_module
  exact asIso (dualComparison (tateMap k L D X x V θ hb) _) ≪≫
    ((MonoidalClosed.internalHom (C :=
      (Curve (LaurentSeries k) (TateCurve k L)).Modules)).mapIso
        (originPower_tateIso k L D X x V θ hb m).symm.op).app
          (𝟙_ (Curve (LaurentSeries k) (TateCurve k L)).Modules)

#print axioms originLine_invertible
#print axioms tateMap_cartesian
#print axioms originIdeal_tate
#print axioms full_labels_tate
#print axioms originLine_tateIso

/-- Genuine finite-dimensionality of arithmetic sections, with scalar action
induced by the structural morphism. No conclusion is inferred from finrank. -/
lemma originSections_finite (m : ℕ) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module F Γ(originLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.Finite F Γ(originLine k L D X x m, ⊤) :=
  Scheme.Modules.IsInvertible.finite_sections_of_isProper
    (Component k L D X x).functionField (structureMap k L D X x)
    (originLine k L D X x m) (originLine_invertible k L D X x m)

lemma thetaSections_finite (m : ℕ) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.Finite F Γ(thetaLine k L D X x m, ⊤) :=
  Scheme.Modules.IsInvertible.finite_sections_of_isProper
    (Component k L D X x).functionField (structureMap k L D X x)
    (thetaLine k L D X x m) (thetaLine_invertible k L D X x m)

open scoped TensorProduct

/-- Flat base change for the actual section module, phrased with a specified
field embedding to avoid unfolding a concrete generic-stalk presentation. -/
lemma fieldSections_baseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    {Y Y' : Scheme} (p : Y ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (p' : Y' ⟶ Spec (CommRingCat.of K)) (c : Y' ⟶ Y)
    (hc : IsPullback c p' p (Spec.map (CommRingCat.ofHom ι)))
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra F K := ι.toAlgebra
    letI : Algebra F Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(Y, ⊤))
    letI : Algebra K Γ(Y', ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p'.appTop).hom.toAlgebra
    letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
      Module.compHom _ (algebraMap K Γ(Y', ⊤))
    ∃ β : K ⊗[F] Γ(M, ⊤) ≃ₗ[K] Γ((Scheme.Modules.pullback c).obj M, ⊤),
      ∀ s, β (1 ⊗ₜ s) = Scheme.Modules.pullbackLocalSection c s := by
  letI : Algebra F K := ι.toAlgebra
  exact Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    (S := F) K p p' c hc M hM

/-- The arithmetic section space commutes with the specified Laurent-field
base change; pure tensors map to actual sheaf pullback. -/
lemma originSections_baseChange (m : ℕ) :
    let F := (Component k L D X x).functionField
    letI : Algebra F (LaurentSeries k) := θ.toAlgebra
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
    letI : Module F Γ(originLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    letI : Algebra (LaurentSeries k) Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)).appTop).hom.toAlgebra
    letI : Module (LaurentSeries k)
        Γ((Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (originLine k L D X x m), ⊤) :=
      Module.compHom _ (algebraMap (LaurentSeries k) Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))
    ∃ β : LaurentSeries k ⊗[F] Γ(originLine k L D X x m, ⊤) ≃ₗ[LaurentSeries k]
        Γ((Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (originLine k L D X x m), ⊤),
      ∀ s, β (1 ⊗ₜ s) = Scheme.Modules.pullbackLocalSection (tateMap k L D X x V θ hb) s :=
  fieldSections_baseChange θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
    (originLine k L D X x m) (originLine_invertible k L D X x m)

#print axioms originSections_finite
#print axioms originSections_baseChange
#print axioms thetaLine_invertible
#print axioms thetaSections_finite

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

/-- The group operation is the base change of the given descended law. -/
def groupLaw : GoodReductionJacobian.RelativeGroupLaw
    (Component k L D X x).functionField (structureMap k L D X x) :=
  D.atlas.descent.family.law.baseChange (base k L D X x)

lemma groupLaw_origin : ((groupLaw k L D X x).one (𝟙 _)).val =
    origin k L D X x := by
  apply pullback.hom_ext
  · change (pullback.lift (D.atlas.descent.family.law.one (𝟙 _ ≫ base k L D X x)).val
      (𝟙 _) _ ≫ pullback.fst _ _) = _
    rw [pullback.lift_fst, Category.id_comp, origin_map]
    exact (congrArg Subtype.val (D.atlas.descent.family.law.one_natural
      (𝟙 _) (base k L D X x) (base k L D X x) (by simp))).symm
  · exact ((groupLaw k L D X x).one (𝟙 _)).property.trans
      (origin_structure k L D X x).symm

lemma groupLaw_commutative : (groupLaw k L D X x).IsCommutative :=
  GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange
    (base k L D X x) D.atlas.descent.family.commutative

instance connected : GeometricallyConnected (structureMap k L D X x) := by
  letI := D.atlas.descent.family.connected
  infer_instance

lemma geometry : GoodReductionJacobian.AbelianSchemePropertyBundle
    (Component k L D X x).functionField (structureMap k L D X x) where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres := fun z => (structureMap k L D X x).isConnected_preimage_singleton z
  hasGroupLaw := ⟨groupLaw k L D X x⟩

/-- A frame exists over the original component field; no covering field is used.
This choice is used only to compute rank, not to assert Tate normalization. -/
def hodgeFrame : (𝟙_ (Spec (Component k L D X x).functionField).Modules) ≅
    hodgeLine k L D X x :=
  (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    (Component k L D X x).functionField _ (hodgeLine_invertible k L D X x)).some.symm

/-- The existing genus-one section theorem applied to this actual group curve. -/
def framedCurve : FramedCurve (Component k L D X x).functionField where
  target := curve k L D X x
  structureMap := structureMap k L D X x
  law := groupLaw k L D X x
  geometry := geometry k L D X x
  dimension := inferInstance
  hodge := by
    rw [groupLaw_origin]
    exact ⟨hodgeFrame k L D X x⟩

lemma framedCurve_zero : (framedCurve k L D X x).zero = origin k L D X x :=
  groupLaw_origin k L D X x

/-- Exact rank of the section space of O(m[0]), with the actual geometric
scalar action. The arbitrary Hodge frame does not enter the statement. -/
lemma originSections_rank (m : ℕ) (hm : 0 < m) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module F Γ(originLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.finrank F Γ(originLine k L D X x m, ⊤) = m := by
  let F := (Component k L D X x).functionField
  letI : Algebra k F := (AlgebraicCurve.baseToFunctionField (projection k L D X x)).toAlgebra
  letI : CharZero F := Algebra.charZero_of_charZero k F
  letI : Algebra F Γ(curve k L D X x, ⊤) :=
    ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have h :
      let M := ((((groupLaw k L D X x).one (𝟙 _)).val).ker ^ m).invModule
      letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
      Module.finrank F Γ(M, ⊤) = m :=
    (SectionExact.origin_positive_sections_free F (framedCurve k L D X x) m hm).2
  have hM : ((((groupLaw k L D X x).one (𝟙 _)).val).ker ^ m).invModule =
      originLine k L D X x m :=
    congrArg (fun e => (e.ker ^ m).invModule) (groupLaw_origin k L D X x)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap k L D X x)
    (((((groupLaw k L D X x).one (𝟙 _)).val).ker ^ m).invModule) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap k L D X x)
    (originLine k L D X x m) ⊤
  let ε := FibreCohomology.sectionsIsoLinear (structureMap k L D X x) (eqToIso hM) ⊤
  exact ε.finrank_eq.symm.trans h

#print axioms groupLaw_origin
#print axioms originSections_rank

/-- Restriction of the origin ideal to the origin is the actual Hodge line,
via the derivation-defined conormal map. -/
def originConormalIso :
    (Scheme.Modules.pullback (origin k L D X x)).obj (origin k L D X x).ker.module ≅
      hodgeLine k L D X x := by
  have hΩ : Scheme.Modules.IsInvertible (structureMap k L D X x).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap k L D X x).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  letI := Conormal.section_conormal_isIso (structureMap k L D X x) (origin k L D X x)
    (origin_structure k L D X x) (origin_cartier k L D X x) hΩ
  exact asIso (Conormal.conormalMap (structureMap k L D X x) (origin k L D X x))

lemma originConormalIso_hom : (originConormalIso k L D X x).hom =
    Conormal.conormalMap (structureMap k L D X x) (origin k L D X x) := rfl

/-- Multiplication of ideal modules, with its defining inclusion equation. -/
def idealTensorIso {Y : Scheme} {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    I.module ⊗ J.module ≅ (I * J).module :=
  (hI.exists_tensor_iso_mul_module hJ).choose

lemma idealTensorIso_inclusion {Y : Scheme} {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (idealTensorIso hI hJ).hom ≫ (I * J).moduleι =
      (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ Y.Modules)).hom :=
  (hI.exists_tensor_iso_mul_module hJ).choose_spec

/-- The inclusion equation uniquely fixes the multiplication comparison. -/
lemma idealTensorIso_unique {Y : Scheme} {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (μ : I.module ⊗ J.module ≅ (I * J).module)
    (hμ : μ.hom ≫ (I * J).moduleι =
      (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ Y.Modules)).hom) :
    μ = idealTensorIso hI hJ := by
  letI : Mono (I * J).moduleι := by
    unfold Scheme.IdealSheafData.moduleι
    infer_instance
  apply Iso.ext
  exact (cancel_mono (I * J).moduleι).mp (hμ.trans (idealTensorIso_inclusion hI hJ).symm)

/-- Restriction of a positive origin ideal power, built from actual ideal
multiplication and the conormal derivation, without choosing a scalar frame. -/
def originPower_hodgeIso : (m : ℕ) → (0 < m) →
    ((Scheme.Modules.pullback (origin k L D X x)).obj ((origin k L D X x).ker ^ m).module ≅
      (hodgeLine k L D X x).tensorPow m)
  | 0, hm => (Nat.not_lt_zero _ hm).elim
  | 1, _ => by
    simpa only [pow_one] using originConormalIso k L D X x ≪≫
      (Scheme.Modules.tensorPowOneIso (hodgeLine k L D X x)).symm
  | m+2, _ => by
    rw [pow_succ]
    exact (Scheme.Modules.pullback (origin k L D X x)).mapIso
        (idealTensorIso ((origin_cartier k L D X x).pow (m+1)) (origin_cartier k L D X x)).symm ≪≫
      Scheme.Modules.pullbackTensorObjIso (origin k L D X x) _ _ ≪≫
      (originPower_hodgeIso (m+1) (Nat.succ_pos _) ⊗ᵢ originConormalIso k L D X x)

/-- The dual conormal-power identification gives the identity fibre of O(m[0]). -/
def originLine_identityIso (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (origin k L D X x)).obj (originLine k L D X x m) ≅
      Scheme.Modules.dual ((hodgeLine k L D X x).tensorPow m) := by
  letI := dualComparison_isIso (origin k L D X x) ((origin k L D X x).ker ^ m).module
    ((origin_cartier k L D X x).pow m).isInvertible_module
  exact asIso (dualComparison (origin k L D X x) _) ≪≫
    ((MonoidalClosed.internalHom (C := (Spec (Component k L D X x).functionField).Modules)).mapIso
      (originPower_hodgeIso k L D X x m hm).symm.op).app
        (𝟙_ (Spec (Component k L D X x).functionField).Modules)

/-- The source's rigidification is obtained by cancelling the Hodge power
against the conormal-dual fibre. It uses no arbitrary choice of Hodge frame. -/
def thetaRigidification (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (origin k L D X x)).obj (thetaLine k L D X x m) ≅
      𝟙_ (Spec (Component k L D X x).functionField).Modules := by
  let W := (hodgeLine k L D X x).tensorPow m
  let eW : (Scheme.Modules.pullback (origin k L D X x)).obj
      ((Scheme.Modules.pullback (structureMap k L D X x)).obj W) ≅ W :=
    (Scheme.Modules.pullbackComp (origin k L D X x) (structureMap k L D X x)).app W ≪≫
      ((Scheme.Modules.pullbackCongr (origin_structure k L D X x)) ≪≫
        Scheme.Modules.pullbackId _).app W
  letI := ((hodgeLine_invertible k L D X x).tensorPow m).isIso_ihom_ev_app_monoidalV2.1
    (𝟙_ (Spec (Component k L D X x).functionField).Modules)
  exact Scheme.Modules.pullbackTensorObjIso (origin k L D X x) _ _ ≪≫
    (originLine_identityIso k L D X x m hm ⊗ᵢ eW) ≪≫
    (β_ (Scheme.Modules.dual W) W) ≪≫
    asIso ((ihom.ev W).app (𝟙_ (Spec (Component k L D X x).functionField).Modules))

#print axioms originConormalIso
#print axioms idealTensorIso_inclusion
#print axioms originPower_hodgeIso
#print axioms thetaRigidification

/-- Tensor powers of the unit, with the standard unitors. -/
def unitPowerIso {Y : Scheme} : (m : ℕ) → (𝟙_ Y.Modules).tensorPow m ≅ 𝟙_ Y.Modules
  | 0 => Iso.refl _
  | m+1 => (unitPowerIso m ⊗ᵢ Iso.refl _) ≪≫ (λ_ _)

/-- A chosen Hodge frame identifies the twisted and untwisted lines. This
comparison is only used for rank and does not define the rigidification. -/
def thetaLine_originIso (m : ℕ) : thetaLine k L D X x m ≅ originLine k L D X x m :=
  (Iso.refl _ ⊗ᵢ
    ((Scheme.Modules.pullback (structureMap k L D X x)).mapIso
      (Scheme.Modules.tensorPowMapIso (hodgeFrame k L D X x).symm m ≪≫ unitPowerIso m) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso (structureMap k L D X x))) ≪≫ (ρ_ _)

/-- The literal Hodge-twisted theta line also has exactly m sections. -/
lemma thetaSections_rank (m : ℕ) (hm : 0 < m) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.finrank F Γ(thetaLine k L D X x m, ⊤) = m := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap k L D X x)
    (originLine k L D X x m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap k L D X x)
    (thetaLine k L D X x m) ⊤
  let ε := FibreCohomology.sectionsIsoLinear (structureMap k L D X x)
    (thetaLine_originIso k L D X x m) ⊤
  exact ε.finrank_eq.trans (originSections_rank k L D X x m hm)

/-- A basis over the original arithmetic field, before imposing theta
 equivariance. No extension field occurs in this finite-dimensional argument. -/
def thetaSections_basis (m : ℕ) (hm : 0 < m) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.Basis (Fin m) F Γ(thetaLine k L D X x m, ⊤) := by
  let F := (Component k L D X x).functionField
  letI : Algebra F Γ(curve k L D X x, ⊤) :=
    ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
  letI : Module.Finite F Γ(thetaLine k L D X x m, ⊤) := thetaSections_finite k L D X x m
  exact Module.finBasisOfFinrankEq F _ (thetaSections_rank k L D X x m hm)

#print axioms thetaSections_rank
#print axioms thetaSections_basis

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The cotangent Hodge line on the specified Tate cubic. -/
def tateHodgeLine : (Puncture k).Modules :=
  (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin
    (LaurentSeries k) (TateCurve k L))).obj
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)).kaehler

/-- A general pointed differential comparison for a specified field embedding.
Keeping the field presentation abstract avoids unfolding the generic stalk. -/
def fieldHodge_baseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    {Y Y' : Scheme} (p : Y ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (p' : Y' ⟶ Spec (CommRingCat.of K)) (c : Y' ⟶ Y)
    (hc : IsPullback c p' p (Spec.map (CommRingCat.ofHom ι)))
    (s : Spec (CommRingCat.of F) ⟶ Y) (t : Spec (CommRingCat.of K) ⟶ Y')
    (ht : t ≫ c = Spec.map (CommRingCat.ofHom ι) ≫ s) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj
      ((Scheme.Modules.pullback s).obj p.kaehler) ≅
    (Scheme.Modules.pullback t).obj p'.kaehler := by
  letI : Algebra F K := ι.toAlgebra
  exact pointedDifferentialIso p p' c hc s t ht

/-- Differential base change uses the actual Cartesian comparison and identity
map, retaining the geometric scalar embedding. -/
def hodgeLine_tateIso :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom θ))).obj (hodgeLine k L D X x) ≅
      tateHodgeLine k L :=
  fieldHodge_baseChange θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
    (origin k L D X x) (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L))
    (tateMap_origin k L D X x V θ hb)

/-- The same Hodge-twisted line on the given Tate cubic. -/
def tateThetaLine (m : ℕ) : (Curve (LaurentSeries k) (TateCurve k L)).Modules :=
  Scheme.Modules.dual
    (((ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L)).ker ^ m).module) ⊗
  (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.structureMap
    (LaurentSeries k) (TateCurve k L))).obj ((tateHodgeLine k L).tensorPow m)

/-- Comparison of the full theta line, combining the origin ideal and the
actual differential comparison on the prescribed Tate fibre. -/
def thetaLine_tateIso (m : ℕ) :
    (Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (thetaLine k L D X x m) ≅
      tateThetaLine k L m :=
  Scheme.Modules.pullbackTensorObjIso (tateMap k L D X x V θ hb) _ _ ≪≫
    (originLine_tateIso k L D X x V θ hb m ⊗ᵢ
      (squarePullbackIso (tateMap k L D X x V θ hb) (structureMap k L D X x)
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
        (Spec.map (CommRingCat.ofHom θ)) (tateMap_structure k L D X x V θ hb)
        ((hodgeLine k L D X x).tensorPow m) ≪≫
        (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.structureMap
          (LaurentSeries k) (TateCurve k L))).mapIso
          (Scheme.Modules.pullbackTensorPowIso (Spec.map (CommRingCat.ofHom θ)) _ m ≪≫
            Scheme.Modules.tensorPowMapIso (hodgeLine_tateIso k L D X x V θ hb) m)))

/-- Sections of the source's theta line commute with the original Laurent-field
extension, with pure tensors carried to actual sheaf pullback. -/
lemma thetaSections_baseChange (m : ℕ) :
    let F := (Component k L D X x).functionField
    letI : Algebra F (LaurentSeries k) := θ.toAlgebra
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso F).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    letI : Algebra (LaurentSeries k) Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)).appTop).hom.toAlgebra
    letI : Module (LaurentSeries k)
        Γ((Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (thetaLine k L D X x m), ⊤) :=
      Module.compHom _ (algebraMap (LaurentSeries k) Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))
    ∃ β : LaurentSeries k ⊗[F] Γ(thetaLine k L D X x m, ⊤) ≃ₗ[LaurentSeries k]
        Γ((Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj (thetaLine k L D X x m), ⊤),
      ∀ s, β (1 ⊗ₜ s) = Scheme.Modules.pullbackLocalSection (tateMap k L D X x V θ hb) s :=
  fieldSections_baseChange θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
    (thetaLine k L D X x m) (thetaLine_invertible k L D X x m)

#print axioms hodgeLine_tateIso
#print axioms thetaLine_tateIso
#print axioms thetaSections_baseChange

namespace GroupInversion
open NeronModelInfra
variable {F : Type} [Field F] {Y : Scheme} {p : Y ⟶ Spec (CommRingCat.of F)}
    (G : GoodReductionJacobian.RelativeGroupLaw F p)

lemma inverse_natural {T T' : Scheme} (t : T ⟶ Spec (CommRingCat.of F))
    (t' : T' ⟶ Spec (CommRingCat.of F)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t p) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t a) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  letI := G.pointGroup t'
  have hmul : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t a))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ a) = G.one t' := by
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural]
  exact eq_inv_of_mul_eq_one_left hmul

/-- Inversion on the given scheme-valued group functor. -/
def morphism : Y ⟶ Y := (G.inv p ⟨𝟙 Y, Category.id_comp p⟩).val

lemma over_eq : morphism G ≫ p = p := (G.inv p ⟨𝟙 Y, Category.id_comp p⟩).property

lemma square : morphism G ≫ morphism G = 𝟙 Y := by
  let a : SchemeHomOver p p := ⟨𝟙 Y, Category.id_comp p⟩
  let n := G.inv p a
  have hn : GoodReductionJacobian.schemeHomOverComp n.val n.property a = n := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural G p p n.val n.property a
  rw [hn] at h
  have hi : G.inv p (G.inv p a) = a := by
    letI := G.pointGroup p
    exact inv_inv a
  have he : GoodReductionJacobian.schemeHomOverComp n.val n.property n = a := h.trans hi
  exact congrArg Subtype.val he

def iso : Y ≅ Y where
  hom := morphism G
  inv := morphism G
  hom_inv_id := square G
  inv_hom_id := square G

lemma fixes_one : (G.one (𝟙 _)).val ≫ morphism G = (G.one (𝟙 _)).val := by
  let a : SchemeHomOver p p := ⟨𝟙 Y, Category.id_comp p⟩
  let z := G.one (𝟙 _)
  have hz : GoodReductionJacobian.schemeHomOverComp z.val z.property a = z := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural G p (𝟙 _) z.val z.property a
  rw [hz] at h
  have hi : G.inv (𝟙 _) z = z := by
    letI := G.pointGroup (𝟙 _)
    exact inv_one
  exact congrArg Subtype.val (h.trans hi)

end GroupInversion

/-- The arithmetic inversion is taken from the original descended group law. -/
def inverseIso : curve k L D X x ≅ curve k L D X x :=
  GroupInversion.iso (groupLaw k L D X x)

lemma inverse_over : (inverseIso k L D X x).hom ≫ structureMap k L D X x =
    structureMap k L D X x := GroupInversion.over_eq (groupLaw k L D X x)

lemma inverse_origin : origin k L D X x ≫ (inverseIso k L D X x).hom =
    origin k L D X x := by
  rw [← groupLaw_origin]
  exact GroupInversion.fixes_one (groupLaw k L D X x)

lemma originIdeal_inverse : (origin k L D X x).ker.comap (inverseIso k L D X x).hom =
    (origin k L D X x).ker :=
  ker_baseChange (IsPullback.of_vert_isIso
    (show CommSq (origin k L D X x) (𝟙 _) (inverseIso k L D X x).hom
      (origin k L D X x) from ⟨by rw [inverse_origin, Category.id_comp]⟩))

/-- Invariance of O(m[0]) under the actual inversion, through its ideal sheaf. -/
def originLine_inverseIso (m : ℕ) :
    (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (originLine k L D X x m) ≅
      originLine k L D X x m := by
  let e := idealPullbackIso (inverseIso k L D X x).hom
    ((origin k L D X x).ker ^ m) ((origin k L D X x).ker ^ m)
    ((origin_cartier k L D X x).pow m) ((origin_cartier k L D X x).pow m)
    (by rw [comap_power, originIdeal_inverse])
  letI := dualComparison_isIso (inverseIso k L D X x).hom
    ((origin k L D X x).ker ^ m).module ((origin_cartier k L D X x).pow m).isInvertible_module
  exact asIso (dualComparison (inverseIso k L D X x).hom _) ≪≫
    ((MonoidalClosed.internalHom (C := (curve k L D X x).Modules)).mapIso e.symm.op).app
      (𝟙_ (curve k L D X x).Modules)

/-- Inversion also preserves the full Hodge-twisted line. The normalization on
2-torsion and compatibility with the rigidification are separate assertions. -/
def thetaLine_inverseIso (m : ℕ) :
    (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (thetaLine k L D X x m) ≅
      thetaLine k L D X x m :=
  Scheme.Modules.pullbackTensorObjIso (inverseIso k L D X x).hom _ _ ≪≫
    (originLine_inverseIso k L D X x m ⊗ᵢ
      ((Scheme.Modules.pullbackComp (inverseIso k L D X x).hom
        (structureMap k L D X x)).app ((hodgeLine k L D X x).tensorPow m) ≪≫
        (Scheme.Modules.pullbackCongr (inverse_over k L D X x)).app
          ((hodgeLine k L D X x).tensorPow m)))

#print axioms inverseIso
#print axioms inverse_origin
#print axioms originIdeal_inverse
#print axioms thetaLine_inverseIso

/-- Multiplication by n on the arithmetic curve retains the descended family map. -/
lemma multiplication_map (n : ℕ) :
    (groupLaw k L D X x).schemeNsmul n ≫ map k L D X x =
      map k L D X x ≫ D.atlas.descent.family.law.schemeNsmul n :=
  (D.atlas.descent.family.law.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
    (base k L D X x) n).1.w.symm

/-- Torsion of a prescribed family label is preserved on the actual generic curve. -/
lemma label_killed (n : ℕ)
    (P : NeronModelInfra.SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hP : P.val ≫ D.atlas.descent.family.law.schemeNsmul n = zero D.atlas.descent.family) :
    label k L D X x P ≫ (groupLaw k L D X x).schemeNsmul n = origin k L D X x := by
  apply pullback.hom_ext
  · rw [Category.assoc, multiplication_map, ← Category.assoc, label_map,
      Category.assoc, hP, origin_map]
  · rw [Category.assoc, (groupLaw k L D X x).schemeNsmul_over,
      label_structure, origin_structure]

lemma full_labels_killed :
    label k L D X x D.atlas.marking.x ≫ (groupLaw k L D X x).schemeNsmul L = origin k L D X x ∧
    label k L D X x D.atlas.marking.y ≫ (groupLaw k L D X x).schemeNsmul L = origin k L D X x :=
  ⟨label_killed k L D X x L D.atlas.marking.x D.atlas.marking.killed_x,
    label_killed k L D X x L D.atlas.marking.y D.atlas.marking.killed_y⟩

#print axioms idealTensorIso_unique
#print axioms full_labels_killed

/-- The arithmetic structural map identifies its field with all global regular
functions. This is the geometric scalar map, not a chosen algebra structure. -/
lemma constants_bijective : Function.Bijective
    (((Scheme.ΓSpecIso (CommRingCat.of (Component k L D X x).functionField)).inv ≫
      (structureMap k L D X x).appTop).hom) := by
  let F := (Component k L D X x).functionField
  letI : Algebra k F := (AlgebraicCurve.baseToFunctionField (projection k L D X x)).toAlgebra
  letI : CharZero F := Algebra.charZero_of_charZero k F
  exact ((framedCurve k L D X x).structure_app_bijective ⊤).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.bijective

/-- Every endomorphism of the actual theta line is one scalar from the
original arithmetic field, acting on every open of the curve. -/
lemma thetaEnd_scalar (m : ℕ) (σ : thetaLine k L D X x m ⟶ thetaLine k L D X x m) :
    ∃! c : (Component k L D X x).functionField,
      RiemannForm.IsConstScalar (structureMap k L D X x) σ c :=
  RiemannForm.existsUnique_isConstScalar _ (structureMap k L D X x)
    (geometry k L D X x) _ (thetaLine_invertible k L D X x m) σ

/-- Rigidification of the inversion pullback using its actual fixed identity. -/
def inverseRigidification (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (origin k L D X x)).obj
      ((Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (thetaLine k L D X x m)) ≅
      𝟙_ (Spec (Component k L D X x).functionField).Modules :=
  (Scheme.Modules.pullbackComp (origin k L D X x) (inverseIso k L D X x).hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr (inverse_origin k L D X x)).app _ ≪≫
    thetaRigidification k L D X x m hm

/-- There is exactly one inversion comparison compatible with the conormal
rigidification. Neither a square root nor a covering field is chosen. -/
lemma existsUnique_normalizedInversion (m : ℕ) (hm : 0 < m) :
    ∃! φ : (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj
        (thetaLine k L D X x m) ≅ thetaLine k L D X x m,
      (Scheme.Modules.pullback (origin k L D X x)).mapIso φ ≪≫
        thetaRigidification k L D X x m hm = inverseRigidification k L D X x m hm := by
  let M := (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (thetaLine k L D X x m)
  let N := thetaLine k L D X x m
  let α := inverseRigidification k L D X x m hm
  let β := thetaRigidification k L D X x m hm
  obtain ⟨φ, hφ⟩ := Polarisation.nonempty_rigidifiedIso_of_iso
    (structureMap k L D X x) (constants_bijective k L D X x)
    (origin k L D X x) (origin_structure k L D X x) M N α β
    (thetaLine_inverseIso k L D X x m)
  haveI := Polarisation.subsingleton_rigidifiedIso
    (structureMap k L D X x) (constants_bijective k L D X x)
    (origin k L D X x) (origin_structure k L D X x) M N
    ((thetaLine_invertible k L D X x m).pullback _) α β
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨ψ, hψ⟩ : {ψ : M ≅ N // (Scheme.Modules.pullback (origin k L D X x)).mapIso ψ ≪≫ β = α})
    ⟨φ, hφ⟩)

/-- The uniquely normalized inversion on the arithmetic theta line. -/
def normalizedInversion (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (thetaLine k L D X x m) ≅
      thetaLine k L D X x m :=
  (existsUnique_normalizedInversion k L D X x m hm).choose

lemma normalizedInversion_identity (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (origin k L D X x)).mapIso (normalizedInversion k L D X x m hm) ≪≫
      thetaRigidification k L D X x m hm = inverseRigidification k L D X x m hm :=
  (existsUnique_normalizedInversion k L D X x m hm).choose_spec.1

/-- An automorphism of the arithmetic theta line fixing its rigidification is
identity. The equality concerns sheaf maps on all opens. -/
lemma rigidifiedAut_eq_refl (m : ℕ) (hm : 0 < m)
    (φ : thetaLine k L D X x m ≅ thetaLine k L D X x m)
    (hφ : (Scheme.Modules.pullback (origin k L D X x)).mapIso φ ≪≫
      thetaRigidification k L D X x m hm = thetaRigidification k L D X x m hm) :
    φ = Iso.refl _ := by
  let M := thetaLine k L D X x m
  let α := thetaRigidification k L D X x m hm
  haveI := Polarisation.subsingleton_rigidifiedIso
    (structureMap k L D X x) (constants_bijective k L D X x)
    (origin k L D X x) (origin_structure k L D X x) M M
    (thetaLine_invertible k L D X x m) α α
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨φ, hφ⟩ : {ψ : M ≅ M // (Scheme.Modules.pullback (origin k L D X x)).mapIso ψ ≪≫ α = α})
    ⟨Iso.refl _, by simp⟩)

#print axioms constants_bijective
#print axioms thetaEnd_scalar
#print axioms existsUnique_normalizedInversion
#print axioms normalizedInversion_identity
#print axioms rigidifiedAut_eq_refl

/-- Positive origin powers have no higher cohomology on the actual arithmetic
curve; the argument retains the given geometric field action. -/
lemma origin_higher_cohomology (m : ℕ) (hm : 0 < m)
    (𝒰 : (curve k L D X x).OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules (structureMap k L D X x)
      (originLine k L D X x m)).HSucc 𝒰 i) := by
  let F := (Component k L D X x).functionField
  letI : Algebra k F := (AlgebraicCurve.baseToFunctionField (projection k L D X x)).toAlgebra
  letI : CharZero F := Algebra.charZero_of_charZero k F
  have h := PositiveSections.Actual.positive_higher_cohomology F
    (framedCurve k L D X x) m hm 𝒰 i
  change Subsingleton ((OModulePresheaf.ofModules (structureMap k L D X x)
    (((((groupLaw k L D X x).one (𝟙 _)).val).ker ^ m).invModule)).HSucc 𝒰 i) at h
  rw [groupLaw_origin] at h
  exact h

/-- The Euler characteristic of O(m[0]) is m on every finite affine cover. -/
lemma origin_eulerChar (m : ℕ) (hm : 0 < m)
    (𝒰 : (curve k L D X x).OrderedAffineCover) :
    (OModulePresheaf.ofModules (structureMap k L D X x)
      (originLine k L D X x m)).eulerChar 𝒰 = (m : ℤ) := by
  let F := (Component k L D X x).functionField
  let M := originLine k L D X x m
  let C := OModulePresheaf.ofModules (structureMap k L D X x) M
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap k L D X x) M ⊤
  obtain ⟨ε⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    (structureMap k L D X x) M 𝒰
  have hrank : Module.finrank F (C.H0 𝒰) = m :=
    ε.finrank_eq.symm.trans (originSections_rank k L D X x m hm)
  have hi (i : ℕ) : C.cechFinrank 𝒰 (i+1) = 0 := by
    letI := origin_higher_cohomology k L D X x m hm 𝒰 i
    change Module.finrank F (C.HSucc 𝒰 i) = 0
    exact Module.finrank_zero_of_subsingleton
  have hcard : 0 < Fintype.card 𝒰.ι := by
    let y := origin k L D X x (IsLocalRing.closedPoint F)
    have hy : y ∈ ⨆ j, 𝒰.U j := by rw [𝒰.iSup_eq_top]; trivial
    obtain ⟨j, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact Fintype.card_pos_iff.mpr ⟨j⟩
  change C.eulerChar 𝒰 = _
  rw [OModulePresheaf.eulerChar_def]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, OModulePresheaf.cechFinrank_zero]
    change (Module.finrank F (C.H0 𝒰) : ℤ) = (m : ℤ)
    exact congrArg (fun n : ℕ => (n : ℤ)) hrank
  · intro i _ hi0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [hi, Nat.cast_zero, mul_zero]
  · simp only [Finset.mem_range, hcard, not_true_eq_false, IsEmpty.forall_iff]

#print axioms origin_higher_cohomology
#print axioms origin_eulerChar

namespace FixedPointPullback
open Scheme.Modules
variable {S₀ S₁ S₂ S₃ : Scheme}

/-- Pullback composition with its specified equality of geometric maps. -/
def compare (f : S₀ ⟶ S₁) (g : S₁ ⟶ S₂) (fg : S₀ ⟶ S₂) (h : f ≫ g = fg) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback fg := pullbackComp f g ≪≫ pullbackCongr h

lemma compare_hom (f : S₀ ⟶ S₁) (g : S₁ ⟶ S₂) (fg : S₀ ⟶ S₂) (h : f ≫ g = fg)
    (M : S₂.Modules) :
    (compare f g fg h).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [h]) := by
  subst fg
  simp [compare, pullbackCongr]

lemma assoc_app (f : S₀ ⟶ S₁) (g : S₁ ⟶ S₂) (h : S₂ ⟶ S₃) (M : S₃.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M := by
  have H := congr_app (congr_arg Iso.hom
    (SheafOfModules.pullback_assoc h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app] at H
  erw [Category.id_comp] at H
  exact H.symm

lemma compare_comp (f : S₀ ⟶ S₁) (g : S₁ ⟶ S₂) (h : S₂ ⟶ S₃)
    (fg : S₀ ⟶ S₂) (gh : S₁ ⟶ S₃) (fgh : S₀ ⟶ S₃)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (M : S₃.Modules) :
    (compare f g fg hfg).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (compare fg h fgh hfgh).hom.app M =
      (Scheme.Modules.pullback f).map ((compare g h gh hgh).hom.app M) ≫
        (compare f gh fgh (by rw [← hgh, ← Category.assoc, hfg, hfgh])).hom.app M := by
  subst fg gh fgh
  simp only [compare_hom, eqToHom_refl, Category.comp_id]
  exact (assoc_app f g h M).symm

lemma compare_id (f : S₀ ⟶ S₁) (M : S₁.Modules) :
    (compare f (𝟙 _) f (Category.comp_id f)).hom.app M =
      (Scheme.Modules.pullback f).map ((pullbackId S₁).hom.app M) := by
  change (pullbackComp f (𝟙 _)).hom.app M = _
  apply (cancel_epi ((pullbackComp f (𝟙 _)).inv.app M)).mp
  rw [Iso.inv_hom_id_app]
  have H := NatTrans.congr_app (pseudofunctor_left_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app, eqToHom_refl] at H
  erw [Category.comp_id ((Scheme.Modules.pullback f).map ((pullbackId S₁).hom.app M))] at H
  exact H.symm

/-- A comparison normalized at a fixed section squares to the canonical
identity comparison on that section. This uses pullback coherence explicitly. -/
lemma square_on_fixed_section (e : S₀ ⟶ S₁) (g : S₁ ⟶ S₁)
    (he : e ≫ g = e) (hg : g ≫ g = 𝟙 _) (M : S₁.Modules)
    (φ : (Scheme.Modules.pullback g).obj M ≅ M)
    (hφ : (Scheme.Modules.pullback e).map φ.hom = (compare e g e he).hom.app M) :
    (Scheme.Modules.pullback e).map ((Scheme.Modules.pullback g).map φ.hom ≫ φ.hom) =
      (Scheme.Modules.pullback e).map ((compare g g (𝟙 _) hg).hom.app M ≫ (pullbackId S₁).hom.app M) := by
  rw [Functor.map_comp, hφ]
  change ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback e).map φ.hom ≫ (compare e g e he).hom.app M) = _
  rw [(compare e g e he).hom.naturality, hφ]
  rw [compare_comp e g g e (𝟙 _) e he hg he M]
  rw [compare_id]
  exact (Functor.map_comp _ _ _).symm


def squareComparison (g : S₁ ⟶ S₁) (hg : g ≫ g = 𝟙 _) (M : S₁.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback g).obj M) ≅ M :=
  (compare g g (𝟙 _) hg).app M ≪≫ (Scheme.Modules.pullbackId _).app M

lemma square_of_rigidified (e : S₀ ⟶ S₁) (g : S₁ ⟶ S₁)
    (he : e ≫ g = e) (hg : g ≫ g = 𝟙 _) (M : S₁.Modules)
    (N : S₀.Modules) (α : (Scheme.Modules.pullback e).obj M ≅ N)
    (φ : (Scheme.Modules.pullback g).obj M ≅ M)
    (hφ : (Scheme.Modules.pullback e).mapIso φ ≪≫ α =
      (pullbackComp e g).app M ≪≫ (pullbackCongr he).app M ≪≫ α)
    (hunique : ∀ ψ : M ≅ M, (Scheme.Modules.pullback e).mapIso ψ ≪≫ α = α → ψ = Iso.refl M) :
    (Scheme.Modules.pullback g).mapIso φ ≪≫ φ = squareComparison g hg M := by
  let C := squareComparison g hg M
  have hn : (compare e g e he).app M ≪≫ α =
      (pullbackComp e g).app M ≪≫ (pullbackCongr he).app M ≪≫ α := by
    rw [compare, NatIso.trans_app, Iso.trans_assoc]
  have hf : (Scheme.Modules.pullback e).map φ.hom = (compare e g e he).hom.app M :=
    (cancel_mono α.hom).mp (congrArg Iso.hom (hφ.trans hn.symm))
  have H := square_on_fixed_section e g he hg M φ hf
  let ψ : M ≅ M := C.symm ≪≫ (Scheme.Modules.pullback g).mapIso φ ≪≫ φ
  have hψ : (Scheme.Modules.pullback e).map ψ.hom = 𝟙 _ := by
    change (Scheme.Modules.pullback e).map
      (C.inv ≫ (Scheme.Modules.pullback g).map φ.hom ≫ φ.hom) = _
    rw [Functor.map_comp, H, ← Functor.map_comp]
    exact (congrArg (Scheme.Modules.pullback e).map C.inv_hom_id).trans
      ((Scheme.Modules.pullback e).map_id _)
  have hψ' : ψ = Iso.refl M := hunique ψ (by
    apply Iso.ext
    change (Scheme.Modules.pullback e).map ψ.hom ≫ _ = _
    rw [hψ, Category.id_comp])
  have He := congrArg Iso.hom hψ'
  apply Iso.ext
  change (Scheme.Modules.pullback g).map φ.hom ≫ φ.hom = C.hom
  calc
    _ = C.hom ≫ ψ.hom := by simp [ψ]
    _ = C.hom := by rw [He, Iso.refl_hom, Category.comp_id]

end FixedPointPullback

/-- The standard identification of the twice-inverted line with itself. -/
def inversionSquareComparison (m : ℕ) :
    (Scheme.Modules.pullback (inverseIso k L D X x).hom).obj
      ((Scheme.Modules.pullback (inverseIso k L D X x).hom).obj (thetaLine k L D X x m)) ≅
      thetaLine k L D X x m :=
  FixedPointPullback.squareComparison (inverseIso k L D X x).hom
    (GroupInversion.square (groupLaw k L D X x)) (thetaLine k L D X x m)

/-- The uniquely rigidified inversion is an involution on the actual line,
with the canonical double-pullback comparison included in the statement. -/
lemma normalizedInversion_square (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (inverseIso k L D X x).hom).mapIso
        (normalizedInversion k L D X x m hm) ≪≫ normalizedInversion k L D X x m hm =
      inversionSquareComparison k L D X x m :=
  FixedPointPullback.square_of_rigidified (origin k L D X x) (inverseIso k L D X x).hom
    (inverse_origin k L D X x) (GroupInversion.square (groupLaw k L D X x))
    (thetaLine k L D X x m) _ (thetaRigidification k L D X x m hm)
    (normalizedInversion k L D X x m hm) (normalizedInversion_identity k L D X x m hm)
    (rigidifiedAut_eq_refl k L D X x m hm)

#print axioms normalizedInversion_square

end ArithmeticFamily

end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.GroupTranslation
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
variable {R : Type} [CommRing R] {Y : Scheme} {p : Y ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R p)

lemma point_translate {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t p) (b : SchemeHomOver (𝟙 _) p) :
    a.val ≫ G.translate b =
      (G.mul t a ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩).val := by
  have h := G.mul_natural p t a.val a.property RelativeGroupLaw.idPoint
    ⟨p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  have h₁ : schemeHomOverComp a.val a.property RelativeGroupLaw.idPoint = a := by
    apply Subtype.ext
    exact Category.comp_id _
  have h₂ : schemeHomOverComp a.val a.property
      (⟨p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ : SchemeHomOver p p) =
      ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b.val) a.property)
  rw [h₁, h₂] at h
  exact congrArg Subtype.val h

lemma comp (a b : SchemeHomOver (𝟙 _) p) :
    G.translate a ≫ G.translate b = G.translate (G.mul (𝟙 _) a b) := by
  let ca : SchemeHomOver p p := ⟨p ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let cb : SchemeHomOver p p := ⟨p ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  have h := point_translate G p (G.mul p RelativeGroupLaw.idPoint ca) b
  have hn := G.mul_natural (𝟙 _) p p (Category.comp_id p) a b
  have hca : schemeHomOverComp p (Category.comp_id p) a = ca := rfl
  have hcb : schemeHomOverComp p (Category.comp_id p) b = cb := rfl
  rw [hca, hcb] at hn
  have hc : (⟨p ≫ (G.mul (𝟙 _) a b).val, by
      rw [Category.assoc, (G.mul (𝟙 _) a b).property, Category.comp_id]⟩ : SchemeHomOver p p) =
      G.mul p ca cb := hn
  change G.translate a ≫ G.translate b = (G.mul p RelativeGroupLaw.idPoint _).val
  rw [hc, ← G.mul_assoc]
  exact h

def iso (a : SchemeHomOver (𝟙 _) p) : Y ≅ Y where
  hom := G.translate a
  inv := G.translate (G.inv (𝟙 _) a)
  hom_inv_id := by rw [comp, G.mul_inv_cancel, G.translate_one]
  inv_hom_id := by rw [comp, G.inv_mul_cancel, G.translate_one]

lemma comm (hc : G.IsCommutative) (a b : SchemeHomOver (𝟙 _) p) :
    G.translate a ≫ G.translate b = G.translate b ≫ G.translate a := by
  rw [comp, comp, hc.mul_comm]

lemma nsmul_eq_pow {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t p) (n : ℕ) :
    letI := G.pointGroup t
    G.nsmul t n a = a ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih]; rfl

lemma nsmul_mul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t p) (n m : ℕ) :
    G.nsmul t n (G.nsmul t m a) = G.nsmul t (m*n) a := by
  letI := G.pointGroup t
  simp only [nsmul_eq_pow, pow_mul]

lemma point_schemeNsmul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t p) (n : ℕ) :
    a.val ≫ G.schemeNsmul n = (G.nsmul t n a).val := by
  have h := G.nsmul_natural p t a.val a.property n RelativeGroupLaw.idPoint
  have ha : schemeHomOverComp a.val a.property RelativeGroupLaw.idPoint = a := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha] at h
  exact congrArg Subtype.val h

lemma translate_nsmul (a : SchemeHomOver (𝟙 _) p) (n : ℕ) :
    End.of (G.translate a) ^ n = End.of (G.translate (G.nsmul (𝟙 _) n a)) := by
  induction n with
  | zero => exact (G.translate_one).symm
  | succ n ih =>
    rw [pow_succ, ih, G.nsmul_succ]
    change G.translate a ≫ G.translate (G.nsmul (𝟙 _) n a) = _
    rw [comp]
    congr 1
    letI := G.pointGroup (𝟙 _)
    rw [nsmul_eq_pow]
    exact (Commute.self_pow a n).eq

lemma translate_order (a : SchemeHomOver (𝟙 _) p) (n : ℕ)
    (ha : G.nsmul (𝟙 _) n a = G.one (𝟙 _)) :
    End.of (G.translate a) ^ n = 1 := by
  rw [translate_nsmul, ha, G.translate_one]
  rfl

#print axioms iso
#print axioms translate_order
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.GroupTranslation

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- The given full-level label as a rational point over the original component field. -/
def labelPoint (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    SchemeHomOver (𝟙 _) (structureMap k L D X x) :=
  ⟨label k L D X x P, label_structure k L D X x P⟩

lemma labelPoint_killed (n : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hP : P.val ≫ D.atlas.descent.family.law.schemeNsmul n =
      ArithmeticThetaOpenHodgeR0180.zero D.atlas.descent.family) :
    (groupLaw k L D X x).nsmul (𝟙 _) n (labelPoint k L D X x P) =
      (groupLaw k L D X x).one (𝟙 _) := by
  apply Subtype.ext
  rw [← GroupTranslation.point_schemeNsmul, groupLaw_origin]
  exact label_killed k L D X x n P hP

/-- Doubling a prescribed full 2m-level label gives the required m-level point. -/
def doubledLabel (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    SchemeHomOver (𝟙 _) (structureMap k L D X x) :=
  (groupLaw k L D X x).nsmul (𝟙 _) 2 (labelPoint k L D X x P)

lemma doubledLabel_killed (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hP : P.val ≫ D.atlas.descent.family.law.schemeNsmul (2*m) =
      ArithmeticThetaOpenHodgeR0180.zero D.atlas.descent.family) :
    (groupLaw k L D X x).nsmul (𝟙 _) m (doubledLabel k L D X x P) =
      (groupLaw k L D X x).one (𝟙 _) := by
  unfold doubledLabel
  rw [GroupTranslation.nsmul_mul]
  exact labelPoint_killed k L D X x (2*m) P hP

/-- The actual translation automorphism attached to the prescribed doubled label. -/
def labelTranslation (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    curve k L D X x ≅ curve k L D X x :=
  GroupTranslation.iso (groupLaw k L D X x) (doubledLabel k L D X x P)

lemma labelTranslation_order (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hP : P.val ≫ D.atlas.descent.family.law.schemeNsmul (2*m) =
      ArithmeticThetaOpenHodgeR0180.zero D.atlas.descent.family) :
    End.of (labelTranslation k L D X x P).hom ^ m = 1 :=
  GroupTranslation.translate_order (groupLaw k L D X x) _ m
    (doubledLabel_killed k L D X x m P hP)

lemma labelTranslations_commute
    (P Q : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    (labelTranslation k L D X x P).hom ≫ (labelTranslation k L D X x Q).hom =
      (labelTranslation k L D X x Q).hom ≫ (labelTranslation k L D X x P).hom :=
  GroupTranslation.comm (groupLaw k L D X x) (groupLaw_commutative k L D X x) _ _

variable (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

lemma tateMap_nsmul (n : ℕ) :
    V.level.law.schemeNsmul n ≫ tateMap k L D X x V θ hb =
      tateMap k L D X x V θ hb ≫ (groupLaw k L D X x).schemeNsmul n := by
  apply pullback.hom_ext
  · rw [Category.assoc, tateMap_map, Category.assoc, multiplication_map,
      ← Category.assoc, tateMap_map]
    exact V.nsmul_eq n
  · rw [Category.assoc, tateMap_structure, Category.assoc,
      (groupLaw k L D X x).schemeNsmul_over, ← Category.assoc,
      V.level.law.schemeNsmul_over]
    exact (tateMap_structure k L D X x V θ hb).symm

/-- The original Tate comparison preserves the actual group operations on all
scheme-valued points, by uniqueness of the pointed elliptic group law. -/
lemma tateMap_mul {T : Scheme} (t : T ⟶ Puncture k)
    (a b : SchemeHomOver t
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))) :
    (V.level.law.mul t a b).val ≫ tateMap k L D X x V θ hb =
      ((groupLaw k L D X x).mul (t ≫ Spec.map (CommRingCat.ofHom θ))
        ⟨a.val ≫ tateMap k L D X x V θ hb, by
          rw [Category.assoc, tateMap_structure, ← Category.assoc, a.property]⟩
        ⟨b.val ≫ tateMap k L D X x V θ hb, by
          rw [Category.assoc, tateMap_structure, ← Category.assoc, b.property]⟩).val := by
  letI := V.level.elliptic
  let G := ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.toWeierstrassLaw
    (groupLaw k L D X x)
  obtain ⟨H, hm, ho⟩ := WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb) G
  have hone : (V.level.law.one (𝟙 _)).val = (H.one (𝟙 _)).val := by
    apply (tateMap_cartesian k L D X x V θ hb).hom_ext
    · rw [V.level.originLaw.1, Category.id_comp, tateMap_origin, ho, Category.id_comp]
      change Spec.map (CommRingCat.ofHom θ) ≫ origin k L D X x =
        ((groupLaw k L D X x).one (Spec.map (CommRingCat.ofHom θ))).val
      rw [← groupLaw_origin]
      exact congrArg Subtype.val ((groupLaw k L D X x).one_natural
        (𝟙 _) (Spec.map (CommRingCat.ofHom θ)) (Spec.map (CommRingCat.ofHom θ))
        (Category.comp_id _))
    · exact (V.level.law.one (𝟙 _)).property.trans (H.one (𝟙 _)).property.symm
  rw [WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
    (TateCurve k L).toProjective V.level.law H hone t a b]
  exact hm t a b

lemma doubledLabel_tate
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val) :
    (V.level.law.nsmul (𝟙 _) 2 Q).val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ (doubledLabel k L D X x P).val := by
  have hQn : Q.val ≫ V.level.law.schemeNsmul 2 = (V.level.law.nsmul (𝟙 _) 2 Q).val := by
    have h := V.level.law.nsmul_natural
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
      (𝟙 _) Q.val Q.property 2 WeierstrassProjModel.RelativeGroupLaw.idPoint
    have he : WeierstrassProjModel.schemeHomOverComp Q.val Q.property
        WeierstrassProjModel.RelativeGroupLaw.idPoint = Q := by
      apply Subtype.ext
      exact Category.comp_id _
    rw [he] at h
    exact congrArg Subtype.val h
  rw [← hQn, Category.assoc, tateMap_nsmul,
    ← Category.assoc, label_tate k L D X x V θ hb P Q hQ,
    Category.assoc]
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom θ) ≫ z)
    (GroupTranslation.point_schemeNsmul (groupLaw k L D X x) (𝟙 _)
      (labelPoint k L D X x P) 2)

/-- Translation by matching rational points commutes with the original
Tate comparison as an equality of scheme morphisms. -/
lemma translation_tate
    (a : SchemeHomOver (𝟙 _) (structureMap k L D X x))
    (b : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hab : b.val ≫ tateMap k L D X x V θ hb = Spec.map (CommRingCat.ofHom θ) ≫ a.val) :
    ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.level.law b ≫
        tateMap k L D X x V θ hb =
      tateMap k L D X x V θ hb ≫ (groupLaw k L D X x).translate a := by
  let pT := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)
  let g := tateMap k L D X x V θ hb
  let φ := Spec.map (CommRingCat.ofHom θ)
  let ap : SchemeHomOver (pT ≫ φ) (structureMap k L D X x) :=
    ⟨g, tateMap_structure k L D X x V θ hb⟩
  let bp : SchemeHomOver pT pT := WeierstrassProjModel.schemeHomOverComp pT (Category.comp_id pT) b
  have h := tateMap_mul k L D X x V θ hb pT
    WeierstrassProjModel.RelativeGroupLaw.idPoint bp
  have hfirst : (⟨(WeierstrassProjModel.RelativeGroupLaw.idPoint (f := pT)).val ≫ g,
        by rw [Category.assoc, tateMap_structure, ← Category.assoc,
          WeierstrassProjModel.RelativeGroupLaw.idPoint.property]⟩ :
      SchemeHomOver (pT ≫ φ) (structureMap k L D X x)) = ap := by
    apply Subtype.ext
    exact Category.id_comp _
  have hsecond : (⟨bp.val ≫ g, by
        rw [Category.assoc, tateMap_structure, ← Category.assoc, bp.property]⟩ :
      SchemeHomOver (pT ≫ φ) (structureMap k L D X x)) =
      ⟨(pT ≫ φ) ≫ a.val, by
        rw [Category.assoc, a.property]
        exact Category.comp_id (pT ≫ φ)⟩ := by
    apply Subtype.ext
    change (pT ≫ b.val) ≫ g = (pT ≫ φ) ≫ a.val
    rw [Category.assoc, hab, Category.assoc]
  rw [hfirst, hsecond] at h
  exact h.trans (GroupTranslation.point_translate (groupLaw k L D X x) (pT ≫ φ) ap a).symm

lemma labelTranslation_tate
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val) :
    ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.level.law
        (V.level.law.nsmul (𝟙 _) 2 Q) ≫ tateMap k L D X x V θ hb =
      tateMap k L D X x V θ hb ≫ (labelTranslation k L D X x P).hom :=
  translation_tate k L D X x V θ hb _ _ (doubledLabel_tate k L D X x V θ hb P Q hQ)

/-- The two translations at the exact full 2m level are defined over its
original component field and satisfy the required geometric order laws. -/
lemma full_level_translations (m : ℕ)
    (D₂ : LevelData k (2*m)) (X₂ : Compactification k (2*m) D₂) (x₂ : X₂.space) :
    End.of (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.x).hom ^ m = 1 ∧
    End.of (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.y).hom ^ m = 1 ∧
    (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.x).hom ≫
        (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.y).hom =
      (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.y).hom ≫
        (labelTranslation k (2*m) D₂ X₂ x₂ D₂.atlas.marking.x).hom :=
  ⟨labelTranslation_order k (2*m) D₂ X₂ x₂ m _ D₂.atlas.marking.killed_x,
   labelTranslation_order k (2*m) D₂ X₂ x₂ m _ D₂.atlas.marking.killed_y,
   labelTranslations_commute k (2*m) D₂ X₂ x₂ _ _⟩

lemma full_doubled_labels_tate :
    (V.level.law.nsmul (𝟙 _) 2 V.level.marking.x).val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ (doubledLabel k L D X x D.atlas.marking.x).val ∧
    (V.level.law.nsmul (𝟙 _) 2 V.level.marking.y).val ≫ tateMap k L D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ (doubledLabel k L D X x D.atlas.marking.y).val :=
  ⟨doubledLabel_tate k L D X x V θ hb _ _ V.classifies.2.2.2.1,
   doubledLabel_tate k L D X x V θ hb _ _ V.classifies.2.2.2.2⟩

#print axioms full_level_translations
#print axioms full_doubled_labels_tate

#print axioms doubledLabel_killed
#print axioms labelTranslation_order
#print axioms labelTranslations_commute
#print axioms translation_tate
#print axioms labelTranslation_tate
#print axioms tateMap_mul
#print axioms tateMap_nsmul
#print axioms doubledLabel_tate
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

/-- The actual sheaf lift over the arithmetic field, without an existence claim. -/
abbrev LabelThetaLift (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :=
  (Scheme.Modules.pullback (labelTranslation k L D X x P).hom).obj
    (thetaLine k L D X x m) ≅ thetaLine k L D X x m

/-- The corresponding lift on the specified Tate cubic and its actual theta line. -/
abbrev TateLabelThetaLift (m : ℕ)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))) :=
  (Scheme.Modules.pullback
    (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.level.law
      (V.level.law.nsmul (𝟙 _) 2 Q))).obj (tateThetaLine k L m) ≅ tateThetaLine k L m

/-- Pullback coherence for the actual translated line and its Tate comparison. -/
def translatedThetaLine_tateIso (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val) :
    (Scheme.Modules.pullback (tateMap k L D X x V θ hb)).obj
      ((Scheme.Modules.pullback (labelTranslation k L D X x P).hom).obj
        (thetaLine k L D X x m)) ≅
    (Scheme.Modules.pullback
      (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.level.law
        (V.level.law.nsmul (𝟙 _) 2 Q))).obj (tateThetaLine k L m) :=
  (Scheme.Modules.pullbackComp (tateMap k L D X x V θ hb)
      (labelTranslation k L D X x P).hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr (labelTranslation_tate k L D X x V θ hb P Q hQ).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ (tateMap k L D X x V θ hb)).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (thetaLine_tateIso k L D X x V θ hb m)

include hb in
/-- A Tate sheaf lift descends to an arithmetic sheaf lift. This is descent of
isomorphism existence; it does not assert that an arbitrary normalized Tate
lift is itself the pullback of an arithmetic lift. -/
lemma labelThetaLift_iff_tate (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val) :
    Nonempty (LabelThetaLift k L D X x m P) ↔
      Nonempty (TateLabelThetaLift k L D X V m Q) := by
  let e := thetaLine_tateIso k L D X x V θ hb m
  let et := translatedThetaLine_tateIso k L D X x V θ hb m P Q hQ
  constructor
  · rintro ⟨α⟩
    exact ⟨et.symm ≪≫ (Scheme.Modules.pullback (tateMap k L D X x V θ hb)).mapIso α ≪≫ e⟩
  · rintro ⟨β⟩
    exact Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback
      (Component k L D X x).functionField (structureMap k L D X x)
      (geometry k L D X x) _ _
      ((thetaLine_invertible k L D X x m).pullback (labelTranslation k L D X x P).hom)
      (thetaLine_invertible k L D X x m)
      (LaurentSeries k) θ
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
      (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
      ⟨et ≪≫ β ≪≫ e.symm⟩

#print axioms translatedThetaLine_tateIso
#print axioms labelThetaLift_iff_tate
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Reflect an actual sheaf isomorphism through a scheme isomorphism. -/
def reflectIso {Y Z : Scheme} (e : Y ≅ Z) (M N : Z.Modules)
    (α : (Scheme.Modules.pullback e.hom).obj M ≅ (Scheme.Modules.pullback e.hom).obj N) : M ≅ N := by
  let c (P : Z.Modules) : P ≅
      (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj P) :=
    ((Scheme.Modules.pullbackId Z).app P).symm ≪≫
      ((Scheme.Modules.pullbackCongr e.inv_hom_id).app P).symm ≪≫
      ((Scheme.Modules.pullbackComp e.inv e.hom).app P).symm
  exact c M ≪≫ (Scheme.Modules.pullback e.inv).mapIso α ≪≫ (c N).symm

/-- Transport an actual ideal-line lift through an equivariant scheme isomorphism. -/
def transportLift {Y Z : Scheme} (e : Y ≅ Z) (f : Y ⟶ Y) (g : Z ⟶ Z)
    (h : f ≫ e.hom = e.hom ≫ g) (M : Y.Modules) (N : Z.Modules)
    (c : (Scheme.Modules.pullback e.hom).obj N ≅ M)
    (α : M ≅ (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullback g).obj N ≅ N :=
  reflectIso e _ _
    ((Scheme.Modules.pullbackComp e.hom g).app N ≪≫
      (Scheme.Modules.pullbackCongr h.symm).app N ≪≫
      ((Scheme.Modules.pullbackComp f e.hom).app N).symm ≪≫
      (Scheme.Modules.pullback f).mapIso c ≪≫ α.symm ≪≫ c.symm)

/-- Dualizing an ideal lift gives the associated positive-divisor line lift. -/
def dualLift {Y : Scheme} (f : Y ⟶ Y) (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M) ≅ Scheme.Modules.dual M := by
  letI := dualComparison_isIso f M hM
  exact asIso (dualComparison f M) ≪≫
    ((MonoidalClosed.internalHom (C := Y.Modules)).mapIso α.symm.op).app (𝟙_ Y.Modules)

/-- Tensoring by the actual pulled-back Hodge line preserves a translation lift. -/
def tensorBaseLift {Y B : Scheme} (p : Y ⟶ B) (f : Y ⟶ Y) (hf : f ≫ p = p)
    (M : Y.Modules) (H : B.Modules)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) :
    (Scheme.Modules.pullback f).obj (M ⊗ (Scheme.Modules.pullback p).obj H) ≅
      M ⊗ (Scheme.Modules.pullback p).obj H :=
  Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    (α ⊗ᵢ ((Scheme.Modules.pullbackComp f p).app H ≪≫
      (Scheme.Modules.pullbackCongr hf).app H))

#print axioms transportLift
#print axioms dualLift
#print axioms tensorBaseLift
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

variable (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (E : genericScheme k M ≅ ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r))
    (hO : genericPoint k M s hs.1 ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (hI : (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker.IsInvertible)

def modelPowerComparison (d : ℕ) :
    (Scheme.Modules.pullback E.hom).obj
      (((ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker^d).module) ≅
      genericPower k M s d := by
  let pT := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r)
  let oT := ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)
  letI : IsProper pT := WeierstrassProjModel.projModelStrCR_isProper (TateCurve k r).toProjective
  have hoT : oT ≫ pT = 𝟙 _ := (WeierstrassProjModel.kwZeroSect _ (TateCurve k r)).property
  letI : IsClosedImmersion (oT ≫ pT) := by rw [hoT]; infer_instance
  letI : IsClosedImmersion oT := IsClosedImmersion.of_comp oT pT
  have hk : (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker.comap E.hom =
      (genericPoint k M s hs.1).ker :=
    ker_baseChange (IsPullback.of_vert_isIso
      (show CommSq (genericPoint k M s hs.1) (𝟙 _) E.hom
        (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)) from
        ⟨by rw [hO, Category.id_comp]⟩))
  exact idealPullbackIso E.hom _ _ (hI.pow d)
      (generic_power_invertible k h3 M hM s hs d)
      (by rw [comap_power, hk]) ≪≫ (genericIdealIso k h3 M hM s hs d).symm

/-- The accepted local ideal lift transports to the full Hodge-twisted line on
the actual Tate cubic whenever the underlying translations match. -/
def modelThetaLift (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M)
    (g : ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r) ⟶
      ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r))
    (hfg : f ≫ E.hom = E.hom ≫ g)
    (hg : g ≫ ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r) =
      ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r))
    (α : ArithmeticThetaGeometricLiftsR0141.Lift k M s d f) :
    (Scheme.Modules.pullback g).obj (tateThetaLine k r d) ≅ tateThetaLine k r d :=
  tensorBaseLift _ g hg _ _ (dualLift g _ (hI.pow d).isInvertible_module
    (transportLift E f g hfg _ _ (modelPowerComparison k h3 M hM s hs E hO hI d) α))

#print axioms modelPowerComparison
#print axioms modelThetaLift
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw

variable (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (V : TateLevel k r)
    (E : genericScheme k M ≅ ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)

lemma model_translation (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (Q : SchemeHomOver (𝟙 _) (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r)))
    (hQ : genericPoint k M p hp ≫ E.hom = Q.val)
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : IsTranslation k M (transport E hE V.law) p hp f) :
    f ≫ E.hom = E.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law Q := by
  have h := hf (genericStructure k M) WeierstrassProjModel.RelativeGroupLaw.idPoint
  rw [Category.id_comp] at h
  rw [← h]
  change ((V.law.mul (genericStructure k M)
    ((pointsEquiv E hE _).toFun WeierstrassProjModel.RelativeGroupLaw.idPoint)
    ((pointsEquiv E hE _).toFun (pointOver k M _ p hp))).val ≫ E.inv) ≫ E.hom = _
  rw [Category.assoc, E.inv_hom_id, Category.comp_id]
  have h₁ : (pointsEquiv E hE _).toFun WeierstrassProjModel.RelativeGroupLaw.idPoint =
      (⟨E.hom, hE⟩ : SchemeHomOver (genericStructure k M)
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r))) := by
    apply Subtype.ext
    exact Category.id_comp _
  have h₂ : (pointsEquiv E hE _).toFun (pointOver k M (genericStructure k M) p hp) =
      WeierstrassProjModel.schemeHomOverComp (genericStructure k M) (Category.comp_id _) Q := by
    apply Subtype.ext
    change ((genericStructure k M) ≫ genericPoint k M p hp) ≫ E.hom = (genericStructure k M) ≫ Q.val
    rw [Category.assoc, hQ]
  exact (congrArg Subtype.val (congrArg₂ (V.law.mul (genericStructure k M)) h₁ h₂)).trans
    (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.comp_shift V.law Q
      (genericStructure k M) ⟨E.hom, hE⟩).symm

#print axioms model_translation
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182

/-- The scalar-direction translation of the prescribed canonical full 2m
marking has an actual sheaf lift on the entire Tate cubic. -/
lemma tate_scalarLift (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
    (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) V)
    (hI : (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k (2*m))).ker.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback
      (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
        (V.law.nsmul (𝟙 _) 2 V.marking.x))).obj (tateThetaLine k (2*m) m) ≅
      tateThetaLine k (2*m) m) := by
  have hpos : 0 < 2*m := Nat.mul_pos (by decide) hm
  have h3 : 3 ≤ 2*m := thetaChartBound m hm he
  have he₂ : Even (2*m) := even_two_mul m
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k (2*m) h3 hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM (zeroIndex (2*m) hpos) 1
  obtain ⟨rot, scal, inv, ha⟩ := algebraized_annular_actions k (2*m) hpos h3 T M hM
  obtain ⟨E, hE, hO, hcoords⟩ := CubicComparison.canonical_model_iso k (2*m) hpos h3 he₂ T M hM s hs V ζ hζ hmark
  let G := transport E hE V.law
  have hG : IsOriginLaw k M s hs.1 G := CubicComparison.transported_origin k M s hs.1 V E hE hO
  obtain ⟨p, hp, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM (zeroIndex (2*m) hpos) (ζ^2)
  let q := V.law.nsmul (𝟙 _) 2 V.marking.x
  have hpq : genericPoint k M p hp.1 ≫ E.hom = q.val := by
    have h := hcoords ⟨2, by omega⟩ (zeroIndex (2*m) hpos) p hp
    simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint, zeroIndex,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, V.law.mul_one] using h
  have hf : IsTranslation k M G p hp.1 (scalarMap k M rot scal inv ha (ζ^2)) :=
    actual_scalar_translation k (2*m) hpos h3 T he₂ M hM s hs G hG rot scal inv ha (ζ^2) p hp
  have hfE := model_translation k M V E hE p hp.1 q hpq _ hf
  have hζm : IsPrimitiveRoot ((ζ^2 : kˣ) : k) m := by
    simpa only [Units.val_pow_eq_pow_val] using IsPrimitiveRoot.pow hpos hζ (rfl : 2*m = 2*m)
  obtain ⟨α, _, _⟩ := geometric_scalar_lift k m hm he T M hM s hs rot scal inv ha (ζ^2) hζm
  exact ⟨modelThetaLift k h3 M hM s hs E hO hI m _ _ hfE
    (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift_over V.law q) α⟩

/-- The second Tate direction has an actual lift, obtained from the accepted
period-shift lift and the same canonical full-level comparison. -/
lemma tate_shiftLift (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
    (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) V)
    (hI : (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k (2*m))).ker.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback
      (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
        (V.law.nsmul (𝟙 _) 2 V.marking.y))).obj (tateThetaLine k (2*m) m) ≅
      tateThetaLine k (2*m) m) := by
  have hpos : 0 < 2*m := Nat.mul_pos (by decide) hm
  have h3 : 3 ≤ 2*m := thetaChartBound m hm he
  have he₂ : Even (2*m) := even_two_mul m
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k (2*m) h3 hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM (zeroIndex (2*m) hpos) 1
  obtain ⟨rot, scal, inv, ha⟩ := algebraized_annular_actions k (2*m) hpos h3 T M hM
  obtain ⟨E, hE, hO, hcoords⟩ := CubicComparison.canonical_model_iso k (2*m) hpos h3 he₂ T M hM s hs V ζ hζ hmark
  let G := transport E hE V.law
  have hG : IsOriginLaw k M s hs.1 G := CubicComparison.transported_origin k M s hs.1 V E hE hO
  let j := next (2*m) hpos (zeroIndex (2*m) hpos)
  obtain ⟨p, hp, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM j 1
  have hj : j.val = 1 := by
    change (0+1) % (2*m) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hpq : genericPoint k M p hp.1 ≫ E.hom = V.marking.y.val := by
    have hp' : MarkedLift k M j (ζ^(zeroIndex (2*m) hpos).val) p := by
      simpa only [zeroIndex, pow_zero] using hp
    have h := hcoords (zeroIndex (2*m) hpos) j p hp'
    simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint, zeroIndex, hj,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply, V.law.one_mul] using h
  have hf : IsTranslation k M G p hp.1 (rotationMap k M rot scal inv ha) :=
    actual_rotation_translation k (2*m) hpos h3 T he₂ M hM s hs G hG rot scal inv ha p hp
  have hfE := model_translation k M V E hE p hp.1 V.marking.y hpq _ hf
  have hdouble : V.law.nsmul (𝟙 _) 2 V.marking.y =
      V.law.mul (𝟙 _) V.marking.y V.marking.y := by
    rw [V.law.nsmul_succ, V.law.nsmul_one_apply]
  have hfE₂ : shiftMap k M rot scal inv ha ≫ E.hom = E.hom ≫
      ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
        (V.law.nsmul (𝟙 _) 2 V.marking.y) := by
    change (rotationMap k M rot scal inv ha ≫ rotationMap k M rot scal inv ha) ≫ E.hom = _
    rw [Category.assoc, hfE, ← Category.assoc, hfE, Category.assoc,
      ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift_comp, hdouble]
  obtain ⟨α, _, _⟩ := geometric_shift_lift k m hm he T M hM s hs rot scal inv ha
  exact ⟨modelThetaLift k h3 M hM s hs E hO hI m _ _ hfE₂
    (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift_over V.law _) α⟩

#print axioms tate_shiftLift

#print axioms tate_scalarLift
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181

/-- Both prescribed m-level translations have actual line lifts over the
original function field. No cover, parameter root, or assumed theta structure
enters this existence theorem. Symmetric/order normalization is still separate. -/
lemma full_level_theta_lifts (k : Type) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X) (ζ : k) (hζ : IsPrimitiveRoot ζ (2*m))
    (hmark : CanonicalMarking k (2*m) ζ V.level)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base) :
    Nonempty (LabelThetaLift k (2*m) D X x m D.atlas.marking.x) ∧
      Nonempty (LabelThetaLift k (2*m) D X x m D.atlas.marking.y) := by
  have hpos : 0 < 2*m := Nat.mul_pos (by decide) hm
  let z : kˣ := (hζ.isUnit hpos.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hpos.ne').unit_spec
  have hzr : IsPrimitiveRoot (z : k) (2*m) := by simpa only [hz] using hζ
  have hzm : CanonicalMarking k (2*m) (z : k) V.level := by simpa only [hz] using hmark
  have hI := tateOrigin_cartier k (2*m) D X x V θ hb
  exact ⟨(labelThetaLift_iff_tate k (2*m) D X x V θ hb m _ _ V.classifies.2.2.2.1).mpr
      (LocalTheta.tate_scalarLift k m hm he V.level z hzr hzm hI),
    (labelThetaLift_iff_tate k (2*m) D X x V θ hb m _ _ V.classifies.2.2.2.2).mpr
      (LocalTheta.tate_shiftLift k m hm he V.level z hzr hzm hI)⟩

#print axioms full_level_theta_lifts
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181

/-- Existence of the actual arithmetic lifts under only the original field,
level and canonical-branch hypotheses. The geometric field embedding is
constructed from that branch inside the proof. -/
lemma component_theta_lifts (k : Type) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
    (V : DiskTest k (2*m) D X) (ζ : k) (hζ : IsPrimitiveRoot ζ (2*m))
    (hmark : CanonicalMarking k (2*m) ζ V.level) :
    Nonempty (LabelThetaLift k (2*m) D X (V.disk (closedPoint k)) m D.atlas.marking.x) ∧
      Nonempty (LabelThetaLift k (2*m) D X (V.disk (closedPoint k)) m D.atlas.marking.y) := by
  obtain ⟨f, θ, hfac, _, hθ⟩ := component_field_factor k (2*m) D X V
  have hb := (component_field_map_over k (2*m) D X V f hfac θ hθ).2
  exact full_level_theta_lifts k m hm he D X (V.disk (closedPoint k)) V ζ hζ hmark θ hb

#print axioms component_theta_lifts
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184

namespace Midpoint
variable {F : Type} [Field F] {Y : Scheme} {p : Y ⟶ Spec (CommRingCat.of F)}
    (G : RelativeGroupLaw F p)

/-- Translation by twice b and inversion agree at -b. -/
lemma translate_double (b : SchemeHomOver (𝟙 _) p) :
    (G.inv (𝟙 _) b).val ≫ G.translate (G.nsmul (𝟙 _) 2 b) =
      (G.inv (𝟙 _) b).val ≫ GroupInversion.morphism G := by
  let a := G.inv (𝟙 _) b
  have hn := GroupInversion.inverse_natural G p (𝟙 _) a.val a.property
    (⟨𝟙 Y, Category.id_comp p⟩ : SchemeHomOver p p)
  have ha : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨𝟙 Y, Category.id_comp p⟩ : SchemeHomOver p p) = a := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha] at hn
  have hInv : a.val ≫ GroupInversion.morphism G = b.val := by
    have he : G.inv (𝟙 _) a = b := by
      letI := G.pointGroup (𝟙 _)
      exact inv_inv b
    exact congrArg Subtype.val (hn.trans he)
  rw [hInv, GroupTranslation.point_translate]
  have hid : (⟨𝟙 _ ≫ (G.nsmul (𝟙 _) 2 b).val, by
      rw [Category.assoc, (G.nsmul (𝟙 _) 2 b).property, Category.comp_id]⟩ :
      SchemeHomOver (𝟙 _) p) = G.nsmul (𝟙 _) 2 b := by
    apply Subtype.ext
    exact Category.id_comp _
  rw [hid]
  letI := G.pointGroup (𝟙 _)
  rw [GroupTranslation.nsmul_eq_pow]
  change (b⁻¹ * b^2).val = b.val
  rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Over a field, a prescribed isomorphism at one rational fibre determines
exactly one isomorphism of two already-isomorphic invertible sheaves. -/
lemma existsUnique_fibreIso
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom)
    (e : SchemeHomOver (𝟙 _) p) (M N : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (c : (Scheme.Modules.pullback e.val).obj M ≅ (Scheme.Modules.pullback e.val).obj N)
    (h : Nonempty (M ≅ N)) :
    ∃! α : M ≅ N, (Scheme.Modules.pullback e.val).mapIso α = c := by
  obtain ⟨α₀⟩ := h
  obtain ⟨β⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    F _ (hN.pullback e.val)
  obtain ⟨α, hα⟩ := Polarisation.nonempty_rigidifiedIso_of_iso p hΓ e.val e.property M N (c ≪≫ β) β α₀
  haveI := Polarisation.subsingleton_rigidifiedIso p hΓ e.val e.property M N hM (c ≪≫ β) β
  refine ⟨α, ?_, fun γ hγ => ?_⟩
  · apply Iso.ext
    exact (cancel_mono β.hom).mp (congrArg Iso.hom hα)
  · exact congrArg Subtype.val (Subsingleton.elim
      (⟨γ, by rw [hγ]⟩ : {φ : M ≅ N // (Scheme.Modules.pullback e.val).mapIso φ ≪≫ β = c ≪≫ β})
      ⟨α, hα⟩)
end Midpoint

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- Fibre comparison between the doubled-label translation and the uniquely
conormal-normalized inversion at the negative full-level label. -/
def midpointComparison (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    let a := ((groupLaw k L D X x).inv (𝟙 _) (labelPoint k L D X x P)).val
    (Scheme.Modules.pullback a).obj
      ((Scheme.Modules.pullback (labelTranslation k L D X x P).hom).obj (thetaLine k L D X x m)) ≅
      (Scheme.Modules.pullback a).obj (thetaLine k L D X x m) := by
  let a := ((groupLaw k L D X x).inv (𝟙 _) (labelPoint k L D X x P)).val
  exact (Scheme.Modules.pullbackComp a (labelTranslation k L D X x P).hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Midpoint.translate_double (groupLaw k L D X x)
      (labelPoint k L D X x P))).app _ ≪≫
    ((Scheme.Modules.pullbackComp a (inverseIso k L D X x).hom).app _).symm ≪≫
    (Scheme.Modules.pullback a).mapIso (normalizedInversion k L D X x m hm)

lemma existsUnique_midpointLift (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hlift : Nonempty (LabelThetaLift k L D X x m P)) :
    ∃! α : LabelThetaLift k L D X x m P,
      (Scheme.Modules.pullback ((groupLaw k L D X x).inv (𝟙 _) (labelPoint k L D X x P)).val).mapIso α =
        midpointComparison k L D X x m hm P :=
  Midpoint.existsUnique_fibreIso (constants_bijective k L D X x)
    ((groupLaw k L D X x).inv (𝟙 _) (labelPoint k L D X x P)) _ _
    ((thetaLine_invertible k L D X x m).pullback _) (thetaLine_invertible k L D X x m)
    (midpointComparison k L D X x m hm P) hlift

open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181

/-- Midpoint-normalized arithmetic lifts exist and are unique under the original
full-level branch hypotheses; symmetry of these lifts is a further theorem. -/
lemma component_midpoint_lifts (m : ℕ) (hm : 0 < m) (he : Even m)
    (D₂ : LevelData k (2*m)) (X₂ : Compactification k (2*m) D₂)
    (V : DiskTest k (2*m) D₂ X₂) (ζ : k) (hζ : IsPrimitiveRoot ζ (2*m))
    (hmark : CanonicalMarking k (2*m) ζ V.level) :
    (∃! α : LabelThetaLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m D₂.atlas.marking.x,
      (Scheme.Modules.pullback ((groupLaw k (2*m) D₂ X₂ (V.disk (closedPoint k))).inv (𝟙 _)
        (labelPoint k (2*m) D₂ X₂ (V.disk (closedPoint k)) D₂.atlas.marking.x)).val).mapIso α =
          midpointComparison k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm D₂.atlas.marking.x) ∧
    (∃! β : LabelThetaLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m D₂.atlas.marking.y,
      (Scheme.Modules.pullback ((groupLaw k (2*m) D₂ X₂ (V.disk (closedPoint k))).inv (𝟙 _)
        (labelPoint k (2*m) D₂ X₂ (V.disk (closedPoint k)) D₂.atlas.marking.y)).val).mapIso β =
          midpointComparison k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm D₂.atlas.marking.y) := by
  obtain ⟨ha, hb⟩ := component_theta_lifts k m hm he D₂ X₂ V ζ hζ hmark
  exact ⟨existsUnique_midpointLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm _ ha,
    existsUnique_midpointLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm _ hb⟩

#print axioms component_midpoint_lifts

#print axioms Midpoint.translate_double
#print axioms Midpoint.existsUnique_fibreIso
#print axioms midpointComparison
#print axioms existsUnique_midpointLift
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
namespace Midpoint
variable {F : Type} [Field F] {Y : Scheme} {p : Y ⟶ Spec (CommRingCat.of F)}
    (G : RelativeGroupLaw F p)

lemma point_inverse {T : Scheme} (t : T ⟶ Spec (CommRingCat.of F))
    (a : SchemeHomOver t p) :
    a.val ≫ GroupInversion.morphism G = (G.inv t a).val := by
  have h := GroupInversion.inverse_natural G p t a.val a.property
    (⟨𝟙 Y, Category.id_comp p⟩ : SchemeHomOver p p)
  have ha : schemeHomOverComp a.val a.property
      (⟨𝟙 Y, Category.id_comp p⟩ : SchemeHomOver p p) = a := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha] at h
  exact congrArg Subtype.val h

/-- Inversion followed after translation by a. -/
def reflection (a : SchemeHomOver (𝟙 _) p) : Y ⟶ Y :=
  G.translate a ≫ GroupInversion.morphism G

lemma reflection_square (hc : G.IsCommutative) (a : SchemeHomOver (𝟙 _) p) :
    reflection G a ≫ reflection G a = 𝟙 Y := by
  let ca : SchemeHomOver p p := ⟨p ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let i : SchemeHomOver p p := ⟨𝟙 Y, Category.id_comp p⟩
  let b := G.inv p (G.mul p i ca)
  have h₁ : reflection G a = b.val := point_inverse G p (G.mul p i ca)
  have h₂ : b.val ≫ G.translate a = (G.mul p b ca).val :=
    GroupTranslation.point_translate G p b a
  conv_lhs => lhs; rw [h₁]
  change b.val ≫ (G.translate a ≫ GroupInversion.morphism G) = _
  rw [← Category.assoc, h₂, point_inverse]
  change (G.inv p (G.mul p (G.inv p (G.mul p i ca)) ca)).val = i.val
  congr 1
  letI := G.pointGroup p
  have hcomm (u v : SchemeHomOver p p) : u * v = v * u := hc.mul_comm p u v
  change ((i * ca)⁻¹ * ca)⁻¹ = i
  rw [mul_inv_rev, inv_inv, hcomm i ca, ← mul_assoc, inv_mul_cancel, one_mul]

lemma reflection_fixed (b : SchemeHomOver (𝟙 _) p) :
    (G.inv (𝟙 _) b).val ≫ reflection G (G.nsmul (𝟙 _) 2 b) =
      (G.inv (𝟙 _) b).val := by
  rw [reflection, ← Category.assoc, translate_double, Category.assoc,
    GroupInversion.square, Category.comp_id]

/-- A lift of an involution can be uniquely normalized to act identically at
one rational fixed point, and the resulting sheaf lift squares to identity. -/
lemma normalized_reflection_exists
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom)
    (e : SchemeHomOver (𝟙 _) p) (g : Y ⟶ Y) (he : e.val ≫ g = e.val)
    (hg : g ≫ g = 𝟙 Y) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hlift : Nonempty ((Scheme.Modules.pullback g).obj M ≅ M)) :
    ∃ φ : (Scheme.Modules.pullback g).obj M ≅ M,
      (Scheme.Modules.pullback e.val).mapIso φ =
        (FixedPointPullback.compare e.val g e.val he).app M ∧
      (Scheme.Modules.pullback g).mapIso φ ≪≫ φ =
        FixedPointPullback.squareComparison g hg M := by
  obtain ⟨φ, hφ, _⟩ := existsUnique_fibreIso hΓ e _ _ (hM.pullback g) hM
    ((FixedPointPullback.compare e.val g e.val he).app M) hlift
  refine ⟨φ, hφ, ?_⟩
  apply FixedPointPullback.square_of_rigidified e.val g he hg M _ (Iso.refl _) φ
  · simp only [hφ, FixedPointPullback.compare, NatIso.trans_app, Iso.trans_refl]
  · intro ψ hψ
    obtain ⟨_, _, hu⟩ := existsUnique_fibreIso hΓ e M M hM hM
      (Iso.refl _) ⟨Iso.refl _⟩
    have hψ' : (Scheme.Modules.pullback e.val).mapIso ψ = Iso.refl _ := by
      simpa only [Iso.trans_refl] using hψ
    exact (hu ψ hψ').trans (hu (Iso.refl _) (by simp)).symm

#print axioms point_inverse
#print axioms reflection_square
#print axioms reflection_fixed
#print axioms normalized_reflection_exists
/-- Composition of genuine line lifts, with the geometric pullback comparison. -/
def composeLift (f g : Y ⟶ Y) (M : Y.Modules)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ M :=
  ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ α

/-- A symmetric arithmetic translation lift exists using the given midpoint.
The square identity is an equality of sheaf isomorphisms, with all canonical
pullback comparisons, rather than an assumed relation on an abstract space. -/
lemma symmetric_translation_lift
    (hc : G.IsCommutative)
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom)
    (b : SchemeHomOver (𝟙 _) p) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ι : (Scheme.Modules.pullback (GroupInversion.morphism G)).obj M ≅ M)
    (hlift : Nonempty ((Scheme.Modules.pullback (G.translate (G.nsmul (𝟙 _) 2 b))).obj M ≅ M)) :
    ∃ α : (Scheme.Modules.pullback (G.translate (G.nsmul (𝟙 _) 2 b))).obj M ≅ M,
      let g := reflection G (G.nsmul (𝟙 _) 2 b)
      let φ := composeLift (G.translate (G.nsmul (𝟙 _) 2 b)) (GroupInversion.morphism G) M α ι
      (Scheme.Modules.pullback (G.inv (𝟙 _) b).val).mapIso φ =
        (FixedPointPullback.compare (G.inv (𝟙 _) b).val g (G.inv (𝟙 _) b).val
          (reflection_fixed G b)).app M ∧
      (Scheme.Modules.pullback g).mapIso φ ≪≫ φ =
        FixedPointPullback.squareComparison g (reflection_square G hc _) M := by
  obtain ⟨α₀⟩ := hlift
  let t := G.translate (G.nsmul (𝟙 _) 2 b)
  let n := GroupInversion.morphism G
  let g := reflection G (G.nsmul (𝟙 _) 2 b)
  obtain ⟨φ, hφ, hsq⟩ := normalized_reflection_exists hΓ (G.inv (𝟙 _) b) g
    (reflection_fixed G b) (reflection_square G hc _) M hM
    ⟨composeLift t n M α₀ ι⟩
  let α := ((Scheme.Modules.pullback t).mapIso ι).symm ≪≫
    (Scheme.Modules.pullbackComp t n).app M ≪≫ φ
  have hα : composeLift t n M α ι = φ := by
    apply Iso.ext
    simp [composeLift, α]
  refine ⟨α, ?_⟩
  change (Scheme.Modules.pullback (G.inv (𝟙 _) b).val).mapIso (composeLift t n M α ι) = _ ∧
    (Scheme.Modules.pullback g).mapIso (composeLift t n M α ι) ≪≫ composeLift t n M α ι = _
  rw [hα]
  exact ⟨hφ, hsq⟩

#print axioms composeLift
#print axioms symmetric_translation_lift
end Midpoint

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- Actual sheaf symmetry relative to the conormal-normalized inversion.
The composite lift above translation followed by inversion squares to the
canonical identity comparison, including its double-pullback isomorphism. -/
def LabelLiftSymmetry (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (α : LabelThetaLift k L D X x m P) : Prop :=
  let G := groupLaw k L D X x
  let g := Midpoint.reflection G (doubledLabel k L D X x P)
  let φ := Midpoint.composeLift (labelTranslation k L D X x P).hom
    (inverseIso k L D X x).hom (thetaLine k L D X x m) α
    (normalizedInversion k L D X x m hm)
  (Scheme.Modules.pullback g).mapIso φ ≪≫ φ =
    FixedPointPullback.squareComparison g
      (Midpoint.reflection_square G (groupLaw_commutative k L D X x) _) _

lemma exists_symmetric_labelLift (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (hlift : Nonempty (LabelThetaLift k L D X x m P)) :
    ∃ α : LabelThetaLift k L D X x m P, LabelLiftSymmetry k L D X x m hm P α := by
  obtain ⟨α, _, hα⟩ := Midpoint.symmetric_translation_lift (groupLaw k L D X x)
    (groupLaw_commutative k L D X x) (constants_bijective k L D X x)
    (labelPoint k L D X x P) (thetaLine k L D X x m)
    (thetaLine_invertible k L D X x m) (normalizedInversion k L D X x m hm) hlift
  exact ⟨α, hα⟩

open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181

/-- Both arithmetic line lifts satisfy the actual sheaf symmetry identity.
Only the original full-level and canonical-branch hypotheses are used. -/
lemma component_symmetric_lifts (m : ℕ) (hm : 0 < m) (he : Even m)
    (D₂ : LevelData k (2*m)) (X₂ : Compactification k (2*m) D₂)
    (V : DiskTest k (2*m) D₂ X₂) (ζ : k) (hζ : IsPrimitiveRoot ζ (2*m))
    (hmark : CanonicalMarking k (2*m) ζ V.level) :
    (∃ α : LabelThetaLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m D₂.atlas.marking.x,
      LabelLiftSymmetry k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm D₂.atlas.marking.x α) ∧
    (∃ β : LabelThetaLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m D₂.atlas.marking.y,
      LabelLiftSymmetry k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm D₂.atlas.marking.y β) := by
  obtain ⟨ha, hb⟩ := component_theta_lifts k m hm he D₂ X₂ V ζ hζ hmark
  exact ⟨exists_symmetric_labelLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm _ ha,
    exists_symmetric_labelLift k (2*m) D₂ X₂ (V.disk (closedPoint k)) m hm _ hb⟩

#print axioms exists_symmetric_labelLift
#print axioms component_symmetric_lifts
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

variable {X Y Z : Scheme}

def unitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  letI := unitPullback_isIso f
  exact asIso (unitPullback f)

def pull (f : X ⟶ Y) {M : Y.Modules}
    (s : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ (Scheme.Modules.pullback f).obj M :=
  (unitIso f).inv ≫ (Scheme.Modules.pullback f).map s

lemma pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (s : (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶ M) :
    pull f (pull g s) ≫ (Scheme.Modules.pullbackComp f g).hom.app M = pull (f ≫ g) s := by
  apply (cancel_epi (unitIso f).hom).mp
  apply (cancel_epi ((Scheme.Modules.pullback f).map (unitIso g).hom)).mp
  simp only [pull, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (unitIso f).hom, Iso.hom_inv_id, Category.id_comp]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (unitIso g).hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).map s ≫ _ =
    (Scheme.Modules.pullback f).map (unitPullback g) ≫ unitPullback f ≫ _
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (unitPullback g)),
    ← unitPullback_comp_hom f g]
  rw [Category.assoc, ← Category.assoc (unitPullback (f ≫ g)),
    show unitPullback (f ≫ g) ≫ (unitIso (f ≫ g)).inv = 𝟙 _ from (unitIso _).hom_inv_id,
    Category.id_comp]
  exact (Scheme.Modules.pullbackComp f g).hom.naturality s

lemma pull_post (f : X ⟶ Y) {M N : Y.Modules}
    (s : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) (u : M ⟶ N) :
    pull f (s ≫ u) = pull f s ≫ (Scheme.Modules.pullback f).map u := by
  simp [pull]

lemma pull_id {M : X.Modules}
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    pull (𝟙 X) s ≫ (Scheme.Modules.pullbackId X).hom.app M = s := by
  apply (cancel_epi (unitIso (𝟙 X)).hom).mp
  rw [← Category.assoc, show (unitIso (𝟙 X)).hom ≫ pull (𝟙 X) s =
    (Scheme.Modules.pullback (𝟙 X)).map s by simp [pull]]
  change (Scheme.Modules.pullback (𝟙 X)).map s ≫ _ = unitPullback (𝟙 X) ≫ s
  rw [ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.RawIteration.unit_id]
  exact (Scheme.Modules.pullbackId X).hom.naturality s

lemma pull_congr {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (s : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) :
    pull f s ≫ (Scheme.Modules.pullbackCongr h).hom.app M = pull g s := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

def act (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) := pull f s ≫ α.hom

lemma act_comp (f g : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act f α (act g β s) = act (f ≫ g) (Midpoint.composeLift f g M α β) s := by
  simp only [act, pull_post, Midpoint.composeLift, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc]
  rw [← pull_comp f g s]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

lemma act_square (g : X ⟶ X) (hg : g ≫ g = 𝟙 X) {M : X.Modules}
    (α : (Scheme.Modules.pullback g).obj M ≅ M)
    (hα : (Scheme.Modules.pullback g).mapIso α ≪≫ α = FixedPointPullback.squareComparison g hg M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act g α (act g α s) = s := by
  change pull g (pull g s ≫ α.hom) ≫ α.hom = s
  rw [pull_post, Category.assoc]
  have hh := congrArg Iso.hom hα
  change (Scheme.Modules.pullback g).map α.hom ≫ α.hom = _ at hh
  rw [hh]
  simp only [FixedPointPullback.squareComparison, FixedPointPullback.compare,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, pull_comp, pull_congr, pull_id]

#print axioms pull_comp
#print axioms act_comp
#print axioms act_square

/-- A canonical sheaf square gives the alternating inversion-conjugacy
identity on every actual global section. -/
lemma act_alternating (f g : X ⟶ X) (hg : g ≫ g = 𝟙 X)
    (hfg : (f ≫ g) ≫ (f ≫ g) = 𝟙 X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (hβ : (Scheme.Modules.pullback g).mapIso β ≪≫ β =
      FixedPointPullback.squareComparison g hg M)
    (hα : (Scheme.Modules.pullback (f ≫ g)).mapIso (Midpoint.composeLift f g M α β) ≪≫
      Midpoint.composeLift f g M α β = FixedPointPullback.squareComparison (f ≫ g) hfg M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act g β (act f α (act g β (act f α s))) = s := by
  have hS := act_square g hg β hβ
  have hAS (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
      act f α (act g β (act f α (act g β s))) = s := by
    simpa only [← act_comp] using act_square (f ≫ g) hfg (Midpoint.composeLift f g M α β) hα s
  have h := congrArg (act g β) (hAS (act g β s))
  simpa only [hS] using h

#print axioms act_alternating
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

lemma labelLiftSymmetry_sections (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (α : LabelThetaLift k L D X x m P)
    (hα : LabelLiftSymmetry k L D X x m hm P α)
    (s : (SheafOfModules.unit (curve k L D X x).ringCatSheaf : (curve k L D X x).Modules) ⟶
      thetaLine k L D X x m) :
    let A := SectionAction.act (labelTranslation k L D X x P).hom α
    let S := SectionAction.act (inverseIso k L D X x).hom (normalizedInversion k L D X x m hm)
    S (A (S (A s))) = s :=
  SectionAction.act_alternating (labelTranslation k L D X x P).hom
    (inverseIso k L D X x).hom (GroupInversion.square (groupLaw k L D X x))
    (Midpoint.reflection_square (groupLaw k L D X x) (groupLaw_commutative k L D X x) _)
    α (normalizedInversion k L D X x m hm) (normalizedInversion_square k L D X x m hm) hα s

#print axioms labelLiftSymmetry_sections
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

lemma tateMap_one {T : Scheme} (t : T ⟶ Puncture k) :
    (V.level.law.one t).val ≫ tateMap k L D X x V θ hb =
      ((groupLaw k L D X x).one (t ≫ Spec.map (CommRingCat.ofHom θ))).val := by
  rw [V.level.originLaw.1, Category.assoc, tateMap_origin, ← Category.assoc, ← groupLaw_origin]
  exact congrArg Subtype.val ((groupLaw k L D X x).one_natural (𝟙 _)
    (t ≫ Spec.map (CommRingCat.ofHom θ)) (t ≫ Spec.map (CommRingCat.ofHom θ))
    (Category.comp_id _))

lemma tateMap_inv {T : Scheme} (t : T ⟶ Puncture k)
    (a : SchemeHomOver t
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))) :
    (V.level.law.inv t a).val ≫ tateMap k L D X x V θ hb =
      ((groupLaw k L D X x).inv (t ≫ Spec.map (CommRingCat.ofHom θ))
        ⟨a.val ≫ tateMap k L D X x V θ hb, by
          rw [Category.assoc, tateMap_structure, ← Category.assoc, a.property]⟩).val := by
  let G := groupLaw k L D X x
  let t' := t ≫ Spec.map (CommRingCat.ofHom θ)
  let ap : SchemeHomOver t' (structureMap k L D X x) :=
    ⟨a.val ≫ tateMap k L D X x V θ hb, by
      rw [Category.assoc, tateMap_structure, ← Category.assoc, a.property]⟩
  let bp : SchemeHomOver t' (structureMap k L D X x) :=
    ⟨(V.level.law.inv t a).val ≫ tateMap k L D X x V θ hb, by
      rw [Category.assoc, tateMap_structure, ← Category.assoc, (V.level.law.inv t a).property]⟩
  have hmul : G.mul t' bp ap = G.one t' := by
    apply Subtype.ext
    change _ = ((groupLaw k L D X x).one (t ≫ Spec.map (CommRingCat.ofHom θ))).val
    rw [← tateMap_mul, V.level.law.inv_mul_cancel, tateMap_one]
  letI := G.pointGroup t'
  exact congrArg Subtype.val (eq_inv_of_mul_eq_one_left hmul)

/-- The actual Tate inversion and arithmetic inversion commute with the
original Cartesian comparison, with no choice of a geometric conjugacy. -/
lemma tateMap_inverse :
    (V.level.law.inv
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
      WeierstrassProjModel.RelativeGroupLaw.idPoint).val ≫ tateMap k L D X x V θ hb =
      tateMap k L D X x V θ hb ≫ (inverseIso k L D X x).hom := by
  have h := tateMap_inv k L D X x V θ hb
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    WeierstrassProjModel.RelativeGroupLaw.idPoint
  simp only [WeierstrassProjModel.RelativeGroupLaw.idPoint, Category.id_comp] at h
  rw [h]
  exact (Midpoint.point_inverse (groupLaw k L D X x) _
    ⟨tateMap k L D X x V θ hb, tateMap_structure k L D X x V θ hb⟩).symm

#print axioms tateMap_one
#print axioms tateMap_inv
#print axioms tateMap_inverse
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141

lemma weierstrass_point_inverse {F : Type} [CommRing F] {Y : Scheme}
    {p : Y ⟶ Spec (CommRingCat.of F)} (G : WeierstrassProjModel.RelativeGroupLaw F p)
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of F)) (a : SchemeHomOver t p) :
    a.val ≫ (G.inv p WeierstrassProjModel.RelativeGroupLaw.idPoint).val = (G.inv t a).val := by
  let b := WeierstrassProjModel.schemeHomOverComp a.val a.property
    (G.inv p WeierstrassProjModel.RelativeGroupLaw.idPoint)
  have ha : WeierstrassProjModel.schemeHomOverComp a.val a.property
      WeierstrassProjModel.RelativeGroupLaw.idPoint = a := by
    apply Subtype.ext
    exact Category.comp_id _
  have hm : G.mul t b a = G.one t := by
    rw [← ha, ← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  letI := G.pointGroup t
  have hi : b = G.inv t a := eq_inv_of_mul_eq_one_left hm
  exact congrArg (fun q : SchemeHomOver t p => q.val) hi

variable (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (V : TateLevel k r)
    (E : genericScheme k M ≅ ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)

lemma model_inverse
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : ∀ {U : Scheme} (t : U ⟶ Puncture k) (a : SchemeHomOver t (genericStructure k M)),
      ((transport E hE V.law).inv t a).val = a.val ≫ f) :
    f ≫ E.hom = E.hom ≫ (V.law.inv
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r))
      WeierstrassProjModel.RelativeGroupLaw.idPoint).val := by
  have h := hf (genericStructure k M) WeierstrassProjModel.RelativeGroupLaw.idPoint
  rw [Category.id_comp] at h
  rw [← h]
  change ((V.law.inv (genericStructure k M)
    ((pointsEquiv E hE _).toFun WeierstrassProjModel.RelativeGroupLaw.idPoint)).val ≫ E.inv) ≫ E.hom = _
  rw [Category.assoc, E.inv_hom_id, Category.comp_id]
  have hi : (pointsEquiv E hE _).toFun WeierstrassProjModel.RelativeGroupLaw.idPoint =
      (⟨E.hom, hE⟩ : SchemeHomOver (genericStructure k M)
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r))) := by
    apply Subtype.ext
    exact Category.id_comp _
  exact (congrArg Subtype.val (congrArg (V.law.inv (genericStructure k M)) hi)).trans
    (weierstrass_point_inverse V.law (genericStructure k M) ⟨E.hom, hE⟩).symm

lemma model_inversionMap (h3 : 3 ≤ r) (he : Even r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (hG : IsOriginLaw k M s hs.1 (transport E hE V.law))
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    inversionMap k M rot scal iv ha ≫ E.hom = E.hom ≫ (V.law.inv
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r))
      WeierstrassProjModel.RelativeGroupLaw.idPoint).val :=
  model_inverse k M V E hE _ (fun {_} t a => actual_inverse_comparison
    k r hr h3 T he M hM s hs (transport E hE V.law) hG rot scal iv ha _ t a)

#print axioms weierstrass_point_inverse
#print axioms model_inverse
#print axioms model_inversionMap
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
variable {X Y : Scheme}

lemma squareIso_section (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {M : X.Modules}
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    pull g (pull c s) ≫ (squareIso f c c g h M).hom = pull c (pull f s) := by
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← Category.assoc, pull_comp, pull_congr, ← pull_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

def baseChangedLift (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj M) ≅
      (Scheme.Modules.pullback c).obj M :=
  squareIso f c c g h M ≪≫ (Scheme.Modules.pullback c).mapIso α

/-- The line-lift action commutes with pullback through its actual geometric
square, on every pulled section. -/
lemma baseChanged_act (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act g (baseChangedLift c f g h α) (pull c s) = pull c (act f α s) := by
  simp only [act, baseChangedLift, Iso.trans_hom, Functor.mapIso_hom, pull_post]
  rw [← Category.assoc, squareIso_section]

/-- Conjugation of a line lift by an actual sheaf isomorphism. -/
def changeLine (f : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) :
    (Scheme.Modules.pullback f).obj N ≅ N :=
  (Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e

lemma changeLine_act (f : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act f (changeLine f e α) (s ≫ e.hom) = act f α s ≫ e.hom := by
  simp only [act, changeLine, pull_post, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map e.hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

lemma baseChanged_alternating (c : Y ⟶ X) (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (h : ∀ s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M,
      act g β (act f α (act g β (act f α s))) = s)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    let A := act f' (baseChangedLift c f f' hf α)
    let S := act g' (baseChangedLift c g g' hg β)
    S (A (S (A (pull c s)))) = pull c s := by
  dsimp only
  rw [baseChanged_act, baseChanged_act, baseChanged_act, baseChanged_act, h]

#print axioms squareIso_section
#print axioms baseChanged_act
#print axioms changeLine_act
#print axioms baseChanged_alternating
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X Y : Scheme}

def scale {M : X.Modules} (a : Γ(X, ⊤))
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :=
  fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) a ≫ s

lemma pull_scale (f : X ⟶ Y) {M : Y.Modules} (a : Γ(Y, ⊤))
    (s : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) :
    pull f (scale a s) = scale (f.appTop a) (pull f s) := by
  have h : (unitIso f).inv ≫ (Scheme.Modules.pullback f).map
      (fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) a) =
      fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) (f.appTop a) ≫ (unitIso f).inv := by
    apply (cancel_mono (unitIso f).hom).mp
    change ((unitIso f).inv ≫ (Scheme.Modules.pullback f).map
      (fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) a)) ≫ unitPullback f = _
    rw [Category.assoc, pullback_multiplication]
    change (unitIso f).inv ≫ (unitIso f).hom ≫ _ = _
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [pull, scale, Functor.map_comp]
  rw [← Category.assoc, h, Category.assoc]

lemma act_scale (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (a : Γ(X, ⊤))
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act f α (scale a s) = scale (f.appTop a) (act f α s) := by
  change pull f (scale a s) ≫ α.hom = scale (f.appTop a) (pull f s ≫ α.hom)
  rw [pull_scale]
  exact Category.assoc _ _ _

lemma base_scalar_fixed {F : Type} [CommRing F] (p : X ⟶ Spec (CommRingCat.of F))
    (f : X ⟶ X) (hf : f ≫ p = p) (a : F) :
    f.appTop (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) =
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a := by
  have h := congrArg Scheme.Hom.appTop hf
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun q => q ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a)) h

lemma act_base_scale {F : Type} [CommRing F] (p : X ⟶ Spec (CommRingCat.of F))
    (f : X ⟶ X) (hf : f ≫ p = p) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (a : F)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    act f α (scale (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) s) =
      scale (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) (act f α s) := by
  rw [act_scale, base_scalar_fixed p f hf]

lemma act_sum (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) {ι : Type} (J : Finset ι)
    (s : ι → ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M)) :
    act f α (∑ i ∈ J, s i) = ∑ i ∈ J, act f α (s i) := by
  unfold act pull
  erw [CategoryTheory.Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]

#print axioms pull_scale
#print axioms act_base_scale
#print axioms act_sum
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X Y : Scheme}

lemma fromSection_top (M : X.Modules) (s : Γ(M, ⊤)) :
    (fromSection M s).app ⊤ (1 : Γ(X, ⊤)) = s := by
  rw [fromSection_apply, one_smul]
  change M.presheaf.map (𝟙 _) s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma fromSection_evaluate (M : X.Modules)
    (s : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    fromSection M (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))) = s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext (a : Γ(X, U))
  rw [fromSection_apply]
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf s).naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  have hn' : M.presheaf.map (homOfLE le_top).op (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))) =
      Scheme.Modules.Hom.app s U (1 : Γ(X, U)) := by
    change Scheme.Modules.Hom.app s U (X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤))) =
      M.presheaf.map (homOfLE le_top).op (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))) at hn
    rw [map_one] at hn
    exact hn.symm
  rw [hn', ← Scheme.Modules.Hom.app_smul]
  congr 1
  exact mul_one a

def globalSectionsEquiv (M : X.Modules) :
    Γ(M, ⊤) ≃ ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) where
  toFun := fromSection M
  invFun s := Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))
  left_inv := fromSection_top M
  right_inv := fromSection_evaluate M

lemma unit_pull_one (f : X ⟶ Y) :
    (unitIso f).hom.app (f ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackLocalSection f (L := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (U := ⊤) (1 : Γ(Y, ⊤))) = (1 : Γ(X, f ⁻¹ᵁ ⊤)) := by
  change (unitPullback f).app (f ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection f (L := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (U := ⊤) (1 : Γ(Y, ⊤))) = _
  rw [Scheme.Modules.app_pullbackLocalSection]
  have h : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _) (unitPullback f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := Equiv.apply_symm_apply _ _
  rw [h]
  exact map_one (f.app ⊤).hom

#print axioms globalSectionsEquiv
#print axioms unit_pull_one

lemma pull_fromSection (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤)) :
    pull f (fromSection M s) =
      fromSection ((Scheme.Modules.pullback f).obj M) (Scheme.Modules.pullbackLocalSection f s) := by
  apply (globalSectionsEquiv ((Scheme.Modules.pullback f).obj M)).symm.injective
  change Scheme.Modules.Hom.app (pull f (fromSection M s)) ⊤ (1 : Γ(X, ⊤)) = _
  rw [show (globalSectionsEquiv ((Scheme.Modules.pullback f).obj M)).symm
    (fromSection ((Scheme.Modules.pullback f).obj M) (Scheme.Modules.pullbackLocalSection f s)) =
      Scheme.Modules.pullbackLocalSection f s from fromSection_top _ _]
  have hi : (unitIso f).inv.app ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.pullbackLocalSection f (L := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (U := ⊤) (1 : Γ(Y, ⊤)) := by
    apply mono_app_injective (unitIso f).hom ⊤
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
    exact (unit_pull_one f).symm
  change ((Scheme.Modules.pullback f).map (fromSection M s)).app ⊤
    ((unitIso f).inv.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [hi]
  exact (Scheme.Modules.pullbackLocalSection_app f (fromSection M s) (1 : Γ(Y, ⊤))).symm.trans
    (congrArg (Scheme.Modules.pullbackLocalSection f) (fromSection_top M s))

#print axioms pull_fromSection

lemma fromSection_map {M N : X.Modules} (u : M ⟶ N) (s : Γ(M, ⊤)) :
    fromSection N (u.app ⊤ s) = fromSection M s ≫ u := by
  have h := fromSection_evaluate N (fromSection M s ≫ u)
  change fromSection N (u.app ⊤ ((fromSection M s).app ⊤ (1 : Γ(X, ⊤)))) = _ at h
  rw [fromSection_top] at h
  exact h

/-- The actual action on the global section module used by flat base change. -/
def globalAct (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(M, ⊤)) : Γ(M, ⊤) :=
  α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f s)

lemma act_fromSection (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(M, ⊤)) :
    act f α (fromSection M s) = fromSection M (globalAct f α s) := by
  rw [act, pull_fromSection, ← fromSection_map]
  rfl

lemma globalAct_alternating (f g : X ⟶ X) (hg : g ≫ g = 𝟙 X)
    (hfg : (f ≫ g) ≫ (f ≫ g) = 𝟙 X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (hβ : (Scheme.Modules.pullback g).mapIso β ≪≫ β =
      FixedPointPullback.squareComparison g hg M)
    (hα : (Scheme.Modules.pullback (f ≫ g)).mapIso (Midpoint.composeLift f g M α β) ≪≫
      Midpoint.composeLift f g M α β = FixedPointPullback.squareComparison (f ≫ g) hfg M)
    (s : Γ(M, ⊤)) :
    globalAct g β (globalAct f α (globalAct g β (globalAct f α s))) = s := by
  apply (globalSectionsEquiv M).injective
  change fromSection M (globalAct g β (globalAct f α (globalAct g β (globalAct f α s)))) =
    fromSection M s
  rw [← act_fromSection, ← act_fromSection, ← act_fromSection, ← act_fromSection]
  exact act_alternating f g hg hfg α β hβ hα _

#print axioms act_fromSection
#print axioms globalAct_alternating

/-- The induced linear endomorphism uses precisely the field action of the
specified structural morphism. -/
def globalActLinear (F : Type) [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    (f : X ⟶ X) (hf : f ≫ p = p) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) :
    letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
    Module.End F Γ(M, ⊤) := by
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  refine { toFun := globalAct f α, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    simp only [globalAct, Scheme.Modules.pullbackLocalSection_add, map_add]
  · intro a s
    change α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f
      ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) • s)) =
      (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) • globalAct f α s
    rw [Scheme.Modules.pullbackLocalSection_smul]
    have hscalar := base_scalar_fixed p f hf a
    change f.app ⊤ (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) =
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a at hscalar
    rw [hscalar, Scheme.Modules.Hom.app_smul]
    rfl

#print axioms globalActLinear
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

lemma labelTranslation_over
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection) :
    (labelTranslation k L D X x P).hom ≫ structureMap k L D X x = structureMap k L D X x :=
  (groupLaw k L D X x).translate_over _

/-- The arithmetic translation operator on the genuine rank-m section module. -/
def thetaSectionOperator (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (α : LabelThetaLift k L D X x m P) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.End F Γ(thetaLine k L D X x m, ⊤) :=
  SectionAction.globalActLinear (Component k L D X x).functionField
    (structureMap k L D X x) (labelTranslation k L D X x P).hom
    (labelTranslation_over k L D X x P) α

/-- The normalized inversion acts linearly over the same component field. -/
def thetaInversionOperator (m : ℕ) (hm : 0 < m) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    Module.End F Γ(thetaLine k L D X x m, ⊤) :=
  SectionAction.globalActLinear (Component k L D X x).functionField
    (structureMap k L D X x) (inverseIso k L D X x).hom (inverse_over k L D X x)
    (normalizedInversion k L D X x m hm)

lemma thetaSectionOperator_symmetry (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (α : LabelThetaLift k L D X x m P)
    (hα : LabelLiftSymmetry k L D X x m hm P α) :
    let F := (Component k L D X x).functionField
    letI : Algebra F Γ(curve k L D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
    let A := thetaSectionOperator k L D X x m P α
    let S := thetaInversionOperator k L D X x m hm
    S * A * S * A = 1 := by
  let F := (Component k L D X x).functionField
  letI : Algebra F Γ(curve k L D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k L D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k L D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k L D X x, ⊤))
  dsimp only
  apply LinearMap.ext
  intro s
  exact SectionAction.globalAct_alternating (labelTranslation k L D X x P).hom
    (inverseIso k L D X x).hom (GroupInversion.square (groupLaw k L D X x))
    (Midpoint.reflection_square (groupLaw k L D X x) (groupLaw_commutative k L D X x) _)
    α (normalizedInversion k L D X x m hm) (normalizedInversion_square k L D X x m hm) hα s

#print axioms thetaSectionOperator
#print axioms thetaSectionOperator_symmetry
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open scoped TensorProduct
variable {X Y : Scheme}

lemma globalAct_baseChanged (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(M, ⊤)) :
    globalAct g (baseChangedLift c f g h α) (Scheme.Modules.pullbackLocalSection c s) =
      Scheme.Modules.pullbackLocalSection c (globalAct f α s) := by
  apply (globalSectionsEquiv ((Scheme.Modules.pullback c).obj M)).injective
  change fromSection _ (globalAct g _ _) = fromSection _ _
  rw [← act_fromSection, ← pull_fromSection, baseChanged_act, act_fromSection, pull_fromSection]

/-- Equality on pulled sections determines a linear map on all sections after
a Cartesian extension of the actual structural field. -/
lemma end_eq_id_on_baseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
    letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
      Module.compHom _ (algebraMap K Γ(Y, ⊤))
    ∀ E : Module.End K Γ((Scheme.Modules.pullback c).obj M, ⊤),
      (∀ s : Γ(M, ⊤), E (Scheme.Modules.pullbackLocalSection c s) =
        Scheme.Modules.pullbackLocalSection c s) → E = 1 := by
  letI : Algebra F K := ι.toAlgebra
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
    Module.compHom _ (algebraMap K Γ(Y, ⊤))
  intro E hE
  obtain ⟨β, hβ⟩ := fieldSections_baseChange ι p q c hc M hM
  apply LinearMap.ext
  intro s
  obtain ⟨t, rfl⟩ := β.surjective s
  change E (β t) = β t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a s =>
    have ht : β (a ⊗ₜ[F] s) = a • β (1 ⊗ₜ[F] s) := by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (β.map_smul a (1 ⊗ₜ[F] s))
    rw [ht, map_smul, hβ, hE]
  | add t u ht hu => simp only [map_add, ht, hu]

set_option maxRecDepth 3000 in
/-- The arithmetic alternating symmetry identity persists on every section
after field base change, not only on the pulled sections. -/
lemma globalAct_alternating_baseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (hf' : f' ≫ q = q) (hg' : g' ≫ q = q)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct g β (globalAct f α (globalAct g β (globalAct f α s))) = s)
    (s : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
    let A := globalAct f' (baseChangedLift c f f' hf α)
    let S := globalAct g' (baseChangedLift c g g' hg β)
    S (A (S (A s))) = s := by
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
    Module.compHom _ (algebraMap K Γ(Y, ⊤))
  let A := globalActLinear K q f' hf' (baseChangedLift c f f' hf α)
  let S := globalActLinear K q g' hg' (baseChangedLift c g g' hg β)
  have he : S * A * S * A = 1 := by
    apply end_eq_id_on_baseChange ι p q c hc M hM
    intro s
    change globalAct g' (baseChangedLift c g g' hg β)
      (globalAct f' (baseChangedLift c f f' hf α)
        (globalAct g' (baseChangedLift c g g' hg β)
          (globalAct f' (baseChangedLift c f f' hf α) (Scheme.Modules.pullbackLocalSection c s)))) = _
    rw [globalAct_baseChanged, globalAct_baseChanged, globalAct_baseChanged,
      globalAct_baseChanged, h]
  exact LinearMap.congr_fun he s

#print axioms globalAct_baseChanged
#print axioms end_eq_id_on_baseChange
#print axioms globalAct_alternating_baseChange
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X : Scheme}

lemma globalAct_changeLine (f : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(M, ⊤)) :
    globalAct f (changeLine f e α) (e.hom.app ⊤ s) = e.hom.app ⊤ (globalAct f α s) := by
  apply (globalSectionsEquiv N).injective
  change fromSection N (globalAct f _ _) = fromSection N _
  rw [← act_fromSection, fromSection_map, changeLine_act, act_fromSection, fromSection_map]

lemma globalAct_alternating_changeLine (f g : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct g β (globalAct f α (globalAct g β (globalAct f α s))) = s)
    (s : Γ(N, ⊤)) :
    let A := globalAct f (changeLine f e α)
    let S := globalAct g (changeLine g e β)
    S (A (S (A s))) = s := by
  have hs : e.hom.app ⊤ (e.inv.app ⊤ s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  dsimp only
  nth_rw 1 [← hs]
  rw [globalAct_changeLine, globalAct_changeLine, globalAct_changeLine, globalAct_changeLine, h, hs]

#print axioms globalAct_changeLine
#print axioms globalAct_alternating_changeLine
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181

/-- Inversion from the actual prescribed Tate group law. -/
def tateInverseMap (k : Type) [Field k] [CharZero k] (L : ℕ) (V : TateLevel k L) :
    ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k L) ⟶
      ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k L) :=
  (V.law.inv (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    WeierstrassProjModel.RelativeGroupLaw.idPoint).val

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

/-- Pullback of the arithmetic lift, transported to the actual Tate theta line. -/
def tateArithmeticLabelLift (m : ℕ)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val)
    (α : LabelThetaLift k L D X x m P) : TateLabelThetaLift k L D X V m Q :=
  SectionAction.changeLine _ (thetaLine_tateIso k L D X x V θ hb m)
    (SectionAction.baseChangedLift (tateMap k L D X x V θ hb)
      (labelTranslation k L D X x P).hom _
      (labelTranslation_tate k L D X x V θ hb P Q hQ).symm α)

/-- Pullback of the conormal-normalized inversion to the same Tate theta line. -/
def tateArithmeticInversionLift (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.pullback (tateInverseMap k L V.level)).obj (tateThetaLine k L m) ≅
      tateThetaLine k L m :=
  SectionAction.changeLine _ (thetaLine_tateIso k L D X x V θ hb m)
    (SectionAction.baseChangedLift (tateMap k L D X x V θ hb)
      (inverseIso k L D X x).hom (tateInverseMap k L V.level)
      (tateMap_inverse k L D X x V θ hb).symm (normalizedInversion k L D X x m hm))

set_option maxRecDepth 3000 in
/-- Arithmetic symmetry holds on every section of the actual Tate theta line
after the original field extension and the checked line comparison. -/
lemma tateArithmeticLabelLift_symmetry (m : ℕ) (hm : 0 < m)
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (Q : SchemeHomOver (𝟙 _)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L)))
    (hQ : Q.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val)
    (α : LabelThetaLift k L D X x m P) (hα : LabelLiftSymmetry k L D X x m hm P α)
    (s : Γ(tateThetaLine k L m, ⊤)) :
    let A := SectionAction.globalAct
      (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.level.law (V.level.law.nsmul (𝟙 _) 2 Q))
      (tateArithmeticLabelLift k L D X x V θ hb m P Q hQ α)
    let S := SectionAction.globalAct (tateInverseMap k L V.level)
      (tateArithmeticInversionLift k L D X x V θ hb m hm)
    S (A (S (A s))) = s := by
  dsimp only [tateArithmeticLabelLift, tateArithmeticInversionLift]
  apply SectionAction.globalAct_alternating_changeLine
  intro s
  apply SectionAction.globalAct_alternating_baseChange θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
    (labelTranslation k L D X x P).hom (inverseIso k L D X x).hom _ _
    (labelTranslation_tate k L D X x V θ hb P Q hQ).symm
    (tateMap_inverse k L D X x V θ hb).symm
    (ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift_over V.level.law _)
    (V.level.law.inv _ WeierstrassProjModel.RelativeGroupLaw.idPoint).property
    (thetaLine k L D X x m) (thetaLine_invertible k L D X x m) α
    (normalizedInversion k L D X x m hm)
  intro s
  exact SectionAction.globalAct_alternating (labelTranslation k L D X x P).hom
    (inverseIso k L D X x).hom (GroupInversion.square (groupLaw k L D X x))
    (Midpoint.reflection_square (groupLaw k L D X x) (groupLaw_commutative k L D X x) _)
    α (normalizedInversion k L D X x m hm) (normalizedInversion_square k L D X x m hm) hα s

#print axioms tateArithmeticLabelLift
#print axioms tateArithmeticInversionLift
#print axioms tateArithmeticLabelLift_symmetry
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

lemma ihomGlobalSectionsEquiv_pre {X : Scheme} {A B N : X.Modules}
    (f : B ⟶ A) (s : Γ((ihom A).obj N, ⊤)) :
    ihomGlobalSectionsEquiv B N (((MonoidalClosed.pre f).app N).app ⊤ s) =
      f ≫ ihomGlobalSectionsEquiv A N s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext b
  rw [ihomGlobalSectionsEquiv_app_apply]
  have hn := ((MonoidalClosed.pre f).app N).mapPresheaf.naturality_apply
    (homOfLE (show U ≤ ⊤ from le_top)).op s
  erw [← hn]
  erw [ihomEval_pre_app]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ihomGlobalSectionsEquiv_app_apply]

/-- Dualization intertwines the genuine global-section action with pullback
and precomposition on sheaf functionals. -/
lemma dualLift_globalAct {X : Scheme} (f : X ⟶ X) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(Scheme.Modules.dual M, ⊤)) :
    ihomGlobalSectionsEquiv M (𝟙_ X.Modules)
      (SectionAction.globalAct f (dualLift f M hM α) s) =
      α.inv ≫ (Scheme.Modules.pullback f).map
        (ihomGlobalSectionsEquiv M (𝟙_ X.Modules) s) ≫
          ArithmeticThetaPolygonCartierR0133.unitPullback f := by
  change ihomGlobalSectionsEquiv M (𝟙_ X.Modules)
    (((MonoidalClosed.pre α.inv).app (𝟙_ X.Modules)).app ⊤
      ((dualComparison f M).app ⊤ (Scheme.Modules.pullbackLocalSection f s))) = _
  rw [ihomGlobalSectionsEquiv_pre, dualComparison_global]

#print axioms ihomGlobalSectionsEquiv_pre
#print axioms dualLift_globalAct
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141

lemma genericDual_globalAct (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    (f : genericScheme k M ⟶ genericScheme k M) (e : Lift k M s d f)
    (v : Γ(Scheme.Modules.dual (genericPower k M s d), ⊤)) :
    ihomGlobalSectionsEquiv _ _
      (SectionAction.globalAct f (dualLift f _ hL e.symm) v) =
      ArithmeticThetaGeometricLiftsR0141.act k M s d f e
        (ihomGlobalSectionsEquiv _ _ v) :=
  dualLift_globalAct f _ hL e.symm v

/-- The accepted symmetry predicate is equivalent to the alternating identity
on sections of the actual dual ideal line. -/
lemma genericDual_symmetric_iff (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    (f g : genericScheme k M ⟶ genericScheme k M)
    (e : Lift k M s d f) (eS : Lift k M s d g) :
    ArithmeticThetaSymmetricMarkingR0142.Symmetric k M s d f g eS e ↔
      ∀ v : Γ(Scheme.Modules.dual (genericPower k M s d), ⊤),
        SectionAction.globalAct g (dualLift g _ hL eS.symm)
          (SectionAction.globalAct f (dualLift f _ hL e.symm)
            (SectionAction.globalAct g (dualLift g _ hL eS.symm)
              (SectionAction.globalAct f (dualLift f _ hL e.symm) v))) = v := by
  constructor
  · intro h v
    apply (ihomGlobalSectionsEquiv _ _).injective
    erw [genericDual_globalAct, genericDual_globalAct, genericDual_globalAct,
      genericDual_globalAct]
    exact h _
  · intro h φ
    let v := (ihomGlobalSectionsEquiv (genericPower k M s d)
      (𝟙_ (genericScheme k M).Modules)).symm φ
    have hv : ihomGlobalSectionsEquiv _ _ v = φ := AddEquiv.apply_symm_apply _ _
    have hh := congrArg (ihomGlobalSectionsEquiv _ _) (h v)
    erw [genericDual_globalAct, genericDual_globalAct, genericDual_globalAct,
      genericDual_globalAct, hv] at hh
    exact hh

#print axioms genericDual_globalAct
#print axioms genericDual_symmetric_iff
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
namespace Scalar
open P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme.Modules

lemma aut_eq_smulIso {X : Scheme} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (e : M ≅ M) :
    ∃ u : Γ(X, ⊤)ˣ, e = smulIso u M := by
  obtain ⟨a, ha, -⟩ := hM.existsUnique_app_eq_smul e.hom
  obtain ⟨b, hb, -⟩ := hM.existsUnique_app_eq_smul e.inv
  obtain ⟨c, -, hc⟩ := hM.existsUnique_app_eq_smul (𝟙 M)
  have h1 : (1 : Γ(X, ⊤)) = c := hc 1 (by
    intro U x
    change x = _
    simp only [map_one, one_smul])
  have hab : a*b = 1 := by
    apply Eq.trans _ h1.symm
    apply hc
    intro U x
    have he := congrArg (fun q => q.app U x) e.inv_hom_id
    change e.hom.app U (e.inv.app U x) = x at he
    rw [ha, hb, smul_smul, ← map_mul] at he
    exact he.symm
  refine ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ?_⟩
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact ha U x

lemma pre_smulHom {X : Scheme} (a : Γ(X, ⊤)) (M N : X.Modules) :
    (MonoidalClosed.pre (smulHom a M)).app N = smulHom a ((ihom M).obj N) := by
  apply Scheme.Modules.ihom_hom_ext
  intro U m t
  rw [ihomEval_pre_app]
  change ihomEval M N U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a • m) t =
    ihomEval M N U m (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a • t)
  rw [ihomEval_smul_left, ihomEval_smul_right]

lemma dualLift_smul {X : Scheme} (f : X ⟶ X) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : M ≅ (Scheme.Modules.pullback f).obj M) (u : Γ(X, ⊤)ˣ) :
    dualLift f M hM (smulIso u M ≪≫ e).symm =
      dualLift f M hM e.symm ≪≫ smulIso u (Scheme.Modules.dual M) := by
  apply Iso.ext
  change dualComparison f M ≫ (MonoidalClosed.pre ((smulIso u M).hom ≫ e.hom)).app _ =
    (dualComparison f M ≫ (MonoidalClosed.pre e.hom).app _) ≫ _
  rw [MonoidalClosed.pre_map]
  change dualComparison f M ≫ ((MonoidalClosed.pre e.hom).app _ ≫
    (MonoidalClosed.pre (smulHom (u : Γ(X, ⊤)) M)).app _) = _
  rw [pre_smulHom, Category.assoc]
  rfl

/-- Every lift of the positive dual line comes from an ideal lift, once one
ideal lift is known. The proof uses actual invertible-sheaf scalar rigidity. -/
lemma exists_idealLift {X : Scheme} (f : X ⟶ X) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : M ≅ (Scheme.Modules.pullback f).obj M)
    (β : (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M) ≅ Scheme.Modules.dual M) :
    ∃ e' : M ≅ (Scheme.Modules.pullback f).obj M,
      dualLift f M hM e'.symm = β := by
  obtain ⟨u, hu⟩ := aut_eq_smulIso hM.dual.1 ((dualLift f M hM e.symm).symm ≪≫ β)
  refine ⟨smulIso u M ≪≫ e, ?_⟩
  rw [dualLift_smul, ← hu]
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

#print axioms aut_eq_smulIso
#print axioms pre_smulHom
#print axioms dualLift_smul
#print axioms exists_idealLift
end Scalar
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

/-- A frame of a base line trivializes its pullback factor on the actual curve. -/
def tensorBaseFrame {Y B : Scheme} (p : Y ⟶ B) (M : Y.Modules)
    (H : B.Modules) (h : H ≅ 𝟙_ B.Modules) :
    M ⊗ (Scheme.Modules.pullback p).obj H ≅ M :=
  (Iso.refl M ⊗ᵢ ((Scheme.Modules.pullback p).mapIso h ≪≫ SectionAction.unitIso p)) ≪≫ ρ_ M

lemma tateHodge_invertible (k : Type) [Field k] [CharZero k] (r : ℕ)
    (hE : (TateCurve k r).IsElliptic) :
    Scheme.Modules.IsInvertible (tateHodgeLine k r) := by
  letI := hE
  let p := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r)
  letI : SmoothOfRelativeDimension 1 p :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  exact Scheme.Modules.IsInvertible.pullback _
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (p.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1)

/-- A frame is chosen over the existing Laurent field, with no extension. -/
def tateHodgePowerFrame (k : Type) [Field k] [CharZero k] (r d : ℕ)
    (hE : (TateCurve k r).IsElliptic) :
    (tateHodgeLine k r).tensorPow d ≅ 𝟙_ (Puncture k).Modules :=
  (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2
    (LaurentSeries k) _ ((tateHodge_invertible k r hE).tensorPow d)).some

variable (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (E : genericScheme k M ≅ ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k r))
    (hO : genericPoint k M s hs.1 ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (hI : (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker.IsInvertible)

/-- The full Tate theta line becomes the accepted generic dual ideal line after
an actual base Hodge frame and the pointed canonical model comparison. -/
def modelThetaComparison (d : ℕ)
    (hH : (tateHodgeLine k r).tensorPow d ≅ 𝟙_ (Puncture k).Modules) :
    (Scheme.Modules.pullback E.hom).obj (tateThetaLine k r d) ≅
      Scheme.Modules.dual (genericPower k M s d) := by
  let I := ((ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker ^ d).module
  let c := modelPowerComparison k h3 M hM s hs E hO hI d
  letI := dualComparison_isIso E.hom I (hI.pow d).isInvertible_module
  exact (Scheme.Modules.pullback E.hom).mapIso
      (tensorBaseFrame (ArithmeticThetaRelativeKatoR0169.structureMap
        (LaurentSeries k) (TateCurve k r)) (Scheme.Modules.dual I) _ hH) ≪≫
    asIso (dualComparison E.hom I) ≪≫
      ((MonoidalClosed.internalHom (C := (genericScheme k M).Modules)).mapIso c.symm.op).app
        (𝟙_ (genericScheme k M).Modules)

def modelThetaIso (d : ℕ) (hE : (TateCurve k r).IsElliptic) :
    (Scheme.Modules.pullback E.hom).obj (tateThetaLine k r d) ≅
      Scheme.Modules.dual (genericPower k M s d) :=
  modelThetaComparison k h3 M hM s hs E hO hI d (tateHodgePowerFrame k r d hE)

#print axioms tateHodge_invertible
#print axioms tateHodgePowerFrame
#print axioms modelThetaIso
#print axioms tensorBaseFrame
#print axioms modelThetaComparison
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X Y : Scheme}

lemma pull_surjective (c : Y ⟶ X) [IsIso c] (M : X.Modules) :
    Function.Surjective (pull c (M := M)) := by
  intro t
  let F := Scheme.Modules.pullback c
  let G := Scheme.Modules.pullback (inv c)
  let η : 𝟭 X.Modules ≅ F ⋙ G :=
    ((Scheme.Modules.pullbackComp (inv c) c) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id c) ≪≫ Scheme.Modules.pullbackId X).symm
  let ε : G ⋙ F ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp c (inv c) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.hom_inv_id c) ≪≫ Scheme.Modules.pullbackId Y
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  refine ⟨F.preimage ((unitIso c).hom ≫ t), ?_⟩
  change (unitIso c).inv ≫ F.map (F.preimage ((unitIso c).hom ≫ t)) = t
  rw [F.map_preimage, Iso.inv_hom_id_assoc]

lemma pullbackSection_surjective (c : Y ⟶ X) [IsIso c] (M : X.Modules) :
    Function.Surjective (fun s : Γ(M, ⊤) => Scheme.Modules.pullbackLocalSection c s) := by
  intro t
  obtain ⟨u, hu⟩ := pull_surjective c M (fromSection _ t)
  obtain ⟨s, hs⟩ := (globalSectionsEquiv M).surjective u
  refine ⟨s, ?_⟩
  apply (globalSectionsEquiv _).injective
  change fromSection _ (Scheme.Modules.pullbackLocalSection c s) = fromSection _ t
  rw [← pull_fromSection]
  exact (congrArg (pull c) hs).trans hu

lemma globalAct_alternating_baseChanged_iso (c : Y ⟶ X) [IsIso c]
    (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct g β (globalAct f α (globalAct g β (globalAct f α s))) = s)
    (s : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
    let A := globalAct f' (baseChangedLift c f f' hf α)
    let S := globalAct g' (baseChangedLift c g g' hg β)
    S (A (S (A s))) = s := by
  obtain ⟨t, rfl⟩ := pullbackSection_surjective c M s
  dsimp only
  rw [globalAct_baseChanged, globalAct_baseChanged, globalAct_baseChanged, globalAct_baseChanged, h]

lemma globalAct_square (f : X ⟶ X) (hf : f ≫ f = 𝟙 X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (hα : (Scheme.Modules.pullback f).mapIso α ≪≫ α = FixedPointPullback.squareComparison f hf M)
    (s : Γ(M, ⊤)) : globalAct f α (globalAct f α s) = s := by
  apply (globalSectionsEquiv M).injective
  change fromSection M (globalAct f α (globalAct f α s)) = fromSection M s
  rw [← act_fromSection, ← act_fromSection]
  exact act_square f hf α hα _

lemma globalAct_square_baseChanged_iso (c : Y ⟶ X) [IsIso c]
    (f : X ⟶ X) (f' : Y ⟶ Y) (hf : c ≫ f = f' ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct f α (globalAct f α s) = s)
    (s : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
    globalAct f' (baseChangedLift c f f' hf α)
      (globalAct f' (baseChangedLift c f f' hf α) s) = s := by
  obtain ⟨t, rfl⟩ := pullbackSection_surjective c M s
  rw [globalAct_baseChanged, globalAct_baseChanged, h]

lemma globalAct_square_changeLine (f : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct f α (globalAct f α s) = s)
    (s : Γ(N, ⊤)) :
    globalAct f (changeLine f e α) (globalAct f (changeLine f e α) s) = s := by
  have hs : e.hom.app ⊤ (e.inv.app ⊤ s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  nth_rw 1 [← hs]
  rw [globalAct_changeLine, globalAct_changeLine, h, hs]

lemma globalAct_square_baseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : CategoryTheory.IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (f : X ⟶ X) (f' : Y ⟶ Y) (hf : c ≫ f = f' ≫ c) (hf' : f' ≫ q = q)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (h : ∀ s : Γ(M, ⊤), globalAct f α (globalAct f α s) = s)
    (s : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
    globalAct f' (baseChangedLift c f f' hf α)
      (globalAct f' (baseChangedLift c f f' hf α) s) = s := by
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
    Module.compHom _ (algebraMap K Γ(Y, ⊤))
  let A := globalActLinear K q f' hf' (baseChangedLift c f f' hf α)
  have he : A * A = 1 := by
    apply end_eq_id_on_baseChange ι p q c hc M hM
    intro t
    change globalAct f' (baseChangedLift c f f' hf α)
      (globalAct f' (baseChangedLift c f f' hf α) (Scheme.Modules.pullbackLocalSection c t)) = _
    rw [globalAct_baseChanged, globalAct_baseChanged, h]
  exact LinearMap.congr_fun he s

#print axioms globalAct_square
#print axioms globalAct_square_baseChanged_iso
#print axioms globalAct_square_changeLine
#print axioms globalAct_square_baseChange
#print axioms pull_surjective
#print axioms pullbackSection_surjective
#print axioms globalAct_alternating_baseChanged_iso
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base)

lemma normalizedInversion_globalAct_square (m : ℕ) (hm : 0 < m)
    (s : Γ(thetaLine k L D X x m, ⊤)) :
    SectionAction.globalAct (inverseIso k L D X x).hom (normalizedInversion k L D X x m hm)
      (SectionAction.globalAct (inverseIso k L D X x).hom (normalizedInversion k L D X x m hm) s) = s :=
  SectionAction.globalAct_square _ (GroupInversion.square (groupLaw k L D X x))
    _ (normalizedInversion_square k L D X x m hm) s

lemma tateArithmeticInversionLift_square (m : ℕ) (hm : 0 < m)
    (s : Γ(tateThetaLine k L m, ⊤)) :
    SectionAction.globalAct (tateInverseMap k L V.level)
      (tateArithmeticInversionLift k L D X x V θ hb m hm)
      (SectionAction.globalAct (tateInverseMap k L V.level)
        (tateArithmeticInversionLift k L D X x V θ hb m hm) s) = s := by
  dsimp only [tateArithmeticInversionLift]
  apply SectionAction.globalAct_square_changeLine
  intro t
  apply SectionAction.globalAct_square_baseChange θ (structureMap k L D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k L))
    (tateMap k L D X x V θ hb) (tateMap_cartesian k L D X x V θ hb)
    (inverseIso k L D X x).hom _ (tateMap_inverse k L D X x V θ hb).symm
    (V.level.law.inv _ WeierstrassProjModel.RelativeGroupLaw.idPoint).property
    (thetaLine k L D X x m) (thetaLine_invertible k L D X x m)
    (normalizedInversion k L D X x m hm)
  exact normalizedInversion_globalAct_square k L D X x m hm

#print axioms normalizedInversion_globalAct_square
#print axioms tateArithmeticInversionLift_square
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
open ArithmeticThetaSymmetricMarkingR0142
open ArithmeticThetaSymmetricMarkingR0142.SymmetricMarkingFiniteSignsR0142

variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d n : ℕ)

lemma involutive_scaled_square (hn : 0 < n)
    (b : Fin n → GenericDual k M s d) (hb : HasBasis k M s d n b)
    (S S' : GenericDual k M s d → GenericDual k M s d)
    (hlin : LinearAction k M s d n S)
    (hS : ∀ φ, S (S φ) = φ) (hS' : ∀ φ, S' (S' φ) = φ)
    (c : LaurentSeries k) (hc : ∀ φ, S' φ = sc k M s d c (S φ)) : c^2 = 1 := by
  apply scalar_faithful k M s d n hn b hb
  intro φ
  have h := hS' φ
  rw [hc, hc] at h
  erw [hlin.scale, sc_mul, hS] at h
  simpa only [pow_two, sc_one] using h

lemma alternating_inversion_scale
    (A S S' : GenericDual k M s d → GenericDual k M s d)
    (hA : LinearAction k M s d n A) (hS : LinearAction k M s d n S)
    (c : LaurentSeries k) (hc : c^2 = 1)
    (hscale : ∀ φ, S' φ = sc k M s d c (S φ)) (φ : GenericDual k M s d) :
    S' (A (S' (A φ))) = S (A (S (A φ))) := by
  rw [hscale, hscale]
  erw [hA.scale, hS.scale, sc_mul, ← pow_two, hc, sc_one]

/-- An involutive arithmetic inversion may differ from the accepted inversion
by a sign; that sign cancels in the alternating symmetry relation. -/
lemma symmetric_change_inversion (h3 : 3 ≤ r) (hM : IsModel k T M)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (hn : 0 < n)
    (b : Fin n → GenericDual k M s d) (hb : HasBasis k M s d n b)
    (f g : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (hg : g ≫ genericStructure k M = genericStructure k M)
    (e : Lift k M s d f) (eS eS' : Lift k M s d g)
    (hS : ∀ φ, act k M s d g eS (act k M s d g eS φ) = φ)
    (hS' : ∀ φ, act k M s d g eS' (act k M s d g eS' φ) = φ) :
    Symmetric k M s d f g eS' e ↔ Symmetric k M s d f g eS e := by
  obtain ⟨c, hc, -⟩ := generic_lift_scalar_comparison k r hr h3 T M hM s hs d g eS eS'
  have hscl := act_scaled k M s d g eS eS' c hc.2
  have linA := linear_act (k := k) (M := M) (s := s) (d := d) n f hf e
  have linS := linear_act (k := k) (M := M) (s := s) (d := d) n g hg eS
  have csq := involutive_scaled_square k M s d n hn b hb _ _ linS hS hS' c hscl
  have heq := alternating_inversion_scale k M s d n _ _ _ linA linS c csq hscl
  constructor
  · intro h φ
    exact (heq φ).symm.trans (h φ)
  · intro h φ
    exact (heq φ).trans (h φ)

#print axioms involutive_scaled_square
#print axioms alternating_inversion_scale
#print axioms symmetric_change_inversion
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaSymmetricMarkingR0142

variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))

/-- Pull an actual positive-line lift through the fixed scheme and line
comparisons, then express it as a genuine ideal-power lift. -/
def inducedIdealLift (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N) : Lift k M s d f :=
  (Scalar.exists_idealLift f _ hL e
    (SectionAction.changeLine f c (SectionAction.baseChangedLift E.hom g f h α))).choose

lemma inducedIdealLift_dual (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N) :
    dualLift f _ hL (inducedIdealLift k M s d hL E N c f g h e α).symm =
      SectionAction.changeLine f c (SectionAction.baseChangedLift E.hom g f h α) :=
  (Scalar.exists_idealLift f _ hL e
    (SectionAction.changeLine f c (SectionAction.baseChangedLift E.hom g f h α))).choose_spec

lemma inducedIdealLift_square (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N)
    (hα : ∀ v : Γ(N, ⊤), SectionAction.globalAct g α (SectionAction.globalAct g α v) = v)
    (φ : GenericDual k M s d) :
    let e' := inducedIdealLift k M s d hL E N c f g h e α
    act k M s d f e' (act k M s d f e' φ) = φ := by
  let e' := inducedIdealLift k M s d hL E N c f g h e α
  let v := (ihomGlobalSectionsEquiv (genericPower k M s d)
    (𝟙_ (genericScheme k M).Modules)).symm φ
  have hv : ihomGlobalSectionsEquiv _ _ v = φ := AddEquiv.apply_symm_apply _ _
  have hh : SectionAction.globalAct f (dualLift f _ hL e'.symm)
      (SectionAction.globalAct f (dualLift f _ hL e'.symm) v) = v := by
    dsimp only [e']
    rw [inducedIdealLift_dual]
    apply SectionAction.globalAct_square_changeLine
    exact SectionAction.globalAct_square_baseChanged_iso E.hom g f h α hα
  have hh' := congrArg (ihomGlobalSectionsEquiv _ _) hh
  erw [genericDual_globalAct, genericDual_globalAct, hv] at hh'
  exact hh'

lemma inducedIdealLift_symmetric
    (f fS : genericScheme k M ⟶ genericScheme k M) (g gS : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (hS : E.hom ≫ gS = fS ≫ E.hom)
    (e : Lift k M s d f) (eS : Lift k M s d fS)
    (α : (Scheme.Modules.pullback g).obj N ≅ N)
    (β : (Scheme.Modules.pullback gS).obj N ≅ N)
    (hα : ∀ v : Γ(N, ⊤), SectionAction.globalAct gS β
      (SectionAction.globalAct g α (SectionAction.globalAct gS β
        (SectionAction.globalAct g α v))) = v) :
    Symmetric k M s d f fS
      (inducedIdealLift k M s d hL E N c fS gS hS eS β)
      (inducedIdealLift k M s d hL E N c f g h e α) := by
  apply (genericDual_symmetric_iff k M s d hL _ _ _ _).mpr
  intro v
  rw [inducedIdealLift_dual, inducedIdealLift_dual]
  apply SectionAction.globalAct_alternating_changeLine
  exact SectionAction.globalAct_alternating_baseChanged_iso E.hom g gS f fS h hS α β hα

/-- The transported symmetry is measured against the accepted local inversion,
using its involutivity and scalar-sign invariance. -/
lemma inducedIdealLift_canonical_symmetric
    (h3 : 3 ≤ r) (hM : IsModel k T M) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (n : ℕ) (hn : 0 < n) (b : Fin n → GenericDual k M s d) (hb : HasBasis k M s d n b)
    (f fS : genericScheme k M ⟶ genericScheme k M) (g gS : Y ⟶ Y)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (hfS : fS ≫ genericStructure k M = genericStructure k M)
    (h : E.hom ≫ g = f ≫ E.hom) (hS : E.hom ≫ gS = fS ≫ E.hom)
    (e : Lift k M s d f) (eS : Lift k M s d fS)
    (α : (Scheme.Modules.pullback g).obj N ≅ N)
    (β : (Scheme.Modules.pullback gS).obj N ≅ N)
    (heS : ∀ φ, act k M s d fS eS (act k M s d fS eS φ) = φ)
    (hβ : ∀ v : Γ(N, ⊤), SectionAction.globalAct gS β (SectionAction.globalAct gS β v) = v)
    (hα : ∀ v : Γ(N, ⊤), SectionAction.globalAct gS β
      (SectionAction.globalAct g α (SectionAction.globalAct gS β
        (SectionAction.globalAct g α v))) = v) :
    Symmetric k M s d f fS eS (inducedIdealLift k M s d hL E N c f g h e α) := by
  apply (symmetric_change_inversion k M s d n h3 hM hs hn b hb f fS hf hfS
    (inducedIdealLift k M s d hL E N c f g h e α) eS
    (inducedIdealLift k M s d hL E N c fS gS hS eS β) heS
    (inducedIdealLift_square k M s d hL E N c fS gS hS eS β hβ)).mp
  exact inducedIdealLift_symmetric k M s d hL E N c f fS g gS h hS e eS α β hα

#print axioms inducedIdealLift
#print axioms inducedIdealLift_dual
#print axioms inducedIdealLift_square
#print axioms inducedIdealLift_symmetric
#print axioms inducedIdealLift_canonical_symmetric
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182

/-- One actual local model, with all three maps compared to the prescribed
Tate marking through the same pointed scheme isomorphism. -/
structure MarkedModel (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (V : TateLevel k (2*m)) (ζ : kˣ) where
  tower : Tower k (2*m) (Nat.mul_pos (by decide) hm)
  model : Model k tower
  isModel : IsModel k tower model
  origin : baseScheme k ⟶ model.X
  markedOrigin : MarkedLift k model (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 origin
  rotation : model.X ≅ model.X
  scaling : kˣ → (model.X ≅ model.X)
  inversion : model.X ≅ model.X
  actions : Actions k model rotation scaling inversion
  cubic : genericScheme k model ≅ ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k (2*m))
  cubic_over : cubic.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m)) = genericStructure k model
  cubic_origin : genericPoint k model origin markedOrigin.1 ≫ cubic.hom =
    ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k (2*m))
  scalar_commutes : scalarMap k model rotation scaling inversion actions (ζ^2) ≫ cubic.hom =
    cubic.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law (V.law.nsmul (𝟙 _) 2 V.marking.x)
  shift_commutes : shiftMap k model rotation scaling inversion actions ≫ cubic.hom =
    cubic.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law (V.law.nsmul (𝟙 _) 2 V.marking.y)
  inversion_commutes : inversionMap k model rotation scaling inversion actions ≫ cubic.hom =
    cubic.hom ≫ tateInverseMap k (2*m) V

lemma markedModel_exists (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
    (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) V) : Nonempty (MarkedModel k m hm V ζ) := by
  have hpos : 0 < 2*m := Nat.mul_pos (by decide) hm
  have h3 : 3 ≤ 2*m := thetaChartBound m hm he
  have he₂ : Even (2*m) := even_two_mul m
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k (2*m) h3 hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM (zeroIndex (2*m) hpos) 1
  obtain ⟨rot, scal, iv, ha⟩ := algebraized_annular_actions k (2*m) hpos h3 T M hM
  obtain ⟨E, hE, hO, hcoords⟩ := CubicComparison.canonical_model_iso k (2*m) hpos h3 he₂ T M hM s hs V ζ hζ hmark
  let G := transport E hE V.law
  have hG : IsOriginLaw k M s hs.1 G := CubicComparison.transported_origin k M s hs.1 V E hE hO
  refine ⟨{ tower := T
            model := M
            isModel := hM
            origin := s
            markedOrigin := hs
            rotation := rot
            scaling := scal
            inversion := iv
            actions := ha
            cubic := E
            cubic_over := hE
            cubic_origin := hO
            scalar_commutes := ?_
            shift_commutes := ?_
            inversion_commutes := ?_ }⟩
  · obtain ⟨p, hp, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM (zeroIndex (2*m) hpos) (ζ^2)
    let q := V.law.nsmul (𝟙 _) 2 V.marking.x
    have hpq : genericPoint k M p hp.1 ≫ E.hom = q.val := by
      have h := hcoords ⟨2, by omega⟩ (zeroIndex (2*m) hpos) p hp
      simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint, zeroIndex,
        WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, V.law.mul_one] using h
    have hf : IsTranslation k M G p hp.1 (scalarMap k M rot scal iv ha (ζ^2)) :=
      actual_scalar_translation k (2*m) hpos h3 T he₂ M hM s hs G hG rot scal iv ha (ζ^2) p hp
    exact model_translation k M V E hE p hp.1 q hpq _ hf
  · let j := next (2*m) hpos (zeroIndex (2*m) hpos)
    obtain ⟨p, hp, _⟩ := marked_section_algebraization k (2*m) hpos h3 T M hM j 1
    have hj : j.val = 1 := by
      change (0+1) % (2*m) = 1
      exact Nat.mod_eq_of_lt (by omega)
    have hpq : genericPoint k M p hp.1 ≫ E.hom = V.marking.y.val := by
      have hp' : MarkedLift k M j (ζ^(zeroIndex (2*m) hpos).val) p := by
        simpa only [zeroIndex, pow_zero] using hp
      have h := hcoords (zeroIndex (2*m) hpos) j p hp'
      simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint, zeroIndex, hj,
        WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,
        WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply, V.law.one_mul] using h
    have hf : IsTranslation k M G p hp.1 (rotationMap k M rot scal iv ha) :=
      actual_rotation_translation k (2*m) hpos h3 T he₂ M hM s hs G hG rot scal iv ha p hp
    have hfE := model_translation k M V E hE p hp.1 V.marking.y hpq _ hf
    have hdouble : V.law.nsmul (𝟙 _) 2 V.marking.y =
        V.law.mul (𝟙 _) V.marking.y V.marking.y := by
      rw [V.law.nsmul_succ, V.law.nsmul_one_apply]
    change (rotationMap k M rot scal iv ha ≫ rotationMap k M rot scal iv ha) ≫ E.hom = _
    rw [Category.assoc, hfE, ← Category.assoc, hfE, Category.assoc,
      ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift_comp, hdouble]
  · exact model_inversionMap k M V E hE h3 he₂ hM s hs hG rot scal iv ha

#print axioms markedModel_exists
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaSymmetricMarkingR0142

lemma tateOrigin_invertible (k : Type) [Field k] [CharZero k] (r : ℕ) (V : TateLevel k r) :
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)).ker.IsInvertible := by
  letI := V.elliptic
  let p := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k r)
  letI : SmoothOfRelativeDimension 1 p :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  letI : IsProper p := WeierstrassProjModel.projModelStrCR_isProper (TateCurve k r).toProjective
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := p) _
    (WeierstrassProjModel.kwZeroSect _ (TateCurve k r)).property

namespace MarkedModel
variable {k : Type} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    {V : TateLevel k (2*m)} {ζ : kˣ} (Q : MarkedModel k m hm V ζ)
    (he : Even m) (hζ : IsPrimitiveRoot (ζ : k) (2*m))

abbrev mapA := scalarMap k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2)
abbrev mapB := shiftMap k Q.model Q.rotation Q.scaling Q.inversion Q.actions
abbrev mapS := inversionMap k Q.model Q.rotation Q.scaling Q.inversion Q.actions

omit [CharZero k] in
include hm hζ in
lemma root_half : IsPrimitiveRoot ((ζ^2 : kˣ) : k) m := by
  simpa only [Units.val_pow_eq_pow_val] using
    IsPrimitiveRoot.pow (Nat.mul_pos (by decide) hm) hζ (rfl : 2*m = 2*m)

def canonicalA : Lift k Q.model Q.origin m Q.mapA :=
  (geometric_scalar_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2) (root_half (hm := hm) hζ)).choose

def canonicalB : Lift k Q.model Q.origin m Q.mapB :=
  (geometric_shift_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions).choose

def canonicalS : Lift k Q.model Q.origin m Q.mapS :=
  (geometric_inversion_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions).choose

lemma canonicalA_eigen : Eigen k Q.model Q.origin m m (ζ^2) Q.mapA (Q.canonicalA he hζ)
    (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin) :=
  (geometric_scalar_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2) (root_half (hm := hm) hζ)).choose_spec.1

lemma canonicalB_cyclic : Cyclic k Q.model Q.origin m m hm Q.mapB (Q.canonicalB he)
    (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin) :=
  (geometric_shift_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions).choose_spec.1

lemma canonicalS_reverses : Reverses k Q.model Q.origin m m hm Q.mapS (Q.canonicalS he)
    (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin) :=
  (geometric_inversion_lift k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions).choose_spec.1

lemma canonical_relations : Relations k Q.model Q.origin m (ζ^2)
    (act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ))
    (act k Q.model Q.origin m Q.mapB (Q.canonicalB he))
    (act k Q.model Q.origin m Q.mapS (Q.canonicalS he)) :=
  geometric_theta_relations k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2) (root_half (hm := hm) hζ)
    (Q.canonicalA he hζ) (Q.canonicalB he) (Q.canonicalA_eigen he hζ)
    (Q.canonicalB_cyclic he) (Q.canonicalS he) (Q.canonicalS_reverses he)

include he in
lemma ideal_invertible : Scheme.Modules.IsInvertible (genericPower k Q.model Q.origin m) :=
  Scheme.Modules.IsInvertible.pullback (genericInclusion k Q.model)
    (AlgebraizedThetaSectionsR0138.power_invertible k (thetaChartBound m hm he)
      Q.model Q.isModel Q.origin Q.markedOrigin m).isInvertible_module

def thetaComparison : (Scheme.Modules.pullback Q.cubic.hom).obj (tateThetaLine k (2*m) m) ≅
    Scheme.Modules.dual (genericPower k Q.model Q.origin m) :=
  modelThetaIso k (thetaChartBound m hm he) Q.model Q.isModel Q.origin Q.markedOrigin
    Q.cubic Q.cubic_origin (tateOrigin_invertible k (2*m) V) m V.elliptic

abbrev tateA := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
  (V.law.nsmul (𝟙 _) 2 V.marking.x)
abbrev tateB := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
  (V.law.nsmul (𝟙 _) 2 V.marking.y)

variable (α : (Scheme.Modules.pullback (tateA (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (β : (Scheme.Modules.pullback (tateB (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)

def inducedA : Lift k Q.model Q.origin m Q.mapA :=
  inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he) Q.cubic (tateThetaLine k (2*m) m)
    (Q.thetaComparison he) Q.mapA _ Q.scalar_commutes.symm (Q.canonicalA he hζ) α

def inducedB : Lift k Q.model Q.origin m Q.mapB :=
  inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he) Q.cubic (tateThetaLine k (2*m) m)
    (Q.thetaComparison he) Q.mapB _ Q.shift_commutes.symm (Q.canonicalB he) β

lemma induced_symmetric
    (S : (Scheme.Modules.pullback (tateInverseMap k (2*m) V)).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (hS : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ S v) = v)
    (hα : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ α
        (SectionAction.globalAct _ S (SectionAction.globalAct _ α v))) = v)
    (hβ : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ β
        (SectionAction.globalAct _ S (SectionAction.globalAct _ β v))) = v) :
    Symmetric k Q.model Q.origin m Q.mapA Q.mapS (Q.canonicalS he) (Q.inducedA he hζ α) ∧
    Symmetric k Q.model Q.origin m Q.mapB Q.mapS (Q.canonicalS he) (Q.inducedB he β) := by
  have hSq := (Q.canonical_relations he hζ).2.2.2.1
  have basis := generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
  constructor
  · exact inducedIdealLift_canonical_symmetric k Q.model Q.origin m (Q.ideal_invertible he)
      Q.cubic _ (Q.thetaComparison he) (thetaChartBound m hm he) Q.isModel Q.markedOrigin
      m hm _ basis Q.mapA Q.mapS _ _
      (GeometricScalarLiftR0141.scalarMap_over k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2))
      (GeometricInversionLiftR0141.inversionMap_structure k Q.model Q.rotation Q.scaling Q.inversion Q.actions)
      Q.scalar_commutes.symm Q.inversion_commutes.symm (Q.canonicalA he hζ) (Q.canonicalS he)
      α S hSq hS hα
  · exact inducedIdealLift_canonical_symmetric k Q.model Q.origin m (Q.ideal_invertible he)
      Q.cubic _ (Q.thetaComparison he) (thetaChartBound m hm he) Q.isModel Q.markedOrigin
      m hm _ basis Q.mapB Q.mapS _ _
      (GeometricShiftLiftR0141.shiftMap_structure k Q.model Q.rotation Q.scaling Q.inversion Q.actions)
      (GeometricInversionLiftR0141.inversionMap_structure k Q.model Q.rotation Q.scaling Q.inversion Q.actions)
      Q.shift_commutes.symm Q.inversion_commutes.symm (Q.canonicalB he) (Q.canonicalS he)
      β S hSq hS hβ

#print axioms canonical_relations
#print axioms thetaComparison
#print axioms induced_symmetric
end MarkedModel
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaSymmetricMarkingR0142
variable {k : Type} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    {V : TateLevel k (2*m)} {ζ : kˣ} (Q : MarkedModel k m hm V ζ)
    (he : Even m) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (α : (Scheme.Modules.pullback (tateA (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (β : (Scheme.Modules.pullback (tateB (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)

/-- Constant signs compare the transported arithmetic lifts with the prescribed
local theta lifts on every open. The exact m-th powers and commutator are
included on all genuine GenericDual sections. -/
def FiniteAlignment : Prop :=
  ∃! σ : k × k, σ.1^2 = 1 ∧ σ.2^2 = 1 ∧
    LiftScaled k Q.model Q.origin m Q.mapA (constant k σ.1)
      (Q.canonicalA he hζ) (Q.inducedA he hζ α) ∧
    LiftScaled k Q.model Q.origin m Q.mapB (constant k σ.2)
      (Q.canonicalB he) (Q.inducedB he β) ∧
    Relations k Q.model Q.origin m (ζ^2)
      (act k Q.model Q.origin m Q.mapA (Q.inducedA he hζ α))
      (act k Q.model Q.origin m Q.mapB (Q.inducedB he β))
      (act k Q.model Q.origin m Q.mapS (Q.canonicalS he))

lemma finiteAlignment
    (S : (Scheme.Modules.pullback (tateInverseMap k (2*m) V)).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (hS : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ S v) = v)
    (hα : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ α
        (SectionAction.globalAct _ S (SectionAction.globalAct _ α v))) = v)
    (hβ : ∀ v : Γ(tateThetaLine k (2*m) m, ⊤),
      SectionAction.globalAct _ S (SectionAction.globalAct _ β
        (SectionAction.globalAct _ S (SectionAction.globalAct _ β v))) = v) :
    Q.FiniteAlignment he hζ α β := by
  obtain ⟨ha, hb⟩ := Q.induced_symmetric he hζ α β S hS hα hβ
  exact symmetric_marking_finite_signs k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2) (root_half (hm := hm) hζ)
    (Q.canonicalA he hζ) (Q.canonicalB he) (Q.canonicalS he)
    (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he) (Q.canonicalS_reverses he)
    (Q.inducedA he hζ α) (Q.inducedB he β) ha hb

#print axioms finiteAlignment
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

def arithmeticModelA :=
  tateArithmeticLabelLift k (2*m) D X x V θ hb m D.atlas.marking.x V.level.marking.x V.classifies.2.2.2.1 α

def arithmeticModelB :=
  tateArithmeticLabelLift k (2*m) D X x V θ hb m D.atlas.marking.y V.level.marking.y V.classifies.2.2.2.2 β

/-- The constructed arithmetic symmetric lifts have the constant finite-sign
comparison at the original canonical branch, without a further field cover. -/
lemma arithmetic_finite_alignment
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β) :
    Q.FiniteAlignment he hζ
      (arithmeticModelA k m D X x V θ hb α)
      (arithmeticModelB k m D X x V θ hb β) := by
  apply Q.finiteAlignment he hζ _ _ (tateArithmeticInversionLift k (2*m) D X x V θ hb m hm)
  · exact tateArithmeticInversionLift_square k (2*m) D X x V θ hb m hm
  · exact tateArithmeticLabelLift_symmetry k (2*m) D X x V θ hb m hm
      D.atlas.marking.x V.level.marking.x V.classifies.2.2.2.1 α hα
  · exact tateArithmeticLabelLift_symmetry k (2*m) D X x V θ hb m hm
      D.atlas.marking.y V.level.marking.y V.classifies.2.2.2.2 β hβ

#print axioms arithmetic_finite_alignment
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X Y : Scheme}

lemma pull_injective (c : Y ⟶ X) [IsIso c] (M : X.Modules) :
    Function.Injective (pull c (M := M)) := by
  let F := Scheme.Modules.pullback c
  let G := Scheme.Modules.pullback (inv c)
  let η : 𝟭 X.Modules ≅ F ⋙ G :=
    ((Scheme.Modules.pullbackComp (inv c) c) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id c) ≪≫ Scheme.Modules.pullbackId X).symm
  let ε : G ⋙ F ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp c (inv c) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.hom_inv_id c) ≪≫ Scheme.Modules.pullbackId Y
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  intro s t h
  apply F.map_injective
  exact (cancel_epi (unitIso c).inv).mp h

lemma pullbackSection_injective (c : Y ⟶ X) [IsIso c] (M : X.Modules) :
    Function.Injective (fun s : Γ(M, ⊤) => Scheme.Modules.pullbackLocalSection c s) := by
  intro s t h
  apply (globalSectionsEquiv M).injective
  apply pull_injective c M
  change pull c (fromSection M s) = pull c (fromSection M t)
  rw [pull_fromSection, pull_fromSection]
  exact congrArg (fromSection _) h

def sectionIso {M N : X.Modules} (e : M ≅ N) : Γ(M, ⊤) ≃ Γ(N, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  right_inv s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl

#print axioms pullbackSection_injective
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141

variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))

def modelFunctional (v : Γ(N, ⊤)) : GenericDual k M s d :=
  ihomGlobalSectionsEquiv _ _ (c.hom.app ⊤ (pullbackLocalSection E.hom v))

lemma modelFunctional_bijective : Function.Bijective (modelFunctional k M s d E N c) :=
  (ihomGlobalSectionsEquiv _ _).bijective.comp
    ((SectionAction.sectionIso c).bijective.comp
      ⟨SectionAction.pullbackSection_injective E.hom N,
       SectionAction.pullbackSection_surjective E.hom N⟩)

def modelFunctionalEquiv : Γ(N, ⊤) ≃ GenericDual k M s d :=
  Equiv.ofBijective _ (modelFunctional_bijective k M s d E N c)

lemma modelFunctional_act (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N) (v : Γ(N, ⊤)) :
    act k M s d f (inducedIdealLift k M s d hL E N c f g h e α)
      (modelFunctional k M s d E N c v) =
    modelFunctional k M s d E N c (SectionAction.globalAct g α v) := by
  unfold modelFunctional
  erw [← genericDual_globalAct k M s d hL f
    (inducedIdealLift k M s d hL E N c f g h e α)]
  rw [inducedIdealLift_dual, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

lemma modelFunctional_iterate (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N) (n : ℕ) (v : Γ(N, ⊤)) :
    (act k M s d f (inducedIdealLift k M s d hL E N c f g h e α))^[n]
      (modelFunctional k M s d E N c v) =
    modelFunctional k M s d E N c ((SectionAction.globalAct g α)^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, modelFunctional_act, Function.iterate_succ_apply']

lemma source_order_of_induced (f : genericScheme k M ⟶ genericScheme k M) (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : Lift k M s d f)
    (α : (Scheme.Modules.pullback g).obj N ≅ N) (n : ℕ)
    (hn : ∀ φ, (act k M s d f (inducedIdealLift k M s d hL E N c f g h e α))^[n] φ = φ)
    (v : Γ(N, ⊤)) : (SectionAction.globalAct g α)^[n] v = v := by
  apply (modelFunctional_bijective k M s d E N c).1
  rw [← modelFunctional_iterate k M s d hL E N c f g h e α n v, hn]

#print axioms modelFunctional_bijective
#print axioms modelFunctional_act
#print axioms source_order_of_induced
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
variable {X Y : Scheme}

lemma fieldSectionPull_injective {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Function.Injective (fun s : Γ(M, ⊤) => Scheme.Modules.pullbackLocalSection c s) := by
  letI : Algebra F K := ι.toAlgebra
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
    Module.compHom _ (algebraMap K Γ(Y, ⊤))
  obtain ⟨β, hβ⟩ := fieldSections_baseChange ι p q c hc M hM
  intro s t h
  apply Module.Flat.tensorProduct_mk_injective (R := F) (S := K) (M := Γ(M, ⊤))
  apply β.injective
  change β (1 ⊗ₜ[F] s) = β (1 ⊗ₜ[F] t)
  rw [hβ, hβ]
  exact h

lemma globalAct_baseChanged_iterate (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (n : ℕ) (s : Γ(M, ⊤)) :
    (globalAct g (baseChangedLift c f g h α))^[n] (Scheme.Modules.pullbackLocalSection c s) =
      Scheme.Modules.pullbackLocalSection c ((globalAct f α)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, globalAct_baseChanged, Function.iterate_succ_apply']

lemma globalAct_changeLine_iterate (f : X ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (n : ℕ) (s : Γ(M, ⊤)) :
    (globalAct f (changeLine f e α))^[n] (e.hom.app ⊤ s) =
      e.hom.app ⊤ ((globalAct f α)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, globalAct_changeLine, Function.iterate_succ_apply']

lemma order_of_fieldBaseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ N)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : c ≫ f = g ≫ c)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (n : ℕ)
    (hn : ∀ s : Γ(N, ⊤), (globalAct g (changeLine g e (baseChangedLift c f g h α)))^[n] s = s)
    (s : Γ(M, ⊤)) : (globalAct f α)^[n] s = s := by
  apply fieldSectionPull_injective ι p q c hc M hM
  have hh := hn (e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection c s))
  rw [globalAct_changeLine_iterate, globalAct_baseChanged_iterate] at hh
  have he := congrArg (fun z => e.inv.app ⊤ z) hh
  have hi (z : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
      e.inv.app ⊤ (e.hom.app ⊤ z) = z := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  simpa only [hi] using he

#print axioms fieldSectionPull_injective
#print axioms order_of_fieldBaseChange
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaGeometricLiftsR0141
variable {k : Type} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    {V : TateLevel k (2*m)} {ζ : kˣ} (Q : MarkedModel k m hm V ζ)
    (he : Even m) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (α : (Scheme.Modules.pullback (tateA (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (β : (Scheme.Modules.pullback (tateB (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)

lemma tate_orders (h : Q.FiniteAlignment he hζ α β) :
    (∀ s : Γ(tateThetaLine k (2*m) m, ⊤), (SectionAction.globalAct _ α)^[m] s = s) ∧
    (∀ s : Γ(tateThetaLine k (2*m) m, ⊤), (SectionAction.globalAct _ β)^[m] s = s) := by
  obtain ⟨σ, hσ, -⟩ := h
  have rel := hσ.2.2.2.2
  constructor
  · exact source_order_of_induced k Q.model Q.origin m (Q.ideal_invertible he) Q.cubic
      (tateThetaLine k (2*m) m) (Q.thetaComparison he) Q.mapA _ Q.scalar_commutes.symm
      (Q.canonicalA he hζ) α m rel.1
  · exact source_order_of_induced k Q.model Q.origin m (Q.ideal_invertible he) Q.cubic
      (tateThetaLine k (2*m) m) (Q.thetaComparison he) Q.mapB _ Q.shift_commutes.symm
      (Q.canonicalB he) β m rel.2.1

#print axioms tate_orders
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

include V θ hb ζ hζ he Q in
/-- The actual arithmetic line operators, not merely their underlying
translations, have m-th power identity over the original component field. -/
lemma arithmetic_lifts_order
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β) :
    (∀ s : Γ(thetaLine k (2*m) D X x m, ⊤),
      (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.x).hom α)^[m] s = s) ∧
    (∀ s : Γ(thetaLine k (2*m) D X x m, ⊤),
      (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.y).hom β)^[m] s = s) := by
  have align := arithmetic_finite_alignment k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  obtain ⟨hA, hB⟩ := Q.tate_orders he hζ _ _ align
  constructor
  · exact SectionAction.order_of_fieldBaseChange θ (structureMap k (2*m) D X x)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m)))
      (tateMap k (2*m) D X x V θ hb) (tateMap_cartesian k (2*m) D X x V θ hb)
      (thetaLine k (2*m) D X x m) (thetaLine_invertible k (2*m) D X x m)
      (thetaLine_tateIso k (2*m) D X x V θ hb m)
      (labelTranslation k (2*m) D X x D.atlas.marking.x).hom _
      (labelTranslation_tate k (2*m) D X x V θ hb _ _ V.classifies.2.2.2.1).symm α m hA
  · exact SectionAction.order_of_fieldBaseChange θ (structureMap k (2*m) D X x)
      (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m)))
      (tateMap k (2*m) D X x V θ hb) (tateMap_cartesian k (2*m) D X x V θ hb)
      (thetaLine k (2*m) D X x m) (thetaLine_invertible k (2*m) D X x m)
      (thetaLine_tateIso k (2*m) D X x V θ hb m)
      (labelTranslation k (2*m) D X x D.atlas.marking.y).hom _
      (labelTranslation_tate k (2*m) D X x V θ hb _ _ V.classifies.2.2.2.2).symm β m hB

#print axioms arithmetic_lifts_order
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))
    (p : Y ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ p = genericStructure k M)

include hE in
lemma modelFunctional_smul (a : LaurentSeries k) (v : Γ(N, ⊤)) :
    modelFunctional k M s d E N c ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop) a) • v) =
      sc k M s d a (modelFunctional k M s d E N c v) := by
  have hscalar : E.hom.appTop (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop) a) =
      scalarAt k M ⊤ a := by
    rw [GeometricShiftLiftR0141.scalarAt_top]
    have hh := congrArg Scheme.Hom.appTop hE
    rw [Scheme.Hom.comp_appTop] at hh
    exact congrArg (fun q => q ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv a)) hh
  unfold modelFunctional
  rw [pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  change ihomGlobalSectionsEquiv _ _ (E.hom.appTop _ • _) = _
  rw [hscalar]
  unfold sc GenericThetaBasisR0140.scale
  erw [AddEquiv.symm_apply_apply]
  rfl

include hE in
lemma source_commutator_of_induced
    (fA fB : genericScheme k M ⟶ genericScheme k M) (gA gB : Y ⟶ Y)
    (hA : E.hom ≫ gA = fA ≫ E.hom) (hB : E.hom ≫ gB = fB ≫ E.hom)
    (eA : Lift k M s d fA) (eB : Lift k M s d fB)
    (α : (Scheme.Modules.pullback gA).obj N ≅ N)
    (β : (Scheme.Modules.pullback gB).obj N ≅ N) (a : LaurentSeries k)
    (hab : ∀ φ, ScaledEq k M s d a
      (act k M s d fB (inducedIdealLift k M s d hL E N c fB gB hB eB β)
        (act k M s d fA (inducedIdealLift k M s d hL E N c fA gA hA eA α) φ))
      (act k M s d fA (inducedIdealLift k M s d hL E N c fA gA hA eA α)
        (act k M s d fB (inducedIdealLift k M s d hL E N c fB gB hB eB β) φ)))
    (v : Γ(N, ⊤)) :
    SectionAction.globalAct gA α (SectionAction.globalAct gB β v) =
      (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop) a) •
        SectionAction.globalAct gB β (SectionAction.globalAct gA α v) := by
  apply (modelFunctional_bijective k M s d E N c).1
  rw [modelFunctional_smul k M s d E N c p hE]
  have hh := (scaled_iff k M s d a _ _).mp (hab (modelFunctional k M s d E N c v))
  rw [modelFunctional_act, modelFunctional_act, modelFunctional_act, modelFunctional_act] at hh
  exact hh

#print axioms modelFunctional_smul
#print axioms source_commutator_of_induced
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}

lemma fieldScalar_pull {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : c ≫ p = q ≫ Spec.map (CommRingCat.ofHom ι)) (a : F) :
    c.appTop (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) (ι a) := by
  have h := congrArg Scheme.Hom.appTop hc
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  change (p.appTop ≫ c.appTop) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a) = _
  rw [h]
  exact congrArg (fun b => q.appTop b)
    (congrArg (fun f => f a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι))).symm

lemma commutator_of_fieldBaseChange {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ N)
    (fA fB : X ⟶ X) (gA gB : Y ⟶ Y)
    (hA : c ≫ fA = gA ≫ c) (hB : c ≫ fB = gB ≫ c)
    (α : (Scheme.Modules.pullback fA).obj M ≅ M)
    (β : (Scheme.Modules.pullback fB).obj M ≅ M) (a : F)
    (hab : ∀ s : Γ(N, ⊤),
      globalAct gA (changeLine gA e (baseChangedLift c fA gA hA α))
        (globalAct gB (changeLine gB e (baseChangedLift c fB gB hB β)) s) =
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) (ι a)) •
        globalAct gB (changeLine gB e (baseChangedLift c fB gB hB β))
          (globalAct gA (changeLine gA e (baseChangedLift c fA gA hA α)) s))
    (s : Γ(M, ⊤)) :
    globalAct fA α (globalAct fB β s) =
      (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) •
        globalAct fB β (globalAct fA α s) := by
  apply fieldSectionPull_injective ι p q c hc M hM
  apply (sectionIso e).injective
  change e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection c (globalAct fA α (globalAct fB β s))) =
    e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection c
      ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) • globalAct fB β (globalAct fA α s)))
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  change _ = c.appTop _ • _
  rw [fieldScalar_pull ι p q c hc.w a]
  have hh := hab (e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection c s))
  rw [globalAct_changeLine, globalAct_baseChanged, globalAct_changeLine, globalAct_baseChanged,
    globalAct_changeLine, globalAct_baseChanged, globalAct_changeLine, globalAct_baseChanged] at hh
  exact hh

#print axioms fieldScalar_pull
#print axioms commutator_of_fieldBaseChange
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaGeometricLiftsR0141
variable {k : Type} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    {V : TateLevel k (2*m)} {ζ : kˣ} (Q : MarkedModel k m hm V ζ)
    (he : Even m) (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (α : (Scheme.Modules.pullback (tateA (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)
    (β : (Scheme.Modules.pullback (tateB (V := V))).obj (tateThetaLine k (2*m) m) ≅ tateThetaLine k (2*m) m)

lemma tate_commutator (h : Q.FiniteAlignment he hζ α β) (v : Γ(tateThetaLine k (2*m) m, ⊤)) :
    SectionAction.globalAct _ α (SectionAction.globalAct _ β v) =
      (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m))).appTop)
        (phase k (ζ^2) 1)) • SectionAction.globalAct _ β (SectionAction.globalAct _ α v) := by
  obtain ⟨σ, hσ, -⟩ := h
  have rel := hσ.2.2.2.2
  exact source_commutator_of_induced k Q.model Q.origin m (Q.ideal_invertible he) Q.cubic
    (tateThetaLine k (2*m) m) (Q.thetaComparison he) _ Q.cubic_over
    Q.mapA Q.mapB _ _ Q.scalar_commutes.symm Q.shift_commutes.symm
    (Q.canonicalA he hζ) (Q.canonicalB he) α β (phase k (ζ^2) 1) rel.2.2.1 v

#print axioms tate_commutator
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGeometricLiftsR0141

lemma component_field_constants (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space) (V : DiskTest k L D X)
    (θ : (Component k L D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k L D X x = V.base) :
    θ.comp (AlgebraicCurve.baseToFunctionField (projection k L D X x)) =
      algebraMap k (LaurentSeries k) := by
  have he : CommRingCat.ofHom (θ.comp (AlgebraicCurve.baseToFunctionField (projection k L D X x))) =
      CommRingCat.ofHom (algebraMap k (LaurentSeries k)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp,
      ← GeometricComponentCuspBoundR0184.componentGenericOpen_over,
      ← Category.assoc, hb]
    exact V.classifies.1
  exact congrArg CommRingCat.Hom.hom he

variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

include hb in
lemma component_root_image :
    θ (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) ((ζ : k)^2)) =
      phase k (ζ^2) 1 := by
  have h := congrArg (fun f : k →+* LaurentSeries k => f ((ζ : k)^2))
    (component_field_constants k (2*m) D X x V θ hb)
  change θ (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) ((ζ : k)^2)) =
    algebraMap k (LaurentSeries k) ((ζ : k)^2) at h
  rw [h]
  simp only [phase, pow_one, Units.val_pow_eq_pow_val, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

include V θ hb ζ hζ he Q in
/-- The commutator has exactly the prescribed primitive-root phase, expressed
using the structural scalar map of the original component field. -/
lemma arithmetic_lifts_commutator
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β)
    (s : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.x).hom α
      (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.y).hom β s) =
      (((Scheme.ΓSpecIso (CommRingCat.of (Component k (2*m) D X x).functionField)).inv ≫
        (structureMap k (2*m) D X x).appTop)
          (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) ((ζ : k)^2))) •
      SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.y).hom β
        (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.x).hom α s) := by
  have align := arithmetic_finite_alignment k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  have ht := Q.tate_commutator he hζ _ _ align
  apply SectionAction.commutator_of_fieldBaseChange θ (structureMap k (2*m) D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m)))
    (tateMap k (2*m) D X x V θ hb) (tateMap_cartesian k (2*m) D X x V θ hb)
    (thetaLine k (2*m) D X x m) (thetaLine_invertible k (2*m) D X x m)
    (thetaLine_tateIso k (2*m) D X x V θ hb m)
    (labelTranslation k (2*m) D X x D.atlas.marking.x).hom
    (labelTranslation k (2*m) D X x D.atlas.marking.y).hom _ _
    (labelTranslation_tate k (2*m) D X x V θ hb _ _ V.classifies.2.2.2.1).symm
    (labelTranslation_tate k (2*m) D X x V θ hb _ _ V.classifies.2.2.2.2).symm α β
    (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) ((ζ : k)^2))
  intro v
  rw [component_root_image k m D X x V θ hb ζ]
  exact ht v

#print axioms component_field_constants
#print axioms component_root_image
#print axioms arithmetic_lifts_commutator
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation
open Polynomial
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

lemma finite_order_has_eigenvalue [Module.Finite F V] [Nontrivial V]
    (A : Module.End F V) {m : ℕ} (hm : 0 < m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (hA : A^m = 1) : ∃ a, A.HasEigenvalue a := by
  have hd : minpoly F A ∣ (X^m - C 1 : F[X]) :=
    minpoly.dvd F A (by simp [hA])
  have hs := (X_pow_sub_one_splits hζ).of_dvd (X_pow_sub_C_ne_zero hm 1) hd
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos (Algebra.IsIntegral.isIntegral A)))
  exact ⟨a, Module.End.hasEigenvalue_of_isRoot ha⟩

lemma pow_apply_nonzero (B : Module.End F V) {m : ℕ} (hm : 0 < m)
    (hB : B^m = 1) {v : V} (hv : v ≠ 0) (n : ℕ) : (B^n) v ≠ 0 := by
  have hinj : Function.Injective B := by
    apply Function.Injective.of_comp (f := (B^(m-1) : Module.End F V))
    intro x y h
    have hxy : (B^m) x = (B^m) y := by
      simpa only [Function.comp_apply, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel hm] using h
    simpa only [hB, Module.End.one_apply] using hxy
  intro h
  apply hv
  apply hinj.iterate n
  simpa only [← Module.End.pow_apply, map_zero] using h

lemma eigen_pow_shift (A B : Module.End F V) (ζ a : F)
    (hab : ∀ v, A (B v) = ζ • B (A v)) {v : V} (hv : A v = a • v) (n : ℕ) :
    A ((B^n) v) = (ζ^n * a) • (B^n) v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hab, ih, map_smul, smul_smul]
    rw [pow_succ']
    simp only [mul_assoc]

lemma exists_fixed_vector [Module.Finite F V] [Nontrivial V]
    (A B : Module.End F V) {m : ℕ} (hm : 0 < m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (hA : A^m = 1) (hB : B^m = 1)
    (hab : ∀ v, A (B v) = ζ • B (A v)) : ∃ v : V, v ≠ 0 ∧ A v = v := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨a, ha⟩ := finite_order_has_eigenvalue A hm hζ hA
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have hev : A v = a • v := Module.End.mem_eigenspace_iff.mp hv.1
  have ham : a^m = 1 := by
    have heq := Module.End.HasEigenvector.pow_apply hv m
    rw [hA, Module.End.one_apply] at heq
    exact (smul_left_injective F hv.2) (heq.symm.trans (one_smul F v).symm)
  have ha0 : a ≠ 0 := by intro h; simp [h, Nat.ne_of_gt hm] at ham
  obtain ⟨j, _, hj⟩ := hζ.eq_pow_of_pow_eq_one (show (a⁻¹)^m = 1 by rw [inv_pow, ham, inv_one])
  refine ⟨(B^j) v, pow_apply_nonzero B hm hB hv.2 j, ?_⟩
  rw [eigen_pow_shift A B ζ a hab hev j, hj, inv_mul_cancel₀ ha0, one_smul]

lemma orbit_linearIndependent (A B : Module.End F V) {m : ℕ} (hm : 0 < m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (hB : B^m = 1)
    (hab : ∀ v, A (B v) = ζ • B (A v)) {v : V} (hv : v ≠ 0) (hAv : A v = v) :
    LinearIndependent F (fun i : Fin m => (B^i.val) v) := by
  apply A.eigenvectors_linearIndependent' (fun i : Fin m => ζ^i.val)
    (fun i j h => Fin.ext (hζ.pow_inj i.isLt j.isLt h))
  intro i
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, pow_apply_nonzero B hm hB hv i.val⟩
  simpa only [mul_one] using eigen_pow_shift A B ζ 1 hab (hAv.trans (one_smul F v).symm) i.val

lemma exists_equivariant_basis [Module.Finite F V]
    (A B : Module.End F V) {m : ℕ} (hm : 0 < m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (hdim : Module.finrank F V = m)
    (hA : A^m = 1) (hB : B^m = 1) (hab : ∀ v, A (B v) = ζ • B (A v)) :
    ∃ b : Module.Basis (Fin m) F V,
      (∀ i, A (b i) = ζ^i.val • b i) ∧
      (∀ i, B (b i) = b ⟨(i.val+1)%m, Nat.mod_lt _ hm⟩) := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (hdim ▸ hm)
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨v, hv, hAv⟩ := exists_fixed_vector A B hm hζ hA hB hab
  let b : Module.Basis (Fin m) F V :=
    basisOfLinearIndependentOfCardEqFinrank' (fun i : Fin m => (B^i.val) v)
      (orbit_linearIndependent A B hm hζ hB hab hv hAv) (by simpa using hdim.symm)
  have hb (i : Fin m) : b i = (B^i.val) v := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hb]
    simpa only [mul_one] using eigen_pow_shift A B ζ 1 hab (hAv.trans (one_smul F v).symm) i.val
  · intro i
    rw [hb, hb]
    rw [← Module.End.mul_apply, ← pow_succ']
    change (B^(i.val+1)) v = (B^((i.val+1)%m)) v
    by_cases hi : i.val+1 < m
    · rw [Nat.mod_eq_of_lt hi]
    · have hi' : i.val+1 = m := by omega
      simp only [hi', Nat.mod_self, hB, pow_zero]

lemma sign_order (A : Module.End F V) {m : ℕ} (he : Even m) (hA : A^m = 1)
    (a : F) (ha : a^2 = 1) : (a • A)^m = 1 := by
  have ham : a^m = 1 := by
    obtain ⟨n, rfl⟩ := he
    rw [← two_mul, pow_mul, ha, one_pow]
  rw [_root_.smul_pow, ham, hA, one_smul]

lemma scaled_commutator (A B : Module.End F V) (ζ a b : F)
    (hab : ∀ v, A (B v) = ζ • B (A v)) (v : V) :
    (a • A) ((b • B) v) = ζ • (b • B) ((a • A) v) := by
  simp only [LinearMap.smul_apply, map_smul, hab, smul_smul]
  congr 1
  ring

#print axioms sign_order
#print axioms scaled_commutator
#print axioms finite_order_has_eigenvalue
#print axioms exists_fixed_vector
#print axioms exists_equivariant_basis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

include V θ hb hζ he Q in
/-- A Schrödinger basis exists over the original component function field,
including after either constant finite sign correction. -/
lemma arithmetic_equivariant_basis
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β)
    (a b : k) (ha : a^2 = 1) (hb' : b^2 = 1) :
    let F := (Component k (2*m) D X x).functionField
    let ι := AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x)
    letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
    ∃ e : Module.Basis (Fin m) F Γ(thetaLine k (2*m) D X x m, ⊤),
      (∀ i, (ι a) • thetaSectionOperator k (2*m) D X x m D.atlas.marking.x α (e i) =
        (ι ((ζ : k)^2))^i.val • e i) ∧
      (∀ i, (ι b) • thetaSectionOperator k (2*m) D X x m D.atlas.marking.y β (e i) =
        e ⟨(i.val+1)%m, Nat.mod_lt _ hm⟩) := by
  let F := (Component k (2*m) D X x).functionField
  let ι := AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x)
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  letI : Module.Finite F Γ(thetaLine k (2*m) D X x m, ⊤) := by
    have h := thetaSections_finite k (2*m) D X x m
    dsimp only at h
    erw [Scheme.Hom.appLE_eq_app] at h
    exact h
  let A := thetaSectionOperator k (2*m) D X x m D.atlas.marking.x α
  let B := thetaSectionOperator k (2*m) D X x m D.atlas.marking.y β
  have hroot : IsPrimitiveRoot (ι ((ζ : k)^2)) m :=
    (show IsPrimitiveRoot ((ζ : k)^2) m from LocalTheta.MarkedModel.root_half (hm := hm) hζ).map_of_injective ι.injective
  obtain ⟨hA, hB⟩ := arithmetic_lifts_order k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  have hAp : A^m = 1 := by
    ext s
    exact (Module.End.pow_apply A m s).trans (hA s)
  have hBp : B^m = 1 := by
    ext s
    exact (Module.End.pow_apply B m s).trans (hB s)
  have hAB : ∀ s, A (B s) = (ι ((ζ : k)^2)) • B (A s) :=
    arithmetic_lifts_commutator k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  have hia : (ι a)^2 = 1 := by rw [← map_pow, ha, map_one]
  have hib : (ι b)^2 = 1 := by rw [← map_pow, hb', map_one]
  exact Representation.exists_equivariant_basis ((ι a) • A) ((ι b) • B) hm hroot
    (by
      have h := thetaSections_rank k (2*m) D X x m hm
      dsimp only at h
      erw [Scheme.Hom.appLE_eq_app] at h
      exact h)
    (Representation.sign_order A he hAp _ hia)
    (Representation.sign_order B he hBp _ hib)
    (Representation.scaled_commutator A B _ _ _ hAB)

#print axioms arithmetic_equivariant_basis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
variable {X Y : Scheme}

def sectionIsoLinear {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    {M N : X.Modules} (e : M ≅ N) :
    letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
    letI : Module F Γ(N, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
    Γ(M, ⊤) ≃ₗ[F] Γ(N, ⊤) := by
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  letI : Module F Γ(N, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  refine { sectionIso e with map_add' := ?_, map_smul' := ?_ }
  · intro a b
    exact (e.hom.app ⊤).hom.map_add a b
  · intro a b
    exact Scheme.Modules.Hom.app_smul e.hom (algebraMap F Γ(X, ⊤) a) b

lemma fieldSectionBasis {F K : Type} [Field F] [Field K] (ι : F →+* K)
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of K)) (c : Y ⟶ X)
    (hc : IsPullback c q p (Spec.map (CommRingCat.ofHom ι)))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ N) {n : ℕ} :
    letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
    letI : Module K Γ(N, ⊤) := Module.compHom _ (algebraMap K Γ(Y, ⊤))
    ∀ b : Module.Basis (Fin n) F Γ(M, ⊤),
      ∃ b' : Module.Basis (Fin n) K Γ(N, ⊤),
        ∀ i, b' i = e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection c (b i)) := by
  letI : Algebra F K := ι.toAlgebra
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Module K Γ(N, ⊤) := Module.compHom _ (algebraMap K Γ(Y, ⊤))
  letI : Module K Γ((Scheme.Modules.pullback c).obj M, ⊤) := Module.compHom _ (algebraMap K Γ(Y, ⊤))
  intro b
  obtain ⟨β, hβ⟩ := fieldSections_baseChange ι p q c hc M hM
  refine ⟨((b.baseChange K).map β).map (sectionIsoLinear q e), ?_⟩
  intro i
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hβ]
  rfl

#print axioms sectionIsoLinear
#print axioms fieldSectionBasis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))
    (p : Y ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ p = genericStructure k M)

local instance : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

lemma modelFunctional_zero : modelFunctional k M s d E N c 0 = 0 := by
  simp only [modelFunctional, pullbackLocalSection_zero, map_zero]

lemma modelFunctional_add (v w : Γ(N, ⊤)) :
    modelFunctional k M s d E N c (v+w) =
      modelFunctional k M s d E N c v + modelFunctional k M s d E N c w := by
  simp only [modelFunctional, pullbackLocalSection_add, map_add]

lemma modelFunctional_sum {ι : Type} (a : Finset ι) (v : ι → Γ(N, ⊤)) :
    modelFunctional k M s d E N c (∑ i ∈ a, v i) =
      ∑ i ∈ a, modelFunctional k M s d E N c (v i) := by
  classical
  induction a using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, modelFunctional_zero]
  | @insert i a hi ih => simp only [Finset.sum_insert hi, modelFunctional_add, ih]

include hE in
lemma modelFunctional_combination (n : ℕ) (b : Fin n → Γ(N, ⊤)) (a : Fin n → LaurentSeries k) :
    modelFunctional k M s d E N c
      (∑ i, ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop) (a i))) • b i) =
      GeometricIntertwinerRigidityR0141.combine k M s d n
        (fun i => modelFunctional k M s d E N c (b i)) a := by
  rw [modelFunctional_sum]
  unfold GeometricIntertwinerRigidityR0141.combine
  apply Finset.sum_congr rfl
  intro i _
  exact modelFunctional_smul k M s d E N c p hE (a i) (b i)

include hE in
lemma modelFunctional_hasBasis (n : ℕ) :
    letI : Algebra (LaurentSeries k) Γ(Y, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop).hom.toAlgebra
    letI : Module (LaurentSeries k) Γ(N, ⊤) := Module.compHom _ (algebraMap (LaurentSeries k) Γ(Y, ⊤))
    ∀ b : Module.Basis (Fin n) (LaurentSeries k) Γ(N, ⊤),
      HasBasis k M s d n (fun i => modelFunctional k M s d E N c (b i)) := by
  letI : Algebra (LaurentSeries k) Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ(N, ⊤) := Module.compHom _ (algebraMap (LaurentSeries k) Γ(Y, ⊤))
  intro b φ
  obtain ⟨v, rfl⟩ := (modelFunctional_bijective k M s d E N c).2 φ
  have hc (a : Fin n → LaurentSeries k) :
      modelFunctional k M s d E N c (b.equivFun.symm a) =
        GeometricIntertwinerRigidityR0141.combine k M s d n
          (fun i => modelFunctional k M s d E N c (b i)) a := by
    rw [Module.Basis.equivFun_symm_apply]
    exact modelFunctional_combination k M s d E N c p hE n b a
  refine ⟨b.equivFun v, ?_, ?_⟩
  · apply (GeometricIntertwinerRigidityR0141.combines_iff k M s d n _ _ _).mpr
    rw [← hc, b.equivFun.symm_apply_apply]
  · intro a ha
    have hh := (GeometricIntertwinerRigidityR0141.combines_iff k M s d n _ _ _).mp ha
    rw [← hc] at hh
    have heq := (modelFunctional_bijective k M s d E N c).1 hh
    exact (b.equivFun.apply_symm_apply a).symm.trans (congrArg b.equivFun heq).symm

#print axioms modelFunctional_hasBasis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (he : Even m) (Q : LocalTheta.MarkedModel k m hm V.level ζ)

def arithmeticTateSection (v : Γ(thetaLine k (2*m) D X x m, ⊤)) : Γ(tateThetaLine k (2*m) m, ⊤) :=
  (thetaLine_tateIso k (2*m) D X x V θ hb m).hom.app ⊤
    (Scheme.Modules.pullbackLocalSection (tateMap k (2*m) D X x V θ hb) v)

def arithmeticModelSection (v : Γ(thetaLine k (2*m) D X x m, ⊤)) : GenericDual k Q.model Q.origin m :=
  LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic (tateThetaLine k (2*m) m)
    (Q.thetaComparison he) (arithmeticTateSection k m D X x V θ hb v)

lemma arithmeticTateSection_smul (a : (Component k (2*m) D X x).functionField)
    (v : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    arithmeticTateSection k m D X x V θ hb
      ((((Scheme.ΓSpecIso (CommRingCat.of (Component k (2*m) D X x).functionField)).inv ≫
        (structureMap k (2*m) D X x).appTop) a) • v) =
      (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
        (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m))).appTop) (θ a)) •
        arithmeticTateSection k m D X x V θ hb v := by
  unfold arithmeticTateSection
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  change (tateMap k (2*m) D X x V θ hb).appTop _ • _ = _
  rw [SectionAction.fieldScalar_pull θ (structureMap k (2*m) D X x)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m)))
    (tateMap k (2*m) D X x V θ hb) (tateMap_cartesian k (2*m) D X x V θ hb).w]

lemma arithmeticModelSection_smul (a : (Component k (2*m) D X x).functionField)
    (v : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    arithmeticModelSection k m hm D X x V θ hb ζ he Q
      ((((Scheme.ΓSpecIso (CommRingCat.of (Component k (2*m) D X x).functionField)).inv ≫
        (structureMap k (2*m) D X x).appTop) a) • v) =
      sc k Q.model Q.origin m (θ a) (arithmeticModelSection k m hm D X x V θ hb ζ he Q v) := by
  unfold arithmeticModelSection
  rw [arithmeticTateSection_smul]
  exact LocalTheta.modelFunctional_smul k Q.model Q.origin m Q.cubic _ (Q.thetaComparison he)
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m))) Q.cubic_over _ _

lemma arithmeticTateSection_act
    (P : SchemeHomOver (𝟙 _) D.atlas.descent.family.projection)
    (P' : SchemeHomOver (𝟙 _) (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m))))
    (hP : P'.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ P.val)
    (α : LabelThetaLift k (2*m) D X x m P)
    (v : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    SectionAction.globalAct _ (tateArithmeticLabelLift k (2*m) D X x V θ hb m P P' hP α)
      (arithmeticTateSection k m D X x V θ hb v) =
      arithmeticTateSection k m D X x V θ hb
        (SectionAction.globalAct (labelTranslation k (2*m) D X x P).hom α v) := by
  unfold arithmeticTateSection tateArithmeticLabelLift
  rw [SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]

lemma arithmeticModelSection_basis :
    let F := (Component k (2*m) D X x).functionField
    letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
    ∀ b : Module.Basis (Fin m) F Γ(thetaLine k (2*m) D X x m, ⊤),
      HasBasis k Q.model Q.origin m m
        (fun i => arithmeticModelSection k m hm D X x V θ hb ζ he Q (b i)) := by
  let F := (Component k (2*m) D X x).functionField
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  let p := ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (TateCurve k (2*m))
  letI : Algebra (LaurentSeries k) Γ(ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k (2*m)), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ p.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ(tateThetaLine k (2*m) m, ⊤) :=
    Module.compHom _ (algebraMap (LaurentSeries k) Γ(ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (TateCurve k (2*m)), ⊤))
  dsimp only
  intro b
  obtain ⟨b', hb'⟩ := SectionAction.fieldSectionBasis θ (structureMap k (2*m) D X x) p
    (tateMap k (2*m) D X x V θ hb) (tateMap_cartesian k (2*m) D X x V θ hb)
    _ (thetaLine_invertible k (2*m) D X x m) (thetaLine_tateIso k (2*m) D X x V θ hb m) b
  have h := LocalTheta.modelFunctional_hasBasis k Q.model Q.origin m Q.cubic _
    (Q.thetaComparison he) p Q.cubic_over m b'
  simpa only [hb', arithmeticModelSection, arithmeticTateSection] using h

#print axioms arithmeticModelSection_smul
#print axioms arithmeticTateSection_act
#print axioms arithmeticModelSection_basis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

lemma arithmeticModelSection_actA (v : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    act k Q.model Q.origin m Q.mapA
      (Q.inducedA he hζ (arithmeticModelA k m D X x V θ hb α))
        (arithmeticModelSection k m hm D X x V θ hb ζ he Q v) =
      arithmeticModelSection k m hm D X x V θ hb ζ he Q
        (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.x).hom α v) := by
  unfold arithmeticModelSection LocalTheta.MarkedModel.inducedA
  rw [LocalTheta.modelFunctional_act]
  rw [arithmeticModelA, arithmeticTateSection_act]

lemma arithmeticModelSection_actB (v : Γ(thetaLine k (2*m) D X x m, ⊤)) :
    act k Q.model Q.origin m Q.mapB
      (Q.inducedB he (arithmeticModelB k m D X x V θ hb β))
        (arithmeticModelSection k m hm D X x V θ hb ζ he Q v) =
      arithmeticModelSection k m hm D X x V θ hb ζ he Q
        (SectionAction.globalAct (labelTranslation k (2*m) D X x D.atlas.marking.y).hom β v) := by
  unfold arithmeticModelSection LocalTheta.MarkedModel.inducedB
  rw [LocalTheta.modelFunctional_act]
  rw [arithmeticModelB, arithmeticTateSection_act]

include hb in
lemma component_phase_image (n : ℕ) :
    θ ((AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) ((ζ : k)^2))^n) =
      phase k (ζ^2) n := by
  rw [map_pow, component_root_image k m D X x V θ hb ζ]
  simp only [phase, pow_one, ← map_pow]

lemma arithmeticModelSection_eigen_cyclic :
    let F := (Component k (2*m) D X x).functionField
    let ι := AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x)
    letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
    ∀ b : Module.Basis (Fin m) F Γ(thetaLine k (2*m) D X x m, ⊤),
      (∀ i, thetaSectionOperator k (2*m) D X x m D.atlas.marking.x α (b i) =
        (ι ((ζ : k)^2))^i.val • b i) →
      (∀ i, thetaSectionOperator k (2*m) D X x m D.atlas.marking.y β (b i) =
        b ⟨(i.val+1)%m, Nat.mod_lt _ hm⟩) →
      Eigen k Q.model Q.origin m m (ζ^2) Q.mapA
        (Q.inducedA he hζ (arithmeticModelA k m D X x V θ hb α))
          (fun i => arithmeticModelSection k m hm D X x V θ hb ζ he Q (b i)) ∧
      Cyclic k Q.model Q.origin m m hm Q.mapB
        (Q.inducedB he (arithmeticModelB k m D X x V θ hb β))
          (fun i => arithmeticModelSection k m hm D X x V θ hb ζ he Q (b i)) := by
  let F := (Component k (2*m) D X x).functionField
  let ι := AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x)
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  dsimp only
  intro b hA hB
  constructor
  · intro i
    apply (scaled_iff k Q.model Q.origin m _ _ _).mpr
    rw [arithmeticModelSection_actA]
    change arithmeticModelSection k m hm D X x V θ hb ζ he Q
      (thetaSectionOperator k (2*m) D X x m D.atlas.marking.x α (b i)) = _
    rw [hA]
    erw [arithmeticModelSection_smul]
    rw [component_phase_image k m D X x V θ hb ζ]
  · intro i
    rw [arithmeticModelSection_actB]
    exact congrArg (arithmeticModelSection k m hm D X x V θ hb ζ he Q) (hB i)

#print axioms arithmeticModelSection_actA
#print axioms arithmeticModelSection_actB
#print axioms arithmeticModelSection_eigen_cyclic
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
open ArithmeticThetaSymmetricMarkingR0142
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)

include hb in
lemma component_constant_image (a : k) :
    θ (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) a) = constant k a := by
  have h := congrArg (fun f : k →+* LaurentSeries k => f a)
    (component_field_constants k (2*m) D X x V θ hb)
  change θ (AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x) a) =
    algebraMap k (LaurentSeries k) a at h
  rw [h]
  simp only [constant, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
    PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

include hζ in
lemma arithmetic_aligned_basis
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β) :
    let F := (Component k (2*m) D X x).functionField
    letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
    ∃ b : Module.Basis (Fin m) F Γ(thetaLine k (2*m) D X x m, ⊤),
      Nonempty (GenericFrame k Q.model Q.origin Q.markedOrigin.1 m) ∧
      ∀ frame : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m,
        genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
          (arithmeticModelSection k m hm D X x V θ hb ζ he Q (b ⟨0, hm⟩)) ≠ 0 ∧
        ∀ i : Fin m,
          genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
            (arithmeticModelSection k m hm D X x V θ hb ζ he Q (b i)) /
          genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
            (arithmeticModelSection k m hm D X x V θ hb ζ he Q (b ⟨0, hm⟩)) =
          algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m i) /
          algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ⟨0, hm⟩) := by
  let F := (Component k (2*m) D X x).functionField
  let ι := AlgebraicCurve.baseToFunctionField (projection k (2*m) D X x)
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  obtain ⟨σ, hσ, _⟩ := arithmetic_finite_alignment k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  obtain ⟨b, hA, hB⟩ := arithmetic_equivariant_basis k m hm D X x V θ hb ζ hζ he Q α β hα hβ
    σ.1 σ.2 hσ.1 hσ.2.1
  let B := fun i : Fin m => arithmeticModelSection k m hm D X x V θ hb ζ he Q (b i)
  have hAb : Eigen k Q.model Q.origin m m (ζ^2) Q.mapA (Q.canonicalA he hζ) B := by
    intro i
    apply (scaled_iff k Q.model Q.origin m _ _ _).mpr
    rw [AlignedMarkingProjectiveValuesR0142.act_scaled_back k Q.model Q.origin m Q.mapA
      (Q.canonicalA he hζ) _ σ.1 hσ.1 hσ.2.2.1]
    dsimp only [B]
    rw [arithmeticModelSection_actA]
    rw [← component_constant_image k m D X x V θ hb σ.1]
    rw [← arithmeticModelSection_smul]
    change arithmeticModelSection k m hm D X x V θ hb ζ he Q
      ((ι σ.1) • thetaSectionOperator k (2*m) D X x m D.atlas.marking.x α (b i)) = _
    rw [hA]
    erw [arithmeticModelSection_smul]
    rw [component_phase_image k m D X x V θ hb ζ]
  have hBb : Cyclic k Q.model Q.origin m m hm Q.mapB (Q.canonicalB he) B := by
    intro i
    rw [AlignedMarkingProjectiveValuesR0142.act_scaled_back k Q.model Q.origin m Q.mapB
      (Q.canonicalB he) _ σ.2 hσ.2.1 hσ.2.2.2.1]
    dsimp only [B]
    rw [arithmeticModelSection_actB]
    rw [← component_constant_image k m D X x V θ hb σ.2]
    rw [← arithmeticModelSection_smul]
    exact congrArg (arithmeticModelSection k m hm D X x V θ hb ζ he Q) (hB i)
  refine ⟨b, ?_⟩
  exact geometric_basis_projective_values k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2) (LocalTheta.MarkedModel.root_half (hm := hm) hζ)
    (Q.canonicalA he hζ) (Q.canonicalB he) (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he)
    B (arithmeticModelSection_basis k m hm D X x V θ hb ζ he Q b) hAb hBb

#print axioms arithmetic_aligned_basis
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
variable {X Y Z : Scheme}

lemma pullbackSection_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (v : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
      (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g v)) =
        Scheme.Modules.pullbackLocalSection (f ≫ g) v := by
  apply (globalSectionsEquiv _).injective
  change fromSection _ _ = fromSection _ _
  erw [fromSection_map, ← pull_fromSection, ← pull_fromSection, pull_comp, pull_fromSection]

lemma pullbackSection_comp_zero_iff (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (v : Γ(M, ⊤)) :
    Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g v) = 0 ↔
      Scheme.Modules.pullbackLocalSection (f ≫ g) v = 0 := by
  have h := pullbackSection_comp f g M v
  have inj := (sectionIso ((Scheme.Modules.pullbackComp f g).app M)).injective
  constructor
  · intro hz
    rw [hz, map_zero] at h
    exact h.symm
  · intro hz
    apply inj
    change ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤ _ =
      ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤ 0
    rw [h, hz, map_zero]

lemma pullbackSection_square_zero {S T : Scheme} (o : S ⟶ X) (t : T ⟶ Y)
    (c : Y ⟶ X) (b : T ⟶ S) (h : t ≫ c = b ≫ o)
    (M : X.Modules) (v : Γ(M, ⊤))
    (hv : Scheme.Modules.pullbackLocalSection o v = 0) :
    Scheme.Modules.pullbackLocalSection t (Scheme.Modules.pullbackLocalSection c v) = 0 := by
  apply (pullbackSection_comp_zero_iff t c M v).mpr
  rw [h]
  apply (pullbackSection_comp_zero_iff b o M v).mp
  rw [hv, Scheme.Modules.pullbackLocalSection_zero]

def pointValue {F : Type} [Field F] (o : Spec (CommRingCat.of F) ⟶ X)
    (M : X.Modules)
    (e : (Scheme.Modules.pullback o).obj M ≅ (SheafOfModules.unit (Spec (CommRingCat.of F)).ringCatSheaf : (Spec (CommRingCat.of F)).Modules))
    (v : Γ(M, ⊤)) : F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    (e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection o v))

lemma pointValue_zero_iff {F : Type} [Field F] (o : Spec (CommRingCat.of F) ⟶ X)
    (M : X.Modules)
    (e : (Scheme.Modules.pullback o).obj M ≅ (SheafOfModules.unit (Spec (CommRingCat.of F)).ringCatSheaf : (Spec (CommRingCat.of F)).Modules))
    (v : Γ(M, ⊤)) : pointValue o M e v = 0 ↔ Scheme.Modules.pullbackLocalSection o v = 0 := by
  unfold pointValue
  constructor
  · intro h
    apply (sectionIso e).injective
    apply (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom (e.hom.app ⊤ _) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom (e.hom.app ⊤ 0)
    rw [h, map_zero, map_zero]
  · intro h
    rw [h, map_zero, map_zero]

#print axioms pullbackSection_square_zero
#print axioms pointValue_zero_iff
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 GenericDualLocalizationR0140
open ArithmeticThetaPolygonCartierR0133
variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (d : ℕ)

lemma genericValue_dualSection_zero (e : GenericFrame k M s hs d)
    (v : Γ(Scheme.Modules.dual (genericPower k M s d), ⊤))
    (hv : pullbackLocalSection (genericPoint k M s hs) v = 0) :
    genericValue k M s hs d e (ihomGlobalSectionsEquiv _ _ v) = 0 := by
  have h := dualComparison_global (genericPoint k M s hs) (genericPower k M s d) v
  rw [hv, map_zero, map_zero] at h
  unfold genericValue
  erw [← h, CategoryTheory.Limits.comp_zero]
  change (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom 0 = 0
  exact map_zero _

#print axioms genericValue_dualSection_zero
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction
open CategoryTheory AlgebraicGeometry
variable {X : Scheme}

def pointValueLinear {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    (o : Spec (CommRingCat.of F) ⟶ X) (ho : o ≫ p = 𝟙 _)
    (M : X.Modules)
    (e : (Scheme.Modules.pullback o).obj M ≅ (SheafOfModules.unit (Spec (CommRingCat.of F)).ringCatSheaf : (Spec (CommRingCat.of F)).Modules)) :
    letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
    letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
    Γ(M, ⊤) →ₗ[F] F := by
  letI : Algebra F Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop).hom.toAlgebra
  letI : Module F Γ(M, ⊤) := Module.compHom _ (algebraMap F Γ(X, ⊤))
  refine { toFun := pointValue o M e, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    simp only [pointValue, Scheme.Modules.pullbackLocalSection_add, map_add]
  · intro a v
    have hs : o.appTop (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) =
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv a := by
      change (p.appTop ≫ o.appTop) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a) = _
      rw [← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
      rfl
    change pointValue o M e ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) a) • v) =
      a * pointValue o M e v
    unfold pointValue
    rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom (o.appTop _ * _) = _
    rw [hs, map_mul]
    erw [CommRingCat.hom_inv_apply]

#print axioms pointValueLinear
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (d : ℕ)
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))

lemma genericValue_modelFunctional_zero (frame : GenericFrame k M s hs d) (v : Γ(N, ⊤))
    (hv : pullbackLocalSection (genericPoint k M s hs ≫ E.hom) v = 0) :
    genericValue k M s hs d frame (modelFunctional k M s d E N c v) = 0 := by
  apply genericValue_dualSection_zero
  rw [pullbackLocalSection_app]
  rw [(SectionAction.pullbackSection_comp_zero_iff (genericPoint k M s hs) E.hom N v).mpr hv, map_zero]

#print axioms genericValue_modelFunctional_zero
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaGenericEvaluationR0140
variable (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (d : ℕ)
local instance : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

lemma genericValue_add (frame : GenericFrame k M s hs d) (φ ψ : GenericDual k M s d) :
    genericValue k M s hs d frame (φ+ψ) = genericValue k M s hs d frame φ +
      genericValue k M s hs d frame ψ := by
  unfold genericValue
  erw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, Scheme.Modules.Hom.add_app]
  exact (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom.hom.map_add _ _

#print axioms genericValue_add
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
variable (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (he : Even m) (Q : LocalTheta.MarkedModel k m hm V.level ζ)

lemma arithmeticModelValue_zero
    (frame : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m)
    (v : Γ(thetaLine k (2*m) D X x m, ⊤))
    (hv : SectionAction.pointValue (origin k (2*m) D X x) (thetaLine k (2*m) D X x m)
      (thetaRigidification k (2*m) D X x m hm) v = 0) :
    genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
      (arithmeticModelSection k m hm D X x V θ hb ζ he Q v) = 0 := by
  have hz := (SectionAction.pointValue_zero_iff _ _ _ v).mp hv
  apply LocalTheta.genericValue_modelFunctional_zero
  unfold arithmeticTateSection
  rw [Scheme.Modules.pullbackLocalSection_app]
  have hsq : (genericPoint k Q.model Q.origin Q.markedOrigin.1 ≫ Q.cubic.hom) ≫
      tateMap k (2*m) D X x V θ hb =
      Spec.map (CommRingCat.ofHom θ) ≫ origin k (2*m) D X x := by
    rw [Q.cubic_origin, tateMap_origin]
  have hzero := SectionAction.pullbackSection_square_zero (origin k (2*m) D X x)
    (genericPoint k Q.model Q.origin Q.markedOrigin.1 ≫ Q.cubic.hom)
    (tateMap k (2*m) D X x V θ hb) (Spec.map (CommRingCat.ofHom θ)) hsq
    (thetaLine k (2*m) D X x m) v hz
  rw [hzero, map_zero]

def arithmeticModelValueLinear
    (frame : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m) :
    let F := (Component k (2*m) D X x).functionField
    letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
    letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
      Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
    Γ(thetaLine k (2*m) D X x m, ⊤) →ₛₗ[θ] LaurentSeries k := by
  let F := (Component k (2*m) D X x).functionField
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  refine { toFun := (fun v => genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
      (arithmeticModelSection k m hm D X x V θ hb ζ he Q v)), map_add' := ?_, map_smul' := ?_ }
  · intro v w
    simp only [arithmeticModelSection, arithmeticTateSection, Scheme.Modules.pullbackLocalSection_add,
      map_add, LocalTheta.modelFunctional_add, LocalTheta.genericValue_add]
  · intro a v
    change genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
      (arithmeticModelSection k m hm D X x V θ hb ζ he Q
        ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop) a) • v)) = _
    rw [arithmeticModelSection_smul]
    exact GeometricBasisProjectiveValuesR0141.value_scaled k Q.model Q.origin Q.markedOrigin.1 m frame
      (θ a) _ _ ((scaled_iff k Q.model Q.origin m _ _ _).mpr rfl)

#print axioms arithmeticModelValue_zero
#print axioms arithmeticModelValueLinear
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation
variable {F K V : Type*} [Field F] [Field K] [AddCommGroup V] [Module F V]

/-- A semilinear evaluation that factors through a one-dimensional arithmetic
fiber gives quotients in the original field. No choice of local frame remains. -/
lemma quotient_of_kernel (θ : F →+* K) (f : V →ₗ[F] F)
    (g : V →ₛₗ[θ] K) (hker : ∀ v, f v = 0 → g v = 0)
    (u v : V) (hu : g u ≠ 0) : f u ≠ 0 ∧ θ (f v / f u) = g v / g u := by
  have hfu : f u ≠ 0 := fun h => hu (hker u h)
  have hzero : f ((f u) • v - (f v) • u) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    exact sub_eq_zero.mpr (mul_comm _ _)
  have h := hker _ hzero
  simp only [map_sub, map_smulₛₗ, smul_eq_mul, sub_eq_zero] at h
  refine ⟨hfu, ?_⟩
  rw [map_div₀]
  apply (div_eq_div_iff ((map_ne_zero_iff θ θ.injective).mpr hfu) hu).mpr
  exact h.symm.trans (mul_comm _ _)

#print axioms quotient_of_kernel
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation

namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141

lemma exact_unary_field_range (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (x : X.space)
    (V : DiskTest k (2*m) D X)
    (θ : (Component k (2*m) D X x).functionField →+* LaurentSeries k)
    (hb : Spec.map (CommRingCat.ofHom θ) ≫
      GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X x = V.base)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (he : Even m)
    (Q : LocalTheta.MarkedModel k m hm V.level ζ)
    (α : LabelThetaLift k (2*m) D X x m D.atlas.marking.x)
    (β : LabelThetaLift k (2*m) D X x m D.atlas.marking.y)
    (hα : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.x α)
    (hβ : LabelLiftSymmetry k (2*m) D X x m hm D.atlas.marking.y β) :
    ∀ i : Fin m, ∃ r : (Component k (2*m) D X x).functionField,
      θ r = algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m i) /
        algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k (2*m) m ⟨0, hm⟩) := by
  let F := (Component k (2*m) D X x).functionField
  letI : Algebra F Γ(curve k (2*m) D X x, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ (structureMap k (2*m) D X x).appTop).hom.toAlgebra
  letI : Module F Γ(thetaLine k (2*m) D X x m, ⊤) :=
    Module.compHom _ (algebraMap F Γ(curve k (2*m) D X x, ⊤))
  obtain ⟨b, ⟨frame⟩, hvalues⟩ := arithmetic_aligned_basis k m hm D X x V θ hb ζ hζ he Q α β hα hβ
  let f := SectionAction.pointValueLinear (structureMap k (2*m) D X x) (origin k (2*m) D X x)
    (origin_structure k (2*m) D X x) (thetaLine k (2*m) D X x m) (thetaRigidification k (2*m) D X x m hm)
  let g := arithmeticModelValueLinear k m hm D X x V θ hb ζ he Q frame
  have hker : ∀ v, f v = 0 → g v = 0 :=
    arithmeticModelValue_zero k m hm D X x V θ hb ζ he Q frame
  intro i
  refine ⟨f (b i) / f (b ⟨0, hm⟩), ?_⟩
  have hv := (Representation.quotient_of_kernel θ f g hker (b ⟨0, hm⟩) (b i) (hvalues frame).1).2
  rw [levelUnary_minimal k m hm, levelUnary_minimal k m hm]
  exact hv.trans ((hvalues frame).2 i)

#print axioms exact_unary_field_range
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

namespace ArithmeticThetaSharpCoverR0194
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
open FullLevelProjectiveRatiosR0194 FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- Exact normalized unary ratios are rational functions on the original
arithmetic full 2m-level component, with their actual punctured-disk expansions. -/
theorem full_level_projective_ratios :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
      (m : ℕ) (hm : 0 < m), Even m →
      ∀ (D : LevelData k (2*m)) (X : Compactification k (2*m) D),
      ∀ (V : DiskTest k (2*m) D X) (ζ : k), IsPrimitiveRoot ζ (2*m) →
      CanonicalMarking k (2*m) ζ V.level → ProjectiveRatios k (2*m) m hm D X V := by
  intro k _ _ _ m hm he D X V ζ hζ hmark
  obtain ⟨f, θ, hfac, hdom, hθ⟩ := component_field_factor k (2*m) D X V
  apply (projectiveRatios_iff_field_range k m hm D X V f hfac hdom θ hθ).mpr
  have hb := (component_field_map_over k (2*m) D X V f hfac θ hθ).2
  let z : kˣ := (hζ.isUnit (Nat.mul_pos (by decide) hm).ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit (Nat.mul_pos (by decide) hm).ne').unit_spec
  have hzr : IsPrimitiveRoot (z : k) (2*m) := by simpa only [hz] using hζ
  have hzm : CanonicalMarking k (2*m) (z : k) V.level := by simpa only [hz] using hmark
  obtain ⟨Q⟩ := LocalTheta.markedModel_exists k m hm he V.level z hzr hzm
  obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩ := component_symmetric_lifts k m hm he D X V ζ hζ hmark
  exact exact_unary_field_range k m hm D X (V.disk (closedPoint k)) V θ hb z hzr he Q α β hα hβ

#print axioms full_level_projective_ratios
end ArithmeticThetaSharpCoverR0194
