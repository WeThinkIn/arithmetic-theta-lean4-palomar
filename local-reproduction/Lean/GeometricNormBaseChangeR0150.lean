import FiniteEtaleLocalNormR0150
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaGeometricNormR0150
namespace BaseChange
open CategoryTheory AlgebraicGeometry

/-- Determinants commute with an actual scalar extension of a finite free algebra. -/
theorem norm_of_baseChange {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra A B] [Algebra R B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [Module.Free R S] [Module.Finite R S]
    (h : IsBaseChange A (IsScalarTower.toAlgHom R S B).toLinearMap) (s : S) :
    algebraMap R A (Algebra.norm R s) = Algebra.norm A (algebraMap S B s) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (h.basis b), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    h.basis_apply]
  simpa only [AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply, map_mul] using
    (h.basis_repr_comp_apply b (s * b j) i).symm

/-- A generic-point square induces the corresponding square on any pair of
nonempty affine opens related by the actual scheme map. -/
theorem section_field_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) [Nonempty U] [Nonempty V] :
    (X.germToFunctionField V).hom.comp (f.appLE U V e).hom =
      φ.comp (Y.germToFunctionField U).hom := by
  have hX : Spec.map (X.germToFunctionField V) ≫ hV.fromSpec =
      X.fromSpecStalk (genericPoint X) := hV.fromSpecStalk_eq_fromSpecStalk _
  have hY : Spec.map (Y.germToFunctionField U) ≫ hU.fromSpec =
      Y.fromSpecStalk (genericPoint Y) := hU.fromSpecStalk_eq_fromSpecStalk _
  have hnat := hU.SpecMap_appLE_fromSpec f hV e
  have he : f.appLE U V e ≫ X.germToFunctionField V =
      Y.germToFunctionField U ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    apply (cancel_mono hU.fromSpec).mp
    simp only [Spec.map_comp, Category.assoc]
    rw [hnat, ← Category.assoc, hX, hY]
    exact hφ
  exact congrArg CommRingCat.Hom.hom he

/-- The categorical pushout of section rings gives free base change and norm naturality. -/
theorem norm_of_pushout {R S A B : CommRingCat.{u}}
    (r : R ⟶ S) (a : R ⟶ A) (b : S ⟶ B) (s : A ⟶ B)
    (h : IsPushout r a b s)
    (hf : letI := r.hom.toAlgebra; Module.Free R S)
    (hfin : letI := r.hom.toAlgebra; Module.Finite R S) :
    (letI := s.hom.toAlgebra; Module.Free A B) ∧
    (∀ x : S, a (letI := r.hom.toAlgebra; Algebra.norm R x) =
      (letI := s.hom.toAlgebra; Algebra.norm A (b x))) := by
  letI := r.hom.toAlgebra
  letI := a.hom.toAlgebra
  letI := b.hom.toAlgebra
  letI := s.hom.toAlgebra
  letI := (b.hom.comp r.hom).toAlgebra
  letI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  letI : IsScalarTower R A B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  letI : Module.Free R S := hf
  letI : Module.Finite R S := hfin
  have hp : Algebra.IsPushout R A S B := CommRingCat.isPushout_iff_isPushout.mp h.flip
  have hb := hp.out
  exact ⟨hb.free, norm_of_baseChange hb⟩

/-- Restricting the geometric square to affine charts gives the actual pushout
of their section rings. -/
theorem sections_pushout {X Y Xb Yb : Scheme.{u}}
    (f : X ⟶ Y) (fb : Xb ⟶ Yb) (i : Xb ⟶ X) (j : Yb ⟶ Y)
    (h : IsPullback i fb f j) [IsFinite f] [IsFinite fb]
    (U : Y.Opens) (V : Yb.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ j ⁻¹ᵁ U)
    (e' : fb ⁻¹ᵁ V ≤ i ⁻¹ᵁ (f ⁻¹ᵁ U)) :
    IsPushout (f.app U) (j.appLE U V e)
      (i.appLE (f ⁻¹ᵁ U) (fb ⁻¹ᵁ V) e') (fb.app V) := by
  have eq : fb ⁻¹ᵁ V = i ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ fb ⁻¹ᵁ V := by
    exact (inf_eq_right.mpr e').symm
  have hp := Scheme.Hom.isPullback_resLE h e le_rfl eq
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have hr := isPushout_appTop_of_isPullback hp
  apply hr.of_iso U.topIso (f ⁻¹ᵁ U).topIso V.topIso (fb ⁻¹ᵁ V).topIso
  all_goals simp [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    Scheme.Hom.appLE_eq_app]

/-- Norm naturality for every section on a free affine norm chart. -/
theorem section_norm {X Y Xb Yb : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Xb] [IsIntegral Yb]
    (f : X ⟶ Y) (fb : Xb ⟶ Yb) (i : Xb ⟶ X) (j : Yb ⟶ Y)
    (h : IsPullback i fb f j) [IsFinite f] [IsFinite fb]
    (φ : Y.functionField →+* X.functionField)
    (φb : Yb.functionField →+* Xb.functionField)
    (α : X.functionField →+* Xb.functionField)
    (β : Y.functionField →+* Yb.functionField)
    (hφ : IsFieldMap f φ) (hφb : IsFieldMap fb φb)
    (hα : IsFieldMap i α) (hβ : IsFieldMap j β)
    (U : Y.Opens) (V : Yb.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ j ⁻¹ᵁ U) (hf : AffineFree f U)
    [Nonempty U] [Nonempty V] [Nonempty (f ⁻¹ᵁ U)] [Nonempty (fb ⁻¹ᵁ V)]
    (a : Γ(X, f ⁻¹ᵁ U)) :
    β (fieldNorm φ (X.germToFunctionField (f ⁻¹ᵁ U) a)) =
      fieldNorm φb (α (X.germToFunctionField (f ⁻¹ᵁ U) a)) := by
  have e' : fb ⁻¹ᵁ V ≤ i ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact fb.preimage_mono e
  have hp := sections_pushout f fb i j h U V hU hV e e'
  obtain ⟨hfree, hnorm⟩ := norm_of_pushout (f.app U) (j.appLE U V e)
    (i.appLE (f ⁻¹ᵁ U) (fb ⁻¹ᵁ V) e') (fb.app V) hp hf (f.finite_app U hU)
  have hN := (LocalNorm.affine_field_data f φ hφ U hU).2.2 hf
  have hNb := (LocalNorm.affine_field_data fb φb hφb V hV).2.2 hfree
  have hi := DFunLike.congr_fun
    (section_field_square i α hα (f ⁻¹ᵁ U) (fb ⁻¹ᵁ V)
      (hU.preimage f) (hV.preimage fb) e') a
  have hj := DFunLike.congr_fun (section_field_square j β hβ U V hU hV e)
    (affineNorm f U a)
  change Xb.germToFunctionField (fb ⁻¹ᵁ V) (i.appLE _ _ e' a) =
    α (X.germToFunctionField (f ⁻¹ᵁ U) a) at hi
  change Yb.germToFunctionField V (j.appLE U V e (affineNorm f U a)) =
    β (Y.germToFunctionField U (affineNorm f U a)) at hj
  rw [← hN a, ← hj, ← hi, ← hNb]
  exact congrArg (Yb.germToFunctionField V) (hnorm a)

theorem fieldNorm_div {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y.functionField →+* X.functionField) (hφ : FiniteFieldMap φ)
    (a b : X.functionField) :
    fieldNorm φ (a / b) = fieldNorm φ a / fieldNorm φ b := by
  letI := φ.toAlgebra
  letI : FiniteDimensional Y.functionField X.functionField := hφ
  simp only [fieldNorm, div_eq_mul_inv, map_mul, Algebra.norm_inv]

end BaseChange
open CategoryTheory AlgebraicGeometry

/-- Field norms commute with a genuine cartesian base change of integral schemes,
with all four field maps fixed by their actual generic-point squares. -/
theorem geometric_norm_base_change
    (X Y Xb Yb : Scheme.{u})
    [IsIntegral X] [IsIntegral Y] [IsIntegral Xb] [IsIntegral Yb]
    (f : X ⟶ Y) (fb : Xb ⟶ Yb) (i : Xb ⟶ X) (j : Yb ⟶ Y)
    (h : IsPullback i fb f j) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField)
    (φb : Yb.functionField →+* Xb.functionField)
    (α : X.functionField →+* Xb.functionField)
    (β : Y.functionField →+* Yb.functionField)
    (hφ : IsFieldMap f φ) (hφb : IsFieldMap fb φb)
    (hα : IsFieldMap i α) (hβ : IsFieldMap j β)
    (g : X.functionField) :
    β (fieldNorm φ g) = fieldNorm φb (α g) := by
  letI : IsFinite fb := MorphismProperty.of_isPullback (P := @IsFinite) h inferInstance
  letI : Etale fb := MorphismProperty.of_isPullback (P := @Etale) h inferInstance
  letI : Surjective fb := MorphismProperty.of_isPullback (P := @Surjective) h inferInstance
  obtain ⟨hfin, _, hlocal⟩ := finite_etale_local_norm X Y f φ hφ
  have hfinb := (finite_etale_local_norm Xb Yb fb φb hφb).1
  obtain ⟨U, hy, hU, hfree, _⟩ := hlocal (j (genericPoint Yb))
  obtain ⟨V, hV, hv, e⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Yb ∈ j ⁻¹ᵁ U from hy)
  letI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI : Nonempty V := ⟨⟨_, hv⟩⟩
  obtain ⟨x, hx⟩ := f.surjective (j (genericPoint Yb))
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by change f x ∈ U; rwa [hx]⟩⟩
  obtain ⟨xb, hxb⟩ := fb.surjective (genericPoint Yb)
  letI : Nonempty (fb ⁻¹ᵁ V) := ⟨⟨xb, by change fb xb ∈ V; rwa [hxb]⟩⟩
  have hsec := BaseChange.section_norm f fb i j h φ φb α β hφ hφb hα hβ
    U V hU hV e hfree
  letI : IsFractionRing Γ(X, f ⁻¹ᵁ U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ (hU.preimage f)
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective Γ(X, f ⁻¹ᵁ U) g
  rw [BaseChange.fieldNorm_div φ hfin, map_div₀, map_div₀,
    BaseChange.fieldNorm_div φb hfinb]
  exact congrArg₂ (· / ·) (hsec a) (hsec b)

end ArithmeticThetaGeometricNormR0150
