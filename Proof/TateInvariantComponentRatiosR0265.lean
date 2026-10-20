module

public import InvariantRatioDefinitionsR0265
public import TateSchemeSectionEvaluationR0263
public import SchemeSchrodingerOrbitR0261
public import SchemeThetaIdentityEvaluationR0261

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaInvariantRatiosR0265
namespace TateInvariantComponentRatios
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaTateSchemeMarkingR0263
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- A field spectrum has just the empty and full opens. -/
lemma field_open (F : Type) [Field F] (U : (Base F).Opens) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr
      (show (U : Set (Base F)) ≠ ∅ from fun e => h (SetLike.coe_injective e))
    apply top_unique
    intro y hy
    exact (Subsingleton.elim x y) ▸ hx

instance bottom_sections (X : Scheme) (M : X.Modules) : Subsingleton Γ(M, ⊥) := by
  have hz (x : Γ(M, ⊥)) : x = 0 := by
    calc
      x = (1 : Γ(X, ⊥)) • x := (one_smul _ _).symm
      _ = (0 : Γ(X, ⊥)) • x := by rw [Subsingleton.elim (1 : Γ(X, ⊥)) 0]
      _ = 0 := zero_smul _ _
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma field_hom_ext (F : Type) [Field F] {M N : (Base F).Modules}
    (f g : M ⟶ N) (h : f.app ⊤ = g.app ⊤) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  rcases field_open F U with rfl | rfl
  · ext x
    exact Subsingleton.elim _ _
  · exact h

lemma field_isIso (F : Type) [Field F] {M N : (Base F).Modules}
    (f : M ⟶ N) (h : Function.Bijective (f.app ⊤)) : IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective (f.app U)).mpr
  rcases field_open F U with rfl | rfl
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · exact h

def frameValue {F : Type} [Field F] {N : (Base F).Modules}
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules))
    (x : Γ(N, ⊤)) : F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom (e.hom.app ⊤ x)

lemma frameValue_injective {F : Type} [Field F] {N : (Base F).Modules}
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules)) :
    Function.Injective (frameValue e) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1.comp
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1

lemma frameValue_smul {F : Type} [Field F] {N : (Base F).Modules}
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules))
    (c : F) (x : Γ(N, ⊤)) :
    frameValue e ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c • x) = c * frameValue e x := by
  unfold frameValue
  rw [Scheme.Modules.Hom.app_smul]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c * _) = _
  rw [map_mul]
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.apply_symm_apply c

lemma ratios_of_generator {F : Type} [Field F] {M N : (Base F).Modules}
    {n : ℕ} (hn : 0 < n) (f : Fin n → (M ⟶ N)) (r : Fin n → F)
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules))
    (x₀ : Γ(M, ⊤))
    (hspan : ∀ x : Γ(M, ⊤), ∃ c : F,
      x = (Scheme.ΓSpecIso (CommRingCat.of F)).inv c • x₀)
    (hne : frameValue e ((f ⟨0,hn⟩).app ⊤ x₀) ≠ 0)
    (hr : ∀ i, frameValue e ((f i).app ⊤ x₀) =
      frameValue e ((f ⟨0,hn⟩).app ⊤ x₀) * r i) :
    IsIso (f ⟨0,hn⟩) ∧ ∀ i, f i = f ⟨0,hn⟩ ≫ scalarEnd N (r i) := by
  have hcalc (i : Fin n) (c : F) :
      frameValue e ((f i).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c • x₀)) =
        c * frameValue e ((f i).app ⊤ x₀) := by
    rw [Scheme.Modules.Hom.app_smul, frameValue_smul]
  constructor
  · apply field_isIso F
    constructor
    · intro x y h
      obtain ⟨c, rfl⟩ := hspan x
      obtain ⟨d, rfl⟩ := hspan y
      have hh := congrArg (frameValue e) h
      rw [hcalc, hcalc] at hh
      rw [(mul_right_cancel₀ hne) hh]
    · intro y
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv
        (frameValue e y / frameValue e ((f ⟨0,hn⟩).app ⊤ x₀)) • x₀, ?_⟩
      apply frameValue_injective e
      rw [hcalc, div_mul_cancel₀ _ hne]
  · intro i
    apply field_hom_ext F
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    apply frameValue_injective e
    change _ = frameValue e ((scalarEnd N (r i)).app ⊤
      ((f ⟨0,hn⟩).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c • x₀)))
    have hs (z : Γ(N, ⊤)) : (scalarEnd N (r i)).app ⊤ z =
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv (r i) • z := by
      simp [scalarEnd,
        P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom_app_apply,
        P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.resTop]
    rw [hs, frameValue_smul, hcalc, hcalc, hr]
    ring

lemma action_top {S : Scheme} (E : Family S) (m : ℕ)
    (g : E.curve ⟶ E.curve) (a : Lift E m g) (A : End (V E m))
    (hA : IsAction E m g a A) (v : Γ(thetaLine E m, ⊤)) :
    A.app ⊤ v = SectionAction.globalAct g a v := by
  obtain ⟨h, hh⟩ := hA
  simpa [SectionAction.globalAct,
    ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.Sections.act]
    using (hh ⊤ v).symm

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (Vd : TateLevel k (2*m)) {ζ : kˣ}
  (Q : LocalTheta.MarkedModel k m hm Vd ζ) (he : Even m)

open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141 (act)
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141 (sc sc_one)
open ArithmeticThetaGeometricLiftsR0141.GeometricIntertwinerRigidityR0141

lemma model_fixed (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (v : GenericDual k Q.model Q.origin m)
    (hv : act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ) v = v) :
    ∃ c : LaurentSeries k, v = sc k Q.model Q.origin m c
      (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ⟨0,hm⟩) := by
  classical
  letI : AddCommGroup (GenericDual k Q.model Q.origin m) :=
    inferInstanceAs (AddCommGroup (genericPower k Q.model Q.origin m ⟶
      (SheafOfModules.unit (genericScheme k Q.model).ringCatSheaf : (genericScheme k Q.model).Modules)))
  let b := genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin
  have hb := generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
  obtain ⟨c, hc, _⟩ := hb v
  have heq : v = combine k Q.model Q.origin m m b c :=
    (combines_iff k Q.model Q.origin m m b c v).mp hc
  have hact := eigen_combine k Q.model Q.origin m m b (ζ^2) Q.mapA
    (ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.scalarMap_over
      k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2))
    (Q.canonicalA he hζ) (Q.canonicalA_eigen he hζ) c
  have hcoords : ArithmeticThetaSchrodingerR0119.standardA k m ((ζ^2 : kˣ) : k) c = c := by
    apply combine_injective k Q.model Q.origin m m b hb
    rw [← hact, ← heq, hv]
  have hvanish (i : Fin m) (hi : i ≠ ⟨0,hm⟩) : c i = 0 := by
    have hi0 : 0 < i.val := by
      by_contra hn
      apply hi
      apply Fin.ext
      change i.val = 0
      omega
    have hn := (LocalTheta.MarkedModel.root_half (hm := hm) hζ).pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hi0) i.isLt
    have hscalar : ArithmeticThetaSchrodingerR0119.scalar k (((ζ^2 : kˣ) : k)^i.val) ≠ 1 := by
      intro h
      apply hn
      exact HahnSeries.single_injective 0 (h.trans HahnSeries.single_zero_one.symm)
    have hiEq := congrFun hcoords i
    change ArithmeticThetaSchrodingerR0119.scalar k _ * c i = c i at hiEq
    exact (mul_eq_zero.mp (show
      (ArithmeticThetaSchrodingerR0119.scalar k (((ζ^2 : kˣ) : k)^i.val) - 1) * c i = 0 by
        rw [sub_mul, one_mul, hiEq, sub_self])).resolve_left (sub_ne_zero.mpr hscalar)
  refine ⟨c ⟨0,hm⟩, ?_⟩
  rw [heq]
  unfold combine
  rw [Finset.sum_eq_single ⟨0,hm⟩]
  · rfl
  · intro i _ hi
    rw [hvanish i hi]
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    simp [mulSection_app]
  · simp

lemma shift_basis
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (hb : shiftLiftFacts k Vd Q he b) (B : End (V (family k Vd) m))
    (hB : IsAction (family k Vd) m _ b B) (i : Fin m) :
    B.app ⊤ (basisSection k Vd Q he i) =
      basisSection k Vd Q he (ArithmeticThetaInfinitesimalPolygonR0129.next m hm i) := by
  rw [action_top _ _ _ _ _ hB]
  apply (sectionEquiv k Vd Q he).injective
  rw [SectionEvaluation.operator_comparison k Vd Q he _ _ b _ hb.1]
  simp only [basisSection, Equiv.apply_symm_apply]
  exact Q.canonicalB_cyclic he i

lemma shift_pow_basis
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (hb : shiftLiftFacts k Vd Q he b) (B : End (V (family k Vd) m))
    (hB : IsAction (family k Vd) m _ b B) (n : ℕ) (hn : n < m) :
    (B ^ n).app ⊤ (basisSection k Vd Q he ⟨0,hm⟩) = basisSection k Vd Q he ⟨n,hn⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change B.app ⊤ ((B ^ n).app ⊤ (basisSection k Vd Q he ⟨0,hm⟩)) = _
    rw [ih (by omega), shift_basis k Vd Q he b hb B hB]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt hn

lemma scalar_basis (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (A : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A) :
    A.app ⊤ (basisSection k Vd Q he ⟨0,hm⟩) = basisSection k Vd Q he ⟨0,hm⟩ := by
  rw [action_top _ _ _ _ _ hA]
  apply (sectionEquiv k Vd Q he).injective
  rw [SectionEvaluation.operator_comparison k Vd Q he _ _ a _ ha.1]
  simp only [basisSection, Equiv.apply_symm_apply]
  have h := (ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141.scaled_iff
    k Q.model Q.origin m _ _ _).mp (Q.canonicalA_eigen he hζ ⟨0,hm⟩)
  simpa [ArithmeticThetaGeometricLiftsR0141.phase, sc_one] using h

lemma fixed_top_span (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (A : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A)
    (v : Γ(V (family k Vd) m, ⊤)) (hv : A.app ⊤ v = v) :
    ∃ c : LaurentSeries k, v =
      (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k Vd).p.appTop) c) •
        basisSection k Vd Q he ⟨0,hm⟩ := by
  have hmodel : act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ)
      (sectionEquiv k Vd Q he v) = sectionEquiv k Vd Q he v := by
    rw [← SectionEvaluation.operator_comparison k Vd Q he _ _ a _ ha.1,
      ← action_top _ _ _ _ _ hA, hv]
  obtain ⟨c, hc⟩ := model_fixed k Vd Q he hζ _ hmodel
  refine ⟨c, (sectionEquiv k Vd Q he).injective ?_⟩
  change _ = LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k Vd Q he)
    ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k Vd).p.appTop) c) • _)
  erw [LocalTheta.modelFunctional_smul k Q.model Q.origin m Q.cubic _
    (modelComparison k Vd Q he) (family k Vd).p Q.cubic_over]
  change (sectionEquiv k Vd Q he) v = sc k Q.model Q.origin m c
    ((sectionEquiv k Vd Q he) (basisSection k Vd Q he ⟨0,hm⟩))
  simpa only [basisSection, Equiv.apply_symm_apply] using hc

lemma value_evaluation (e : FiberFrame k Vd)
    (v : Γ(thetaLine (family k Vd) m, ⊤)) :
    value k Vd e v = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (e.hom.app ⊤ ((evaluation (family k Vd) m).app ⊤ v)) := by
  rw [SchemeThetaIdentityEvaluation.evaluation_top]
  rfl

lemma component_ratios (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (hb : shiftLiftFacts k Vd Q he b)
    (A B : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A) (hB : IsAction (family k Vd) m _ b B) :
    ComponentRatios (family k Vd) m hm A B (unaryRatio k m hm) := by
  obtain ⟨⟨e⟩, heval⟩ := SectionEvaluation.exact_values k Vd Q he hζ
  obtain ⟨x₀, hx₀⟩ := (SchemeSchrodingerOrbit.fixedSections_bijective A ⊤).2
    ⟨basisSection k Vd Q he ⟨0,hm⟩, by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact scalar_basis k Vd Q he hζ a ha A hA⟩
  have hzero : (fixedι A).app ⊤ x₀ = basisSection k Vd Q he ⟨0,hm⟩ :=
    congrArg Subtype.val hx₀
  have hinj : Function.Injective ((fixedι A).app ⊤) :=
    (ModuleCat.mono_iff_injective ((SchemeSchrodingerOrbit.sections ⊤).map (fixedι A))).mp
      inferInstance
  have hspan (x : Γ(fixed A, ⊤)) : ∃ c : LaurentSeries k,
      x = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c • x₀ := by
    obtain ⟨c, hc⟩ := fixed_top_span k Vd Q he hζ a ha A hA
      ((fixedι A).app ⊤ x) (SchemeSchrodingerOrbit.fixed_mem A ⊤ x)
    refine ⟨c, hinj ?_⟩
    rw [Scheme.Modules.Hom.app_smul, hzero]
    exact hc
  have hcomp (i : Fin m) : frameValue e ((component (family k Vd) m A B i).app ⊤ x₀) =
      value k Vd e (basisSection k Vd Q he i) := by
    change frameValue e ((evaluation (family k Vd) m).app ⊤
      ((B ^ i.val).app ⊤ ((fixedι A).app ⊤ x₀))) = _
    rw [hzero, shift_pow_basis k Vd Q he b hb B hB i.val i.isLt]
    exact (value_evaluation k Vd e _).symm
  apply ratios_of_generator hm (component (family k Vd) m A B) (unaryRatio k m hm) e x₀ hspan
  · rw [hcomp]
    exact (heval e).1
  · intro i
    rw [hcomp, hcomp]
    have h := (heval e).2 i
    change value k Vd e (basisSection k Vd Q he i) /
      value k Vd e (basisSection k Vd Q he ⟨0,hm⟩) = unaryRatio k m hm i at h
    exact (div_eq_iff (heval e).1).mp h |>.trans (mul_comm _ _)

end TateInvariantComponentRatios
/-- The actual invariant-line components for the matched literal Tate lifts
are the complete unary ratios, as morphisms of sheaves. -/
theorem tate_invariant_component_ratios :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (Vd : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd ζ), ∀ (a : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd))) (b : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd))), ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd Q he hζ a → ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd Q he b → ∀ (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m)), ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd)) a A → ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd)) b B → ArithmeticThetaInvariantRatiosR0265.ComponentRatios (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m hm A B (ArithmeticThetaInvariantRatiosR0265.unaryRatio k m hm) := by
  intro k _ _ m hm he Vd ζ hζ Q a b ha hb A B hA hB
  exact TateInvariantComponentRatios.component_ratios k Vd Q he hζ a b ha hb A B hA hB

end ArithmeticThetaInvariantRatiosR0265

#print axioms ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios.model_fixed
#print axioms ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios.ratios_of_generator
#print axioms ArithmeticThetaInvariantRatiosR0265.tate_invariant_component_ratios
