import SymmetricMarkingDefinitionsR0142
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul

/-! Structural scalar comparison on every local section of the marked ideal power. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSymmetricMarkingR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141

namespace GenericLiftScalarComparisonR0142

lemma iso_scalar {X : Scheme.{u}} {L N : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (e e' : L ≅ N) :
    ∃! a : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(L, U)),
      e'.hom.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a •
        e.hom.app U x := by
  obtain ⟨a, ha, hu⟩ := hL.existsUnique_app_eq_smul (e'.hom ≫ e.inv)
  have hc (U : X.Opens) (x : Γ(L, U)) :
      e.hom.app U (e.inv.app U (e'.hom.app U x)) = e'.hom.app U x := by
    have h := congrArg (fun q => q.app U (e'.hom.app U x)) e.inv_hom_id
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h
  refine ⟨a, ?_, ?_⟩
  · intro U x
    have h := congrArg (fun y => e.hom.app U y) (ha U x)
    change e.hom.app U (e.inv.app U (e'.hom.app U x)) = _ at h
    rw [hc, Scheme.Modules.Hom.app_smul] at h
    exact h
  · intro b hb
    apply hu b
    intro U x
    change e.inv.app U (e'.hom.app U x) = _
    rw [hb, Scheme.Modules.Hom.app_smul]
    have h := congrArg (fun q => q.app U x) e.hom_inv_id
    have h' : e.inv.app U (e.hom.app U x) = x := by
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h
    rw [h']

lemma scalar_ne_zero {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) [Nontrivial Γ(X, ⊤)]
    (e : L ≅ L) (a : Γ(X, ⊤))
    (ha : ∀ (U : X.Opens) (x : Γ(L, U)),
      e.hom.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • x) :
    a ≠ 0 := by
  intro h
  subst a
  obtain ⟨b, hb, hu⟩ := hL.existsUnique_app_eq_smul (𝟙 L)
  have hzero (U : X.Opens) (x : Γ(L, U)) : x = 0 := by
    have hx := ha U x
    simp only [map_zero, zero_smul] at hx
    have hh := congrArg (fun q => q.app U x) e.hom_inv_id
    have hh' : e.inv.app U (e.hom.app U x) = x := by
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using hh
    rw [hx, map_zero] at hh'
    exact hh'.symm
  have h0 : (0 : Γ(X, ⊤)) = b := hu 0 (by
    intro U x
    change x = _
    simpa only [map_zero, zero_smul] using hzero U x)
  have h1 : (1 : Γ(X, ⊤)) = b := hu 1 (by
    intro U x
    change x = _
    simp only [map_one, one_smul])
  exact zero_ne_one (h0.trans h1.symm)

end GenericLiftScalarComparisonR0142

theorem generic_lift_scalar_comparison :
∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r → ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T), ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M → ∀ (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X), ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s → ∀ (d : ℕ) (f : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (e e' : ArithmeticThetaGeometricLiftsR0141.Lift k M s d f), ∃! c : LaurentSeries k, c ≠ 0 ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s d f c e e' := by
  intro k _ _ r hr h3 T M hM s hs d f e e'
  have hL : Scheme.Modules.IsInvertible (genericPower k M s d) :=
    Scheme.Modules.IsInvertible.pullback (genericInclusion k M)
      (ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138.power_invertible
        k h3 M hM s hs d).isInvertible_module
  let σ : LaurentSeries k →+* Γ(genericScheme k M, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
      (genericStructure k M).appTop).hom
  have hσ : Function.Bijective σ :=
    AlgebraizedGeometricConnectednessR0135.genericScalar_bijective k M h3 hM
  letI : Nontrivial Γ(genericScheme k M, ⊤) := hσ.1.nontrivial
  obtain ⟨a, ha, hu⟩ := GenericLiftScalarComparisonR0142.iso_scalar hL e e'
  obtain ⟨c, hc⟩ := hσ.2 a
  have hendo : ∀ (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)),
      (e' ≪≫ e.symm).hom.app U x =
        (genericScheme k M).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • x := by
    intro U x
    change e.inv.app U (e'.hom.app U x) = _
    rw [ha, Scheme.Modules.Hom.app_smul]
    have h := congrArg (fun q => q.app U x) e.hom_inv_id
    have hx : e.inv.app U (e.hom.app U x) = x := by
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h
    rw [hx]
  have ha0 : a ≠ 0 :=
    GenericLiftScalarComparisonR0142.scalar_ne_zero hL (e' ≪≫ e.symm) a hendo
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro h
    apply ha0
    rw [← hc, h, map_zero]
  · intro U x
    change e'.hom.app U x =
      (genericScheme k M).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (σ c) •
        e.hom.app U x
    rw [hc]
    exact ha U x
  · intro b hb
    apply hσ.1
    rw [hc]
    exact hu (σ b) hb.2

end ArithmeticThetaSymmetricMarkingR0142
#print axioms ArithmeticThetaSymmetricMarkingR0142.generic_lift_scalar_comparison
