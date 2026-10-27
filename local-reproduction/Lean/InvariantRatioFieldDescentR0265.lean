import InvariantRatioDefinitionsR0265
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaInvariantRatiosR0265
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262

namespace InvariantRatioFieldDescent
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

lemma scalar_exists {F : Type u} [Field F] {M : (Base F).Modules}
    (hM : Scheme.Modules.IsInvertible M) (g : End M) :
    ∃ a : F, g = scalarEnd M a := by
  obtain ⟨a, ha, -⟩ := hM.existsUnique_app_eq_smul g
  refine ⟨(Scheme.ΓSpecIso (.of F)).hom.hom a, ?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change g.app U x = (scalarEnd M _).app U x
  simp only [scalarEnd, smulHom_app_apply, resTop]
  simpa using ha U x

lemma scalar_injective {F : Type u} [Field F] {M : (Base F).Modules}
    (hM : Scheme.Modules.IsInvertible M) : Function.Injective (scalarEnd M) := by
  intro a b hab
  obtain ⟨c, hc, hu⟩ := hM.existsUnique_app_eq_smul (scalarEnd M a)
  have ha : (Scheme.ΓSpecIso (.of F)).inv.hom a = c := hu _ (by
    intro U x
    rfl)
  have hb : (Scheme.ΓSpecIso (.of F)).inv.hom b = c := hu _ (by
    intro U x
    rw [hab]
    rfl)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of F)).inv).1
    (ha.trans hb.symm)

lemma scalar_zero {F : Type u} [Field F] (M : (Base F).Modules) :
    scalarEnd M 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (scalarEnd M 0).app U x = 0
  simp [scalarEnd, smulHom_app_apply, resTop]

lemma scalar_one {F : Type u} [Field F] (M : (Base F).Modules) :
    scalarEnd M 1 = 𝟙 M := by
  simp only [scalarEnd, map_one, smulHom_one]

lemma scalar_iso {F : Type u} [Field F] (M : (Base F).Modules) (a : F) (ha : a ≠ 0) :
    IsIso (scalarEnd M a) := by
  obtain ⟨v, hv⟩ := (isUnit_iff_ne_zero.mpr ha).map (Scheme.ΓSpecIso (.of F)).inv.hom
  change IsIso (smulHom _ M)
  rw [← hv]
  exact (smulIso v M).isIso_hom

lemma scalar_natural {F : Type u} [Field F] {M N : (Base F).Modules}
    (g : M ⟶ N) (a : F) : scalarEnd M a ≫ g = g ≫ scalarEnd N a :=
  smulHom_comp _ _

lemma scalar_pullback {F K : Type u} [Field F] [Field K] (θ : F →+* K)
    (M : (Base F).Modules) (a : F) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom θ))).map (scalarEnd M a) =
    scalarEnd ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom θ))).obj M) (θ a) := by
  unfold scalarEnd
  rw [pullback_map_smulHom]
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom θ)) a).symm

lemma line_iso {F : Type u} [Field F] {L M : (Base F).Modules}
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (L ≅ M) := by
  obtain ⟨eL⟩ := hL.nonempty_iso_unit_of_forall_invertible_free F
    (fun N _ _ _ => inferInstance) L
  obtain ⟨eM⟩ := hM.nonempty_iso_unit_of_forall_invertible_free F
    (fun N _ _ _ => inferInstance) M
  exact ⟨eL ≪≫ eM.symm⟩

lemma iso_ne_zero {F : Type u} [Field F] {M N : (Base F).Modules}
    (hM : Scheme.Modules.IsInvertible M) (g : M ⟶ N) [IsIso g] : g ≠ 0 := by
  intro hg
  have hid : 𝟙 M = 0 := by
    calc
      𝟙 M = g ≫ inv g := (IsIso.hom_inv_id g).symm
      _ = 0 := by simp only [hg, zero_comp]
  exact one_ne_zero (scalar_injective hM (by rw [scalar_one, scalar_zero, hid]))

lemma line_nonzero_iso {F : Type u} [Field F] {L M : (Base F).Modules}
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (g : L ⟶ M) (hg : g ≠ 0) : IsIso g := by
  obtain ⟨e⟩ := line_iso hL hM
  obtain ⟨a, ha⟩ := scalar_exists hM (e.inv ≫ g)
  have he : g = e.hom ≫ scalarEnd M a := by
    rw [← ha, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have ha0 : a ≠ 0 := by
    intro h
    apply hg
    rw [he, h, scalar_zero, comp_zero]
  letI := scalar_iso M a ha0
  rw [he]
  infer_instance

end InvariantRatioFieldDescent

open InvariantRatioFieldDescent

/-- Faithful descent of the actual invariant-component quotients. -/
theorem invariant_ratio_field_descent :
∀ (F K : Type u) [Field F] [Field K] (θ : F →+* K) (E : ArithmeticThetaLocalWeierstrassR0203.Family (ArithmeticThetaLocalWeierstrassR0203.Base F)) (E' : ArithmeticThetaLocalWeierstrassR0203.Family (ArithmeticThetaLocalWeierstrassR0203.Base K)) (f : Quiver.Hom E'.curve E.curve) (hc : CategoryTheory.IsPullback f E'.p E.p (AlgebraicGeometry.Spec.map (CommRingCat.ofHom θ))) (hz : CategoryTheory.CategoryStruct.comp E'.zero f = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map (CommRingCat.ofHom θ)) E.zero) (m : ℕ) (hm : 0 < m) (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V E m)) (A' B' : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V E' m)), AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSchemeSchrodingerR0261.fixed A) → AlgebraicGeometry.Scheme.Modules.IsInvertible ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaSchemeThetaMarkingR0259.thetaLine E m)) → ArithmeticThetaSchemeThetaNaturalityR0262.InvariantComponents E E' (AlgebraicGeometry.Spec.map (CommRingCat.ofHom θ)) f hc hz m A B A' B' → ∀ s : Fin m → K, ArithmeticThetaInvariantRatiosR0265.ComponentRatios E' m hm A' B' s → ∃! r : Fin m → F, ArithmeticThetaInvariantRatiosR0265.ComponentRatios E m hm A B r ∧ ∀ i, θ (r i) = s i := by
  intro F K _ _ θ E E' f hc hz m hm A B A' B' hL hM hcmp s hs
  let b := Spec.map (CommRingCat.ofHom θ)
  let P := Scheme.Modules.pullback b
  let M := (Scheme.Modules.pullback E.zero).obj (thetaLine E m)
  let M' := (Scheme.Modules.pullback E'.zero).obj (thetaLine E' m)
  let z : Fin m := ⟨0, hm⟩
  let c := component E m A B
  let c' := component E' m A' B'
  let d := fiberComparison E E' b f hc hz m
  obtain ⟨e, he, -⟩ := hcmp
  have H (i : Fin m) : P.map (c i) ≫ d.hom = e.hom ≫ c' i := he.2.2 i
  letI : IsIso (c' z) := hs.1
  have hP : IsIso (P.map (c z)) := by
    have hh : P.map (c z) = e.hom ≫ c' z ≫ d.inv := by
      rw [← Category.assoc, ← H z, Category.assoc, d.hom_inv_id, Category.comp_id]
    rw [hh]
    infer_instance
  letI := hP
  have hn : c z ≠ 0 := by
    intro hh
    apply iso_ne_zero (hL.pullback b) (P.map (c z))
    rw [hh, P.map_zero]
  letI : IsIso (c z) := line_nonzero_iso hL hM (c z) hn
  have hex (i : Fin m) : ∃ a : F, c i = c z ≫ scalarEnd M a := by
    obtain ⟨a, ha⟩ := scalar_exists hM (inv (c z) ≫ c i)
    refine ⟨a, ?_⟩
    rw [← ha, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  choose r hr using hex
  have hr_image (i : Fin m) : θ (r i) = s i := by
    have hh : c' i = c' z ≫ scalarEnd M' (θ (r i)) := by
      apply (cancel_epi e.hom).mp
      rw [← H i, hr i, P.map_comp, Category.assoc]
      change P.map (c z) ≫ P.map (scalarEnd M (r i)) ≫ d.hom = _
      rw [scalar_pullback θ M (r i), scalar_natural d.hom,
        ← Category.assoc, H z, Category.assoc]
    have hi : scalarEnd M' (θ (r i)) = scalarEnd M' (s i) := by
      apply (cancel_epi (c' z)).mp
      exact hh.symm.trans (hs.2 i)
    exact scalar_injective (SchemeInvariantThetaLine.invertible_of_iso d (hM.pullback b)) hi
  refine ⟨r, ⟨⟨inferInstance, hr⟩, hr_image⟩, ?_⟩
  intro r' hr'
  funext i
  exact θ.injective ((hr'.2 i).trans (hr_image i).symm)

#print axioms invariant_ratio_field_descent
end ArithmeticThetaInvariantRatiosR0265
