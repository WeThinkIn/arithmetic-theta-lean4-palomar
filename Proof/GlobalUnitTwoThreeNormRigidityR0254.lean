module

import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank

public import KatoCharacterizationDefinitionsR0254
public import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField
public import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected

public import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaKatoCharacterizationR0254
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeKatoUnitR0250
open ArithmeticThetaSchemeKatoNormR0251

namespace GlobalUnitTwoThreeNormRigidity

lemma structure_app_bijective {S : Scheme.{u}} (E : Family S) (U : S.Opens) :
    Function.Bijective (E.p.app U) := by
  letI := E.proper
  letI := E.dimension
  letI := E.connected
  letI : GeometricallyReduced E.p := ⟨by
    intro K _ y Z fst snd hpb
    letI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) hpb inferInstance
    exact Smooth.isReduced_of_isReduced_of_isLocallyNoetherian snd⟩
  apply bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField
  intro s
  exact bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected _

lemma complement_injective {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I) :
    Function.Injective (restrict (⊤ : X.Opens) I.support.compl le_top) := by
  intro s t h
  apply NormSection.sections_eq_local
  intro x _
  obtain ⟨U, hx, b, hb, hIb⟩ := hI x
  refine ⟨U.1, hx, le_top, ?_⟩
  apply ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor.complement_restrict_injective I U b hb hIb
  simpa only [NormSection.restrict_trans] using
    congrArg (restrict I.support.compl (U.1 ⊓ I.support.compl) inf_le_right) h

lemma unit_eq_one_of_four_nine {M : Type*} [Monoid M] (a : Mˣ)
    (h4 : a ^ 4 = a) (h9 : a ^ 9 = a) : a = 1 := by
  have h3 : a ^ 3 = 1 := by
    apply mul_right_cancel (b := a)
    simpa only [← pow_succ, one_mul] using h4
  have h8 : a ^ 8 = 1 := by
    apply mul_right_cancel (b := a)
    simpa only [← pow_succ, one_mul] using h9
  have h9' : a ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by decide, pow_mul, h3, one_pow]
  exact h9.symm.trans h9'

lemma affine_finrank_eq_module {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [Flat f] [IsFinite f]
    (s : S) [IsAffine X]
    (hf : letI := f.appTop.hom.toAlgebra; Module.Free Γ(S, ⊤) Γ(X, ⊤)) :
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
  letI := hf
  exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Γ(S, ⊤)) (M := Γ(X, ⊤))) _

/-- The rank of the actual finite flat map is computed by its affine section algebra. -/
lemma finrank_eq_affine_module
    {Y X : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Flat p]
    (U : X.Opens) (hU : IsAffineOpen U) (x : U)
    (hf : ArithmeticThetaGeometricNormR0150.AffineFree p U) :
    letI := (p.app U).hom.toAlgebra
    p.finrank x.1 = Module.finrank Γ(X,U) Γ(Y,p ⁻¹ᵁ U) := by
  letI : Nonempty U := ⟨x⟩
  letI : IsAffine U := hU
  let V := p ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage p
  letI : IsAffine V := hV
  let g := p ∣_ U
  letI := (p.app U).hom.toAlgebra
  have hg : g.finrank x = Module.finrank Γ(X,U) Γ(Y,V) := by
    letI := g.appTop.hom.toAlgebra
    have hc := (arrowResLEAppIso p U V le_rfl).inv.w
    simp only [arrowResLEAppIso, Arrow.isoMk_inv_left, Arrow.isoMk_inv_right, Arrow.mk_hom] at hc
    let eR := U.topIso.symm.commRingCatIsoToRingEquiv
    let eM := V.topIso.symm.commRingCatIsoToRingEquiv
    have he : (algebraMap Γ(U,⊤) Γ(V,⊤)).comp eR.toRingHom =
        eM.toRingHom.comp (algebraMap Γ(X,U) Γ(Y,V)) := by
      ext z
      have hz := congr($(hc) z)
      dsimp only [Arrow.mk] at hz
      change g.appTop (U.topIso.inv z) = V.topIso.inv (p.app U z)
      simpa only [V,g,Scheme.Hom.resLE,Scheme.homOfLE_rfl,Category.id_comp,
        Scheme.Hom.appLE_eq_app,ConcreteCategory.comp_apply] using hz
    letI : Module.Free Γ(X,U) Γ(Y,V) := hf
    letI : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
    letI : RingHomInvPair eR.symm.toRingHom eR.toRingHom := RingHomInvPair.of_ringEquiv eR.symm
    let e : Γ(Y,V) ≃ₛₗ[eR.toRingHom] Γ(V,⊤) :=
      { __ := eM.toAddEquiv
        map_smul' := by
          intro r x
          change eM (algebraMap _ _ r * x) = algebraMap _ _ (eR r) * eM x
          rw [map_mul]
          exact congrArg (fun z => z * eM x) (RingHom.congr_fun he r).symm }
    have hga := affine_finrank_eq_module g x (Module.Free.of_equiv e)
    exact hga.trans (Algebra.finrank_eq_of_equiv_equiv eR eM he).symm
  have hpull := Scheme.Hom.finrank_pullback_snd p U.ι x
  have hrestrict := Scheme.Hom.finrank_comp_left_of_isIso
    (pullbackRestrictIsoRestrict p U).inv (Limits.pullback.snd p U.ι)
  calc
    _ = Scheme.Hom.finrank (Limits.pullback.snd p U.ι) x := hpull.symm
    _ = g.finrank x := by simpa [g,morphismRestrict] using (hrestrict x).symm
    _ = _ := hg


lemma scalar_restriction {X : Scheme.{u}} (f : X ⟶ X)
    (a : Γ(X, ⊤)) (ha : f.appTop a = a) (V : X.Opens) :
    f.app V (restrict ⊤ V le_top a) = restrict ⊤ (f ⁻¹ᵁ V) le_top a := by
  have h := ConcreteCategory.congr_hom
    (f.naturality (homOfLE (show V ≤ ⊤ from le_top)).op) a
  change f.app V (restrict ⊤ V le_top a) =
    restrict ⊤ (f ⁻¹ᵁ V) le_top (f.appTop a) at h
  rwa [ha] at h

lemma norm_fixed_power {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [Etale f]
    (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I)
    (d : ℕ) (hd : ∀ x, f.finrank x = d)
    (a : Γ(X, ⊤)) (ha : f.appTop a = a)
    (hn : NormInvariant f I.support.compl (restrict ⊤ I.support.compl le_top a)) :
    a ^ d = a := by
  obtain ⟨N, hN, e, he⟩ := hn
  apply complement_injective I hI
  apply NormSection.sections_eq_local
  intro x hx
  obtain ⟨V, hxV, eV, hfV⟩ := finite_etale_free_cover X X f I.support.compl x hx
  refine ⟨V.1, hxV, eV, ?_⟩
  letI := (f.app V.1).hom.toAlgebra
  letI : Module.Free Γ(X,V.1) Γ(X,f ⁻¹ᵁ V.1) := hfV
  have hr : Module.finrank Γ(X,V.1) Γ(X,f ⁻¹ᵁ V.1) = d :=
    (finrank_eq_affine_module f V.1 V.2 ⟨x,hxV⟩ hfV).symm.trans (hd x)
  have hs := hN.1 I.support.compl
    (restrict I.support.compl (f ⁻¹ᵁ I.support.compl) e
      (restrict ⊤ I.support.compl le_top a))
  rw [he] at hs
  have hsV := hs V eV hfV
  simp only [NormSection.restrict_trans] at hsV ⊢
  rw [← scalar_restriction f a ha V.1] at hsV
  change Algebra.norm Γ(X,V.1) (algebraMap Γ(X,V.1) Γ(X,f ⁻¹ᵁ V.1)
    (restrict ⊤ V.1 le_top a)) = restrict ⊤ V.1 le_top a at hsV
  rw [Algebra.norm_algebraMap, hr] at hsV
  change (X.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom (a ^ d) = _
  rw [map_pow]
  exact hsV

lemma multiplication_fixes_global {S : Scheme.{u}} (E : Family S)
    (n : ℕ) (a : Γ(E.curve, ⊤)) : (multiplication E n).appTop a = a := by
  obtain ⟨b, rfl⟩ := (structure_app_bijective E ⊤).surjective a
  have ho : multiplication E n ≫ E.p = E.p :=
    (ArithmeticThetaSchemeLevelR0204.multiple E E.p n
      ⟨𝟙 E.curve, Category.id_comp E.p⟩).property
  exact ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop ho) b

end GlobalUnitTwoThreeNormRigidity

/-- Two actual determinant norms rigidify every global curve unit, over the
original arbitrary base scheme. -/
theorem global_unit_two_three_norm_rigidity :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (Base k)) (E : Family S),
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ a : GlobalUnits E,
      NormInvariant (multiplication E 2) (complement E c) (restrictGlobal E c a) →
      NormInvariant (multiplication E 3) (complement E c) (restrictGlobal E c a) → a = 1 := by
  intro k _ _ S σ E c hc _ a h2 h3
  have hI := SchemeKatoCartierDivisor.torsion_effective σ E c (by omega)
  have hp (n : ℕ) (hn : 0 < n)
      (h : NormInvariant (multiplication E n) (complement E c) (restrictGlobal E c a)) :
      a ^ (n ^ 2) = a := by
    obtain ⟨hf, he, _, hd⟩ := scheme_multiplication_degree k S σ E n hn
    letI := hf
    letI := he
    apply Units.ext
    exact GlobalUnitTwoThreeNormRigidity.norm_fixed_power (multiplication E n)
      (torsionIdeal E c) hI (n ^ 2) hd (a : _)
      (GlobalUnitTwoThreeNormRigidity.multiplication_fixes_global E n (a : _)) h
  exact GlobalUnitTwoThreeNormRigidity.unit_eq_one_of_four_nine a
    (hp 2 (by decide) h2) (hp 3 (by decide) h3)

#print axioms global_unit_two_three_norm_rigidity

end ArithmeticThetaKatoCharacterizationR0254
