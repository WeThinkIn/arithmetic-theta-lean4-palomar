module

public import RootCoverFlat

import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaKummer ArithmeticThetaNormalization
  ArithmeticThetaNormalizationField ArithmeticThetaNormalizationFinite

namespace ArithmeticThetaGeometricDegree

universe u
noncomputable section

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

theorem rootCover_generic_finrank_eq_functionField_finrank :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f]
      (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] (N s : ℕ),
      0 < N → ∀ (r : Fin s → Ω) (a : Fin s → X.functionField),
        (∀ j, r j ^ N = algebraMap X.functionField Ω (a j)) →
          AlgebraicGeometry.Scheme.Hom.finrank
            (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) (genericPoint X) =
            Module.finrank X.functionField
              (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField := by
  intro X hX k hk hcz f hs hlf hrd Ω hΩ hAlg N s hN r a hr
  let E : IntermediateField X.functionField Ω :=
    ArithmeticThetaKummerCover.generatedRootField X Ω s r
  have hdegree := ArithmeticThetaKummerCover.generatedRootField_degree X Ω N s hN r a hr
  obtain ⟨hnoeth, hchar, hnormal⟩ :=
    ArithmeticThetaSmoothNormality.smooth_normalization_prerequisites X k f
  letI : IsLocallyNoetherian X := hnoeth
  letI : CharZero X.functionField := hchar
  letI : FiniteDimensional X.functionField E := hdegree.1
  letI : Algebra.IsAlgebraic X.functionField E := Algebra.IsAlgebraic.of_finite _ _
  letI : Algebra.IsIntegral X.functionField E := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable X.functionField E := inferInstance
  letI : IsFinite (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    extensionFromNormalization_finite X E hnormal
  letI : Flat (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    rootCover_finite_flat X k f Ω N s hN r a hr
  let i := X.affineOpenCover.idx (genericPoint X)
  let U : X.Opens := (X.affineOpenCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineOpenCover.f i)
  have hxU : genericPoint X ∈ U := by
    exact X.affineOpenCover.covers (genericPoint X)
  let xU : U := ⟨genericPoint X, hxU⟩
  letI : Nonempty U := ⟨xU⟩
  letI : IsAffine U := hU
  letI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  letI : IsIntegral (Spec Γ(X, U)) := IsIntegral.of_isIso hU.isoSpec.hom
  letI : IsDomain Γ(X, U) := (affine_isIntegral_iff _).mp inferInstance
  let V : (ArithmeticThetaKummerCover.rootCover X Ω s r).Opens :=
    ArithmeticThetaKummerCover.rootCoverMap X Ω s r ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage _
  letI : IsAffine V := hV
  letI : Nonempty V := inferInstance
  let g := ArithmeticThetaKummerCover.rootCoverMap X Ω s r ∣_ U
  letI : Algebra Γ(X, U) Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V) :=
    ((ArithmeticThetaKummerCover.rootCoverMap X Ω s r).app U).hom.toAlgebra
  have hg : g.finrank xU = Module.finrank Γ(X, U)
      Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V) := by
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
    have hga := affine_finrank_eq_module g xU
    have hc := (arrowResLEAppIso (ArithmeticThetaKummerCover.rootCoverMap X Ω s r)
      U V le_rfl).inv.w
    simp only [arrowResLEAppIso, Arrow.isoMk_inv_left, Arrow.isoMk_inv_right, Arrow.mk_hom] at hc
    have hfin : Module.finrank Γ(X, U) Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V) =
        Module.finrank Γ(U, ⊤) Γ(V, ⊤) := by
      apply Algebra.finrank_eq_of_equiv_equiv
        U.topIso.symm.commRingCatIsoToRingEquiv V.topIso.symm.commRingCatIsoToRingEquiv
      ext z
      simp only [Scheme.Hom.resLE, Scheme.homOfLE_rfl, Category.id_comp,
        Scheme.Hom.appLE_eq_app] at hc
      have hz := congr($(hc) z)
      change g.appTop (U.topIso.inv z) = V.topIso.inv ((ArithmeticThetaKummerCover.rootCoverMap X Ω s r).app U z)
      simpa only [V, g, Arrow.mk_right, Scheme.Hom.resLE, Scheme.homOfLE_rfl, Category.id_comp, Scheme.Hom.appLE_eq_app, ConcreteCategory.comp_apply] using! hz
    exact hga.trans hfin.symm
  have hpull := Scheme.Hom.finrank_pullback_snd
    (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) U.ι xU
  have hrestrict := Scheme.Hom.finrank_comp_left_of_isIso
    (pullbackRestrictIsoRestrict (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) U).inv
    (Limits.pullback.snd (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) U.ι)
  have hfg : AlgebraicGeometry.Scheme.Hom.finrank
      (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) (genericPoint X) =
      Module.finrank Γ(X, U) Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V) := by
    calc
      _ = Scheme.Hom.finrank
          (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) (U.ι xU) := by rfl
      _ = Scheme.Hom.finrank
          (Limits.pullback.snd (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) U.ι) xU := hpull.symm
      _ = Scheme.Hom.finrank g xU := by
        simpa [g, morphismRestrict] using (hrestrict xU).symm
      _ = _ := hg
  letI : Algebra Γ(X, U) X.functionField :=
    (X.germToFunctionField U).hom.toAlgebra
  letI : Algebra Γ(X, U)
      (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField :=
    ((algebraMap X.functionField
      (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField).comp
        (algebraMap Γ(X, U) X.functionField)).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField
      (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V)
      (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField :=
    ((ArithmeticThetaKummerCover.rootCover X Ω s r).germToFunctionField V).hom.toAlgebra
  letI : IsScalarTower Γ(X, U)
      Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V)
      (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    exact congr($(normalizationBaseFieldMap_germ X E U) b)
  have hfracX := functionField_isFractionRing_of_isAffineOpen X U hU
  have hfracY := functionField_isFractionRing_of_isAffineOpen
    (ArithmeticThetaKummerCover.rootCover X Ω s r) V hV
  have hdim := IsFractionRing.finrank_eq (Γ(X, U)) X.functionField
    Γ(ArithmeticThetaKummerCover.rootCover X Ω s r, V)
    (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField
  exact hfg.trans hdim.symm

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.rootCover_generic_finrank_eq_functionField_finrank
