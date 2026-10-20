module

public import FiniteEtaleMapFiniteModelR0221
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true

/-! Descent of a finite, possibly ramified map between the given curve models. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRamifiedRootModelsR0222
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 FiniteEtaleMap

namespace RamifiedFiniteMap

open scoped nonZeroDivisors
open TensorProduct

/-- Over a domain, localization at a prime does not change module rank. -/
theorem rankAtStalk_eq_finrank_domain (R A : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup A] [Module R A] (p : PrimeSpectrum R) :
    Module.rankAtStalk A p = Module.finrank R A := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A) p.asIdeal.primeCompl_le_nonZeroDivisors

/-- Rank in a ring pushout is preserved by a flat extension of integral bases.
The finite map itself need not be etale or flat. -/
theorem ring_finrank_pushout {R S T P : CommRingCat} [IsDomain R] [IsDomain T]
    {f : R ⟶ S} {g : R ⟶ T} {inl : S ⟶ P} {inr : T ⟶ P}
    (h : IsPushout f g inl inr) (hg : g.hom.Flat) (x : PrimeSpectrum T) :
    inr.hom.finrank x = f.hom.finrank (PrimeSpectrum.comap g.hom x) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have : IsScalarTower R T P := .of_algebraMap_eq' <| congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  have : Module.Flat R T := hg
  have : FaithfulSMul R T := inferInstance
  change Module.rankAtStalk P x = Module.rankAtStalk S _
  rw [rankAtStalk_eq_finrank_domain, rankAtStalk_eq_finrank_domain]
  have : Algebra.IsPushout R T S P := Algebra.IsPushout.symm inferInstance
  rw [(Algebra.IsPushout.equiv R T S P).symm.toLinearEquiv.finrank_eq]
  exact (TensorProduct.isBaseChange R S T).finrank_eq

private def affineRank {X S : Scheme} [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)

theorem affineRank_pullback {X S Y T : Scheme} [IsAffine S] [IsAffine T]
    [IsIntegral S] [IsIntegral T] (f : X ⟶ S) (f' : Y ⟶ T)
    (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [IsFinite f] [Flat g]
    (s : S) (t : T) (hs : g t = s) : affineRank f' t = affineRank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have hp : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [affineRank]
  rw [ring_finrank_pushout hp g.flat_appTop (T.isoSpec.hom t),
    ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl


/-- The affine chart formula for a finite map over an integral base,
compared along a flat map from another integral affine scheme. -/
theorem finrank_affine_pullback {X S T : Scheme} [IsIntegral S] [IsIntegral T]
    (f : X ⟶ S) (g : T ⟶ S) [IsAffine T] [Flat g] [IsFinite f] (t : T) :
    f.finrank (g t) = affineRank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  have : Nonempty (Spec R) := ⟨z⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion (u ≫ pullback.snd i g)
  have : Nonempty (Spec (S.affineOpenCover.X (S.affineOpenCover.idx (g t)))) :=
    ⟨(S.affineOpenCover.covers (g t)).choose⟩
  have : IsIntegral (Spec (S.affineOpenCover.X (S.affineOpenCover.idx (g t)))) :=
    isIntegral_of_isOpenImmersion i
  change affineRank _ _ = _
  trans affineRank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · exact (affineRank_pullback (pullback.snd f i) _ _ (u ≫ pullback.fst i g)
      (IsPullback.map_fst_comp_fst_snd_comp_fst f g i u) _ z hyl).symm
  · simp_rw [← hyr]
    exact affineRank_pullback _ _ _ _ (.of_hasPullback _ _) _ _ rfl

/-- Affine presentation of the rank, without flatness of the finite map. -/
theorem finrank_affine {X S : Scheme} [IsIntegral S] [IsAffine S]
    (f : X ⟶ S) [IsFinite f] (s : S) : f.finrank s = affineRank f s := by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl, finrank_affine_pullback]
  exact affineRank_pullback _ _ _ _ (.of_hasPullback _ _) _ _ rfl

/-- Flat base change between integral schemes preserves pointwise rank of any
finite map, including ramified maps. -/
theorem finrank_pullback {X S T : Scheme} [IsIntegral S] [IsIntegral T]
    (f : X ⟶ S) (g : T ⟶ S) [Flat g] [IsFinite f] (t : T) :
    (pullback.snd f g).finrank t = f.finrank (g t) := by
  obtain ⟨R, i, hi, t', rfl⟩ := T.exists_Spec_apply_eq t
  have : Nonempty (Spec R) := ⟨t'⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion i
  rw [finrank_affine_pullback _ i, ← Scheme.Hom.comp_apply,
    finrank_affine_pullback _ (i ≫ g)]
  exact affineRank_pullback _ _ (pullbackLeftPullbackSndIso f g i).hom (𝟙 _)
    (IsPullback.of_horiz_isIso (by simp)) _ _ rfl

/-- Invariance under an isomorphism on the source, over an integral base. -/
theorem finrank_comp_iso {X Y S : Scheme} [IsIntegral S]
    (i : X ⟶ Y) (f : Y ⟶ S) [IsIso i] [IsFinite f] :
    (i ≫ f).finrank = f.finrank := by
  ext s
  obtain ⟨R, j, hj, s', rfl⟩ := S.exists_Spec_apply_eq s
  have : Nonempty (Spec R) := ⟨s'⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  rw [finrank_affine_pullback _ j, finrank_affine_pullback _ j]
  apply affineRank_pullback _ _ (pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp))
    (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

theorem finrank_cartesian {P X Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) [IsFinite f] [Flat g] (y : Y) :
    b.finrank y = f.finrank (g y) := by
  rw [← h.isoPullback_hom_snd, finrank_comp_iso, finrank_pullback]

/-- Finite fibers descend through the actual Cartesian square. Properness of
both curve models then promotes quasi-finiteness to finiteness. -/
theorem properties_of_cartesian {X Y : Curve Omega} {K : FieldStage}
    (M : Model X K) (N : Model Y K) (f : X.space ⟶ Y.space)
    [IsFinite f] [Surjective f] (g : M.curve.space ⟶ N.curve.space)
    (hg : g ≫ N.curve.map = M.curve.map)
    (hc : IsPullback M.projection f g N.projection) :
    IsFinite g ∧ Surjective g ∧
      ∀ y : Y.space, g.finrank (N.projection y) = f.finrank y := by
  have : Surjective N.projection := (projection_fpqc N).1
  have : IsProper N.curve.map := N.curve.proper
  have : IsProper (g ≫ N.curve.map) := hg.symm ▸ M.curve.proper
  have : IsProper g := IsProper.of_comp g N.curve.map
  have : LocallyQuasiFinite g := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro z
    obtain ⟨y, rfl⟩ := N.projection.surjective z
    have he : M.projection '' (f ⁻¹' {y}) = g ⁻¹' {N.projection y} := by
      simpa only [Set.image_singleton] using
        Scheme.image_preimage_eq_of_isPullback hc.flip {y}
    rw [← he]
    exact (f.finite_preimage_singleton y).image M.projection
  have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  have : Surjective (f ≫ N.projection) := inferInstance
  have : Surjective (M.projection ≫ g) := hc.w.symm ▸ inferInstance
  have : Surjective g := Surjective.of_comp M.projection g
  have : Flat N.projection := (projection_fpqc N).2.1
  have : GeometricallyIntegral Y.map := Y.geometricallyIntegral
  have : IsIntegral Y.space := GeometricallyIntegral.isIntegral_of_subsingleton Y.map
  have : GeometricallyIntegral N.curve.map := N.curve.geometricallyIntegral
  have : IsIntegral N.curve.space :=
    GeometricallyIntegral.isIntegral_of_subsingleton N.curve.map
  exact ⟨inferInstance, inferInstance, fun y =>
    (finrank_cartesian M.projection f g N.projection hc y).symm⟩

end RamifiedFiniteMap

/-- Descend the prescribed finite surjective map, retaining the input models
through Cartesian refinements and preserving pointwise scheme finrank. -/
theorem ramified_finite_map_model :
    ∀ (X Y : ArithmeticThetaFiniteFieldModelsR0221.Curve ArithmeticThetaFiniteFieldModelsR0221.Omega) (K0 : ArithmeticThetaFiniteFieldModelsR0221.FieldStage), FiniteDimensional ℚ K0 → ∀ (M : ArithmeticThetaFiniteFieldModelsR0221.Model X K0) (N : ArithmeticThetaFiniteFieldModelsR0221.Model Y K0) (f : Quiver.Hom X.space Y.space), CategoryTheory.CategoryStruct.comp f Y.map = X.map → AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Surjective f → ∃ K : ArithmeticThetaFiniteFieldModelsR0221.FieldStage, FiniteDimensional ℚ K ∧ ∃ (M1 : ArithmeticThetaFiniteFieldModelsR0221.Model X K) (N1 : ArithmeticThetaFiniteFieldModelsR0221.Model Y K) (_ : ArithmeticThetaFiniteFieldModelsR0221.Refinement M M1) (_ : ArithmeticThetaFiniteFieldModelsR0221.Refinement N N1) (g : Quiver.Hom M1.curve.space N1.curve.space), CategoryTheory.CategoryStruct.comp g N1.curve.map = M1.curve.map ∧ CategoryTheory.IsPullback M1.projection f g N1.projection ∧ AlgebraicGeometry.IsFinite g ∧ AlgebraicGeometry.Surjective g ∧ ∀ y : Y.space, AlgebraicGeometry.Scheme.Hom.finrank g (N1.projection y) = AlgebraicGeometry.Scheme.Hom.finrank f y := by
  intro X Y K0 hK M N f hf hfinite hsurjective
  have : FiniteDimensional ℚ K0 := hK
  have : IsFinite f := hfinite
  have : Surjective f := hsurjective
  obtain ⟨s, a, ha, hb⟩ := exists_stage_map M N f hf
  let K := stage K0 s
  have h : K0 ≤ K := le_sup_left
  let M1 := extendModel M h
  let N1 := extendModel N h
  let g : M1.curve.space ⟶ N1.curve.space :=
    pullback.lift a (pullback.snd M.curve.map (extensionMap h))
      (hb.trans pullback.condition)
  have hg : g ≫ N1.curve.map = M1.curve.map := pullback.lift_snd _ _ _
  have he : M1.projection ≫ g = f ≫ N1.projection := by
    apply pullback.hom_ext
    · change extendProjection M h ≫ g ≫ pullback.fst _ _ =
        (f ≫ extendProjection N h) ≫ pullback.fst _ _
      dsimp only [g]
      rw [pullback.lift_fst, Category.assoc, extendProjection_fst]
      exact ha
    · change extendProjection M h ≫ g ≫ pullback.snd _ _ =
        (f ≫ extendProjection N h) ≫ pullback.snd _ _
      dsimp only [g]
      rw [pullback.lift_snd, extendProjection_snd, Category.assoc,
        extendProjection_snd, ← Category.assoc, hf]
  have hc : IsPullback M1.projection f g N1.projection :=
    cartesian_of_comparison M1 N1 f hf g hg he
  exact ⟨K, stage_finite K0 s, M1, N1, extendRefinement M h, extendRefinement N h,
    g, hg, hc, RamifiedFiniteMap.properties_of_cartesian M1 N1 f g hg hc⟩

end ArithmeticThetaRamifiedRootModelsR0222

#print axioms ArithmeticThetaRamifiedRootModelsR0222.ramified_finite_map_model
