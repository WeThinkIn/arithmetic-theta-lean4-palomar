module

public import RelativeDiscriminantDefinitionsR0171
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
public import RelativeCurveGeometryR0169
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeDiscriminantR0171
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open scoped TensorProduct

namespace RelativeConormalHodgeGenerator

/-- The conormal exact sequence sends a principal kernel generator to a
spanning differential when the quotient has no relative differentials. -/
lemma tensor_differential_surjective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Subsingleton (KaehlerDifferential R B)]
    (hsurj : Function.Surjective (algebraMap A B))
    (a : A) (hker : RingHom.ker (algebraMap A B) = Ideal.span {a}) :
    Function.Surjective (fun b : B => b •
      ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A a)) := by
  intro ω
  have hzero : KaehlerDifferential.mapBaseChange R A B ω = 0 := Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    R A B hsurj ω).mp hzero
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  have hx : (x : A) ∈ Ideal.span {a} := hker ▸ x.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hx
  have ha : algebraMap A B a = 0 := RingHom.mem_ker.mp
    (hker.symm ▸ Ideal.subset_span (Set.mem_singleton a))
  refine ⟨algebraMap A B r, ?_⟩
  rw [← hv, KaehlerDifferential.kerCotangentToTensor_toCotangent, hr,
    Derivation.leibniz, TensorProduct.tmul_add]
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    ← Algebra.algebraMap_eq_smul_one, ha, TensorProduct.zero_tmul, zero_add]
  rfl


/-- The section-ring algebra on an open of an affine base is unramified. -/
lemma base_sections_unramified (R : Type u) [CommRing R]
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V) :
    letI := Scheme.Hom.sectionsAlgebra (𝟙 (Spec (CommRingCat.of R))) V
    Algebra.FormallyUnramified R Γ(Spec (CommRingCat.of R), V) := by
  letI := Scheme.Hom.sectionsAlgebra (𝟙 (Spec (CommRingCat.of R))) V
  have h₁ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  have h₂ := Scheme.Hom.formallyUnramified_appLE (𝟙 (Spec (CommRingCat.of R)))
    (isAffineOpen_top _) hV (show V ≤ (𝟙 (Spec (CommRingCat.of R))) ⁻¹ᵁ ⊤ from le_top)
  exact h₁.comp h₂

/-- A principal ideal of a section gives a frame of the pulled-back relative
cotangent line. The subopen quantifier is supplied by the affine frame theorem. -/
lemma frame_of_section_kernel {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ X)
    [IsClosedImmersion s] (hs : s ≫ f = 𝟙 _)
    (hΩ : Scheme.Modules.IsInvertible f.kaehler)
    (U : X.affineOpens) (a : Γ(X, U.1))
    (hker : s.ker.ideal U = Ideal.span {a}) :
    IsFrame ((Scheme.Modules.pullback s).obj f.kaehler) (s ⁻¹ᵁ U.1)
      (Scheme.Modules.pullbackLocalSection s
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD f U.1 a)) := by
  let V := s ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage s
  letI := f.sectionsAlgebra U.1
  letI : Algebra Γ(X, U.1) Γ(Spec (CommRingCat.of R), V) := (s.app U.1).hom.toAlgebra
  letI algB : Algebra R Γ(Spec (CommRingCat.of R), V) :=
    ((s.app U.1).hom.comp (algebraMap R Γ(X, U.1))).toAlgebra
  letI : IsScalarTower R Γ(X, U.1) Γ(Spec (CommRingCat.of R), V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have halg : algebraMap R Γ(Spec (CommRingCat.of R), V) =
      @algebraMap R Γ(Spec (CommRingCat.of R), V) _ _
        (Scheme.Hom.sectionsAlgebra (𝟙 (Spec (CommRingCat.of R))) V) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      f.appLE ⊤ U.1 le_top ≫ s.app U.1).hom = _
    rw [s.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hs]
    rfl
  haveI : Algebra.FormallyUnramified R Γ(Spec (CommRingCat.of R), V) := by
    have heq : algB =
        Scheme.Hom.sectionsAlgebra (𝟙 (Spec (CommRingCat.of R))) V :=
      Algebra.algebra_ext _ _ (RingHom.congr_fun halg)
    change @Algebra.FormallyUnramified R Γ(Spec (CommRingCat.of R), V) _ _ algB
    rw [heq]
    exact base_sections_unramified R V hV
  have hker' : RingHom.ker (algebraMap Γ(X, U.1) Γ(Spec (CommRingCat.of R), V)) =
      Ideal.span {a} := by
    change RingHom.ker (s.app U.1).hom = Ideal.span {a}
    simpa only [Scheme.Hom.ker_apply] using hker
  have hgen := tensor_differential_surjective (R := R)
    (s.app_surjective U.1 U.2) a hker'
  let e := LinearEquiv.ofBijective (f.kaehlerToSectionsₗ U.1)
    (f.kaehlerToSections_bijective_of_isAffineOpen U.2)
  obtain ⟨β, hβ⟩ := hΩ.exists_baseChange_sections_linearEquiv_pullback_of_le
    s U.1 U.2 V hV le_rfl
  have hgen' : Function.Surjective (fun b : Γ(Spec (CommRingCat.of R), V) =>
      b • Scheme.Modules.pullbackLocalSection s
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD f U.1 a)) := by
    intro z
    obtain ⟨w, hw⟩ := β.surjective z
    obtain ⟨v, hv⟩ := (LinearEquiv.baseChange Γ(X, U.1) Γ(Spec (CommRingCat.of R), V) _ _ e).surjective w
    obtain ⟨b, hb⟩ := hgen v
    refine ⟨b, ?_⟩
    rw [← hw, ← hv, ← hb, map_smul, map_smul]
    rw [LinearEquiv.baseChange_tmul, hβ]
    change b • _ = b • (((Scheme.Modules.pullback s).obj f.kaehler).presheaf.map
      (homOfLE (le_refl V)).op _)
    congr 1
    exact (CategoryTheory.Functor.map_id_apply _ _ _).symm
  have hspan : Submodule.span Γ(Spec (CommRingCat.of R), V)
      {Scheme.Modules.pullbackLocalSection s
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD f U.1 a)} = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨b, rfl⟩ := hgen' z
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hframe := (hΩ.pullback s).isFrameOn_of_isAffineOpen_of_span_singleton_eq_top hV _ hspan
  exact fun W hW => hframe hW hW

end RelativeConormalHodgeGenerator
/-- The actual differential of any local Cartier equation of the origin is
an intrinsic frame of the relative Hodge sheaf on every subopen. -/
theorem relative_conormal_hodge_generator :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (U : (ArithmeticThetaRelativeKatoR0169.Curve R W).affineOpens) [Nonempty U.1] (a : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj (Opposite.op U.1)) (ha : IsRegular a) (hI : (ArithmeticThetaRelativeKatoNaturalityR0170.identityIdeal R W).ideal U = Ideal.span ({a} : Set _)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W) ((TopologicalSpace.Opens.map (ArithmeticThetaRelativeKatoR0169.origin R W).base).obj U.1) (ArithmeticThetaRelativeDiscriminantR0171.localDifferential R W U.1 a) := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG U _ a ha hI
  let : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (relative_curve_geometry R W).2.2.2.2.2.1
  let : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hs : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  have : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [hs]
    infer_instance
  let : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  have hΩ : Scheme.Modules.IsInvertible (structureMap R W).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap R W).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  exact RelativeConormalHodgeGenerator.frame_of_section_kernel
    (structureMap R W) (origin R W) hs hΩ U a hI

#print axioms relative_conormal_hodge_generator
end ArithmeticThetaRelativeDiscriminantR0171
