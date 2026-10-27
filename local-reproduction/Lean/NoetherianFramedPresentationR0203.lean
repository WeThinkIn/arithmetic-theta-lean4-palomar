import NoetherianPoleFiltrationR0203
import ArbitrarySmoothDiscriminantR0203

/-! Noetherian framed presentation. The general algebraic and canonical-map engines
are reused from r0174; geometric specializations here allow nilpotents and the zero ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
universe u
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open ArithmeticThetaLocalWeierstrassR0203

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.SectionRing
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173

/-- The framed curve has an actual graded section ring for the inverse
origin ideal.  This packages all positive origin-power sections and their
multiplication without choosing bases or assuming a presentation. -/
theorem exists_origin_section_ring (R : Type u) [CommRing R] 
    [IsNoetherianRing R]  [Algebra ℚ R]
    (Q : FramedCurve R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (𝓐 : ℕ → Submodule R A) (_ : GradedAlgebra 𝓐)
      (ι : ∀ m : ℕ, 𝓐 m → Γ(((Q.zero).ker.invModule).tensorPow m, ⊤)),
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing Q.structureMap
        (Q.zero).ker.invModule A 𝓐 ι := by
  let I := (Q.zero).ker
  have hI : I.IsInvertible := Q.zero_ideal_invertible
  exact AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
    Q.structureMap I.invModule hI.isInvertible_invModule

end
end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.SectionRing

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open SectionExact
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)

/-- Surjectivity for the actual adjunction restriction map to the origin subscheme. -/




lemma surjective_identity_tensorPower (m : ℕ) (hm : 0 < m) :
    Function.Surjective (Scheme.Modules.pullbackLocalSection Q.zero
      (L := Q.zero.ker.invModule.tensorPow (m+1)) (U := ⊤)) := by
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible (m+1)
  exact surjective_pullback_of_iso Q.zero δ (NoetherianPoleFiltration.surjective_identity_restriction R Q m hm)


/-- A frame of the actual inverse origin ideal restricted to the identity. -/
def identityLineFrame : (Scheme.Modules.pullback Q.zero).obj Q.zero.ker.invModule ≅
    𝟙_ (Spec (CommRingCat.of R)).Modules := by
  let η := (NoetherianPoleFiltration.origin_power_restriction_trivial R Q 1 (by omega)).some
  simpa only [pow_one] using η

/-- Tensor-compatible restriction, before identifying powers of the unit line. -/
def powerRestriction (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    Γ((𝟙_ (Spec (CommRingCat.of R)).Modules).tensorPow m, ⊤) :=
  ((Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
      Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m).hom.app ⊤)
    (Scheme.Modules.pullbackLocalSection Q.zero s)


lemma exists_normalized_section (m : ℕ) (hm : 0 < m) :
    ∃ s : Γ(Q.zero.ker.invModule.tensorPow (m+1), ⊤),
      powerRestriction R Q (m+1) s = unitPower R (m+1) := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule (m+1) ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) (m+1)
  obtain ⟨s,hs⟩ := surjective_identity_tensorPower R Q m hm
    (η.inv.app ⊤ (unitPower R (m+1)))
  refine ⟨s, ?_⟩
  change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s) = _
  rw [hs]
  change (η.inv ≫ η.hom).app ⊤ (unitPower R (m+1)) = _
  rw [η.inv_hom_id]
  rfl

lemma powerRestriction_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤)) :
    powerRestriction R Q (m+n)
      ((Scheme.Modules.tensorPowAdd Q.zero.ker.invModule m n).hom.app ⊤
        (Scheme.Modules.tensorSections s t)) =
      (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (CommRingCat.of R)).Modules) m n).hom.app ⊤
        (Scheme.Modules.tensorSections (powerRestriction R Q m s) (powerRestriction R Q n t)) :=
  Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
    Q.zero Q.zero.ker.invModule _ (identityLineFrame R Q) m n s t

lemma normalized_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤))
    (hs : powerRestriction R Q m s = unitPower R m)
    (ht : powerRestriction R Q n t = unitPower R n) :
    powerRestriction R Q (m+n)
      ((Scheme.Modules.tensorPowAdd Q.zero.ker.invModule m n).hom.app ⊤
        (Scheme.Modules.tensorSections s t)) = unitPower R (m+n) := by
  rw [powerRestriction_mul, hs, ht]
  exact Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection _ m n

lemma exists_normalized_coordinates :
    ∃ (x : Γ(Q.zero.ker.invModule.tensorPow 2, ⊤))
      (y : Γ(Q.zero.ker.invModule.tensorPow 3, ⊤)),
      powerRestriction R Q 2 x = unitPower R 2 ∧
      powerRestriction R Q 3 y = unitPower R 3 := by
  obtain ⟨x,hx⟩ := exists_normalized_section R Q 1 (by omega)
  obtain ⟨y,hy⟩ := exists_normalized_section R Q 2 (by omega)
  exact ⟨x,y,hx,hy⟩



lemma powerRestriction_sub (m : ℕ) (s t : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    powerRestriction R Q m (s-t) = powerRestriction R Q m s - powerRestriction R Q m t := by
  unfold powerRestriction
  rw [Scheme.Modules.pullbackLocalSection_sub, map_sub]

/-- The leading polar coefficients of y² and x³ agree.  The full cubic relation
requires the subsequent filtration descent, which is not asserted here. -/
lemma exists_coordinates_cubic_difference_restricts_zero :
    ∃ (x : Γ(Q.zero.ker.invModule.tensorPow 2, ⊤))
      (y : Γ(Q.zero.ker.invModule.tensorPow 3, ⊤)),
      powerRestriction R Q 2 x = unitPower R 2 ∧
      powerRestriction R Q 3 y = unitPower R 3 ∧
      powerRestriction R Q 6
        (sectionMul R Q 3 3 y y - sectionMul R Q 4 2 (sectionMul R Q 2 2 x x) x) = 0 := by
  obtain ⟨x,y,hx,hy⟩ := exists_normalized_coordinates R Q
  refine ⟨x,y,hx,hy,?_⟩
  rw [powerRestriction_sub]
  have hy2 := normalized_mul R Q 3 3 y y hy hy
  have hx2 := normalized_mul R Q 2 2 x x hx hx
  have hx3 := normalized_mul R Q 4 2 (sectionMul R Q 2 2 x x) x hx2 hx
  exact sub_eq_zero.mpr (hy2.trans hx3.symm)


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory



variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)

/-- The actual zero restriction criterion gives a lift through multiplication
by the actual ideal inclusion, before cancelling its inverse line. -/
lemma exists_ideal_lift (m : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (hs : powerRestriction R Q m s = 0) :
    ∃ t : Γ(Q.zero.ker.invModule.tensorPow m ⊗ Q.zero.ker.module, ⊤),
      ((Q.zero.ker.invModule.tensorPow m ◁ Q.zero.ker.moduleι) ≫
        (ρ_ (Q.zero.ker.invModule.tensorPow m)).hom).app ⊤ t = s := by
  let I := Q.zero.ker
  let M := I.invModule.tensorPow m
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero I.invModule m ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m
  have hzero : Scheme.Modules.pullbackLocalSection Q.zero s = 0 :=
    (Scheme.Modules.Hom.mono_iff_injective η.hom).mp inferInstance ⊤
      (by
        rw [map_zero]
        exact hs)
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by
    rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  have hz := restriction_zero_of_iso_hom_comp_eq I.subschemeι (asIso Q.zero.toImage)
    Q.zero Q.zero.toImage_imageι M s hzero
  obtain ⟨δ⟩ := invPower_tensorPower I Q.zero_ideal_invertible m
  have hMinv : Scheme.Modules.IsInvertible M := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨ε⟩⟩ := (Q.zero_ideal_invertible.pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ.symm ≪≫ ε⟩⟩
  have hM : Scheme.Modules.IsLocallyFreeOfRank 1 M :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hMinv
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I M hM
  haveI := hS.mono_f
  exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
    (ShortComplex.mk _ _ w) hS.exact ⊤ s hz


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
variable {X : Scheme.{u}}







variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)




lemma exists_pole_filtration_factor (m : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow (m+1), ⊤))
    (hs : powerRestriction R Q (m+1) s = 0) :
    ∃ t : Γ(Q.zero.ker.invModule.tensorPow m, ⊤),
      sectionMul R Q m 1 t (originDegreeOne R Q) = s := by
  obtain ⟨v,hv⟩ := exists_ideal_lift R Q (m+1) s hs
  obtain ⟨t,ht⟩ := exists_tensor_factor Q.zero.ker (originPairing R Q)
    (Q.zero.ker.invModule.tensorPow m) s v hv
  refine ⟨t, ?_⟩
  change (Scheme.Modules.tensorPowAdd _ m 1).hom.app ⊤
    (Scheme.Modules.tensorSections t (Scheme.Modules.tensorPowSection (originSection R Q) 1)) = s
  rw [tensorPowAdd_one_section]
  exact ht


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite


variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)

lemma unitPower_isFrame (m : ℕ) : Scheme.Modules.IsFrameOn (unitPower R m) ⊤ :=
  (Scheme.Modules.isFrameOn_unitSection ⊤).tensorPowSection m


def unitPowerScalarEquiv (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    R ≃ₗ[R] Γ((𝟙_ (Spec (.of R)).Modules).tensorPow m, ⊤) :=
  frameScalarEquiv (𝟙 _) (by simpa using Function.bijective_id) _ (unitPower R m) (unitPower_isFrame R m)


def identityRestrictionLinear (M : Q.target.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj M) ⊤
    Γ(M,⊤) →ₗ[R] Γ((Scheme.Modules.pullback Q.zero).obj M, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj M) ⊤
  refine { toFun := Scheme.Modules.pullbackLocalSection Q.zero
           map_add' := Scheme.Modules.pullbackLocalSection_add Q.zero
           map_smul' := ?_ }
  intro r s
  change Scheme.Modules.pullbackLocalSection Q.zero
    ((Q.structureMap.constToPresheaf.app (op ⊤)).hom r • s) =
    ((Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op (Q.zero ⁻¹ᵁ ⊤))).hom r •
      Scheme.Modules.pullbackLocalSection Q.zero s
  rw [Scheme.Modules.pullbackLocalSection_smul]
  have h := congrArg (fun f : CommRingCat.of R ⟶ _ => f.hom r)
    (Conormal.section_scalar Q.structureMap Q.zero Q.zero_over ⊤)
  exact congrArg (fun a => a • Scheme.Modules.pullbackLocalSection Q.zero s) h

def powerRestrictionLinear (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    Γ(Q.zero.ker.invModule.tensorPow m, ⊤) →ₗ[R]
      Γ((𝟙_ (Spec (.of R)).Modules).tensorPow m, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj (Q.zero.ker.invModule.tensorPow m)) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  exact (FibreCohomology.sectionsIsoLinear (𝟙 (Spec (.of R)))
    (Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
      Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m) ⊤).toLinearMap ∘ₗ
        identityRestrictionLinear R Q _

def leadingCoefficient (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
    Γ(Q.zero.ker.invModule.tensorPow m, ⊤) →ₗ[R] R := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  exact (unitPowerScalarEquiv R m).symm.toLinearMap ∘ₗ powerRestrictionLinear R Q m

lemma leadingCoefficient_spec (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    powerRestriction R Q m s = leadingCoefficient R Q m s • unitPower R m := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  change powerRestriction R Q m s = (unitPowerScalarEquiv R m)
    ((unitPowerScalarEquiv R m).symm (powerRestriction R Q m s))
  exact ((unitPowerScalarEquiv R m).apply_symm_apply (powerRestriction R Q m s)).symm

lemma leadingCoefficient_eq_zero_iff (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    leadingCoefficient R Q m s = 0 ↔ powerRestriction R Q m s = 0 := by
  change (unitPowerScalarEquiv R m).symm (powerRestriction R Q m s) = 0 ↔ _
  exact (unitPowerScalarEquiv R m).symm.map_eq_zero_iff


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)


lemma originSection_identity_zero : Scheme.Modules.pullbackLocalSection Q.zero (originSection R Q) = 0 := by
  let I := Q.zero.ker
  let L := I.invModule
  have hL : Scheme.Modules.IsLocallyFreeOfRank 1 L :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr Q.zero_ideal_invertible.isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I L hL
  have hzmap : idealSectionRight I (originPairing R Q) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L = 0 := by
    change (originPairing R Q).inv ≫ ((L ◁ I.moduleι) ≫ (ρ_ L).hom) ≫ _ = 0
    rw [w, CategoryTheory.Limits.comp_zero]
  have hz : Scheme.Modules.pullbackLocalSection I.subschemeι (originSection R Q) = 0 :=
    congrArg (fun f => f.app ⊤ (Scheme.Modules.unitSection ⊤)) hzmap
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  let e := asIso Q.zero.toImage
  have he : e.hom ≫ I.subschemeι = Q.zero := Q.zero.toImage_imageι
  have hcomp := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection e.hom I.subschemeι L ⊤
    (originSection R Q)
  rw [hz, Scheme.Modules.pullbackLocalSection_zero, map_zero] at hcomp
  exact restriction_zero_congr (e.hom ≫ I.subschemeι) Q.zero he L (originSection R Q) hcomp.symm

lemma originDegreeOne_restriction_zero : powerRestriction R Q 1 (originDegreeOne R Q) = 0 := by
  let L := Q.zero.ker.invModule
  have hunit : (λ_ L).inv.app ⊤ (originSection R Q) = originDegreeOne R Q := by
    apply (Scheme.Modules.Hom.mono_iff_injective (λ_ L).hom).mp inferInstance ⊤
    change ((λ_ L).inv ≫ (λ_ L).hom).app ⊤ (originSection R Q) = _
    rw [Iso.inv_hom_id]
    change originSection R Q = (λ_ L).hom.app ⊤
      (Scheme.Modules.tensorSections (Scheme.Modules.unitSection ⊤) (originSection R Q))
    simpa only [Scheme.Modules.unitSection, one_smul] using
      (Scheme.Modules.leftUnitor_hom_app_tensorSections (1 : Γ(Q.target, ⊤)) (originSection R Q)).symm
  have hpb := Scheme.Modules.pullbackLocalSection_app Q.zero (λ_ L).inv (originSection R Q)
  rw [originSection_identity_zero, map_zero] at hpb
  have hz : Scheme.Modules.pullbackLocalSection Q.zero (originDegreeOne R Q) = 0 := by
    rw [hunit] at hpb
    exact hpb
  unfold powerRestriction
  rw [hz, map_zero]


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite


variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
lemma sectionMul_origin_injective (m : ℕ) :
    Function.Injective (fun s : Γ(Q.zero.ker.invModule.tensorPow m,⊤) =>
      sectionMul R Q m 1 s (originDegreeOne R Q)) := by
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible (m+1)
  have hM : Scheme.Modules.IsInvertible (Q.zero.ker.invModule.tensorPow (m+1)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨ε⟩⟩ := (Q.zero_ideal_invertible.pow (m+1)).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ.symm ≪≫ ε⟩⟩
  have hi := tensor_originSection_injective Q.zero.ker (originPairing R Q)
    (Q.zero.ker.invModule.tensorPow m) hM
  intro a b hab
  apply hi
  unfold sectionMul originDegreeOne at hab
  dsimp only at hab
  rw [tensorPowAdd_one_section, tensorPowAdd_one_section] at hab
  exact hab

lemma leadingCoefficient_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (leadingCoefficient R Q (m+1)) := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule (m+1) ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) (m+1)
  intro r
  obtain ⟨s,hs⟩ := surjective_identity_tensorPower R Q m hm
    (η.inv.app ⊤ ((unitPowerScalarEquiv R (m+1)) r))
  refine ⟨s, ?_⟩
  apply (unitPowerScalarEquiv R (m+1)).injective
  change (unitPowerScalarEquiv R (m+1)) ((unitPowerScalarEquiv R (m+1)).symm
    (powerRestriction R Q (m+1) s)) = _
  rw [LinearEquiv.apply_symm_apply]
  change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s) = _
  rw [hs]
  change (η.inv ≫ η.hom).app ⊤ ((unitPowerScalarEquiv R (m+1)) r) = _
  rw [η.inv_hom_id]
  rfl


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)

lemma unitPowerScalar_mul (m n : ℕ) (r t : R) :
    (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (.of R)).Modules) m n).hom.app ⊤
      (Scheme.Modules.tensorSections ((unitPowerScalarEquiv R m) r) ((unitPowerScalarEquiv R n) t)) =
        (unitPowerScalarEquiv R (m+n)) (r*t) := by
  let a : R →+* Γ(Spec (.of R), ⊤) :=
    ((Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op ⊤)).hom
  change (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (.of R)).Modules) m n).hom.app ⊤
    (Scheme.Modules.tensorSections (a r • unitPower R m) (a t • unitPower R n)) =
      a (r*t) • unitPower R (m+n)
  rw [Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, smul_smul, ← map_mul]
  exact congrArg (fun b => a (r*t) • b)
    (Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection _ m n)

lemma leadingCoefficient_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤)) :
    leadingCoefficient R Q (m+n) (sectionMul R Q m n s t) =
      leadingCoefficient R Q m s * leadingCoefficient R Q n t := by
  apply (unitPowerScalarEquiv R (m+n)).injective
  change (unitPowerScalarEquiv R (m+n)) ((unitPowerScalarEquiv R (m+n)).symm
    (powerRestriction R Q (m+n) (sectionMul R Q m n s t))) = _
  rw [LinearEquiv.apply_symm_apply]
  unfold sectionMul
  rw [powerRestriction_mul]
  have hs : powerRestriction R Q m s = (unitPowerScalarEquiv R m) (leadingCoefficient R Q m s) :=
    leadingCoefficient_spec R Q m s
  have ht : powerRestriction R Q n t = (unitPowerScalarEquiv R n) (leadingCoefficient R Q n t) :=
    leadingCoefficient_spec R Q n t
  rw [hs,ht]
  exact unitPowerScalar_mul R m n _ _

lemma leadingCoefficient_normalized (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (hs : powerRestriction R Q m s = unitPower R m) : leadingCoefficient R Q m s = 1 := by
  apply (unitPowerScalarEquiv R m).injective
  change (unitPowerScalarEquiv R m) ((unitPowerScalarEquiv R m).symm (powerRestriction R Q m s)) = _
  rw [LinearEquiv.apply_symm_apply, hs]
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
    ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  change unitPower R m = (1 : R) • unitPower R m
  exact (one_smul _ _).symm



lemma degreeOne_restriction_zero (s : Γ(Q.zero.ker.invModule.tensorPow 1, ⊤)) :
    powerRestriction R Q 1 s = 0 := by
  let L := Q.zero.ker.invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap (L.tensorPow 1) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap (Q.zero.ker ^ 1).invModule ⊤
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible 1
  obtain ⟨ε⟩ := NoetherianPoleFiltration.origin_first_sections R Q
  let e := FibreCohomology.sectionsIsoLinear Q.structureMap δ.symm ⊤ ≪≫ₗ ε
  let η := SectionExact.unit_sections Q.structureMap
    (NoetherianPoleFiltration.structure_app_bijective R Q ⊤)
  let f := LinearMap.toSpanSingleton R Γ(L.tensorPow 1, ⊤) (originDegreeOne R Q)
  have hf : Function.Injective f := by
    intro a b hab
    apply η.injective
    apply tensor_originSection_injective Q.zero.ker (originPairing R Q) (𝟙_ Q.target.Modules)
      (by simpa only [Scheme.Modules.tensorPow_succ, Scheme.Modules.tensorPow_zero] using
        (Q.zero_ideal_invertible.isInvertible_invModule.tensorPow 1))
    have hη (r : R) : η r = GradedOAlgebra.baseScalar Q.structureMap r •
        Scheme.Modules.unitSection (X := Q.target) ⊤ := by
      rw [Scheme.Modules.smul_unitSection]
      change ((Scheme.ΓSpecIso (.of R)).inv ≫ Q.structureMap.appLE ⊤ ⊤ le_top).hom r =
        (Q.structureMap.app ⊤).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
      rw [Scheme.Hom.app_eq_appLE]
      rfl
    dsimp only
    rw [hη a, hη b,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_left]
    change (Q.structureMap.constToPresheaf.app (op ⊤)).hom a • originDegreeOne R Q =
      (Q.structureMap.constToPresheaf.app (op ⊤)).hom b • originDegreeOne R Q at hab
    rw [← GeometricCubic.baseScalar_eq_const, ← GeometricCubic.baseScalar_eq_const] at hab
    simpa only [originDegreeOne, Scheme.Modules.tensorPowSection_one, originSection] using hab
  have hgf : leadingCoefficient R Q 1 ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro r
    change leadingCoefficient R Q 1 (r • originDegreeOne R Q) = 0
    rw [map_smul, (leadingCoefficient_eq_zero_iff R Q 1 _).mpr
      (originDegreeOne_restriction_zero R Q), smul_zero]
  have hg := NoetherianPoleFiltration.functional_zero_of_rank_one e.symm f
    (leadingCoefficient R Q 1) hf hgf
  apply (leadingCoefficient_eq_zero_iff R Q 1 s).mp
  exact LinearMap.congr_fun hg s

lemma degreeOne_generated (s : Γ(Q.zero.ker.invModule.tensorPow 1, ⊤)) :
    ∃ r : R, s = (GradedOAlgebra.baseScalar Q.structureMap r) • originDegreeOne R Q := by
  obtain ⟨t,ht⟩ := exists_pole_filtration_factor R Q 0 s (degreeOne_restriction_zero R Q s)
  let η := SectionExact.unit_sections Q.structureMap (NoetherianPoleFiltration.structure_app_bijective R Q ⊤)
  obtain ⟨r,hr⟩ := η.surjective t
  refine ⟨r, ?_⟩
  rw [← ht]
  unfold sectionMul originDegreeOne
  rw [tensorPowAdd_one_section]
  change Scheme.Modules.tensorSections t (originSection R Q) = _
  have hscalar : t = GradedOAlgebra.baseScalar Q.structureMap r •
      Scheme.Modules.unitSection (X := Q.target) ⊤ := by
    rw [← hr]
    rw [Scheme.Modules.smul_unitSection]
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ Q.structureMap.appLE ⊤ ⊤ le_top).hom r =
      (Q.structureMap.app ⊤).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [hscalar, Scheme.Modules.tensorSections_smul_left]
  rfl


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Filtration

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)



def gradedLead (m : ℕ) : 𝓐 m →ₗ[R] R := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  exact leadingCoefficient R Q m ∘ₗ (sectionLinearEquiv R Q A 𝓐 ι hRing m).toLinearMap

include hRing
lemma gradedLead_mul (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n) :
    gradedLead R Q A 𝓐 ι hRing (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ =
      gradedLead R Q A 𝓐 ι hRing m a * gradedLead R Q A 𝓐 ι hRing n b := by
  change leadingCoefficient R Q (m+n) (ι (m+n) _) = _
  rw [hRing.map_mul]
  exact leadingCoefficient_mul R Q m n (ι m a) (ι n b)

lemma gradedLead_drop (z : 𝓐 1) (hz : ι 1 z = originDegreeOne R Q)
    (m : ℕ) (a : 𝓐 (m+1)) (ha : gradedLead R Q A 𝓐 ι hRing (m+1) a = 0) :
    ∃ b : 𝓐 m, (z:A)*b = a := by
  have ha' : powerRestriction R Q (m+1) (ι (m+1) a) = 0 :=
    (leadingCoefficient_eq_zero_iff R Q (m+1) _).mp ha
  obtain ⟨t,ht⟩ := exists_pole_filtration_factor R Q m (ι (m+1) a) ha'
  obtain ⟨b,hb⟩ := (hRing.bijective m).2 t
  refine ⟨b, ?_⟩
  have hba : (⟨(b:A)*z, SetLike.mul_mem_graded b.2 z.2⟩ : 𝓐 (m+1)) = a := by
    apply (hRing.bijective (m+1)).1
    rw [hRing.map_mul, hb, hz]
    exact ht
  simpa only [mul_comm] using congrArg Subtype.val hba

lemma graded_degree_one (z : 𝓐 1) (hz : ι 1 z = originDegreeOne R Q) (a : 𝓐 1) :
    ∃ r : R, (a:A) = algebraMap R A r * z := by
  obtain ⟨r,hr⟩ := degreeOne_generated R Q (ι 1 a)
  refine ⟨r, ?_⟩
  have h : a = r • z := by
    apply (hRing.bijective 1).1
    rw [hRing.map_smul, hz]
    exact hr
  simpa only [Submodule.coe_smul, Algebra.smul_def] using congrArg Subtype.val h

/-- The cubic relation in the actual section ring, with the origin section
and coordinates whose leading polar coefficients are one. -/
lemma exists_sectionRing_cubic :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (a1 a2 a3 a4 a6 : R),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      (y:A)^2 + algebraMap R A a1 * x * y * z + algebraMap R A a3 * y * z^3 =
        (x:A)^3 + algebraMap R A a2 * x^2 * z^2 +
          algebraMap R A a4 * x * z^4 + algebraMap R A a6 * z^6 := by
  obtain ⟨z,hz⟩ := (hRing.bijective 1).2 (originDegreeOne R Q)
  obtain ⟨sx,sy,hsx,hsy⟩ := exists_normalized_coordinates R Q
  obtain ⟨x,hx⟩ := (hRing.bijective 2).2 sx
  obtain ⟨y,hy⟩ := (hRing.bijective 3).2 sy
  have hx' : powerRestriction R Q 2 (ι 2 x) = unitPower R 2 := by rw [hx]; exact hsx
  have hy' : powerRestriction R Q 3 (ι 3 y) = unitPower R 3 := by rw [hy]; exact hsy
  obtain ⟨a1,a2,a3,a4,a6,heq⟩ := CubicAlgebra.cubic_of_exact_pole_filtration 𝓐
    (gradedLead R Q A 𝓐 ι hRing) z (gradedLead_drop R Q A 𝓐 ι hRing z hz)
    (gradedLead_mul R Q A 𝓐 ι hRing) (graded_degree_one R Q A 𝓐 ι hRing z hz)
    x y (leadingCoefficient_normalized R Q 2 _ hx') (leadingCoefficient_normalized R Q 3 _ hy')
  exact ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx',hy',heq⟩

omit hRing in
/-- Coordinates and a Weierstrass equation are constructed on the actual inverse
origin-ideal section ring. No coordinate, basis or relation is assumed. -/
theorem exists_origin_cubic :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R),
        j 1 z = originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x) = unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y) = unitPower R 3 ∧
        (y:B)^2 + algebraMap R B W.a₁ * x * y * z + algebraMap R B W.a₃ * y * z^3 =
          (x:B)^3 + algebraMap R B W.a₂ * x^2 * z^2 +
            algebraMap R B W.a₄ * x * z^4 + algebraMap R B W.a₆ * z^6 := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  obtain ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx,hy,hrel⟩ := exists_sectionRing_cubic R Q B 𝓑 j hj
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,z,x,y,⟨a1,a2,a3,a4,a6⟩,hz,hx,hy,hrel⟩


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma graded_degree_zero (a : 𝓐 0) : ∃ r : R, (a:A) = algebraMap R A r := by
  let η := SectionExact.unit_sections Q.structureMap (NoetherianPoleFiltration.structure_app_bijective R Q ⊤)
  obtain ⟨r,hr⟩ := η.surjective (ι 0 a)
  have ha : a = r • (⟨1, SetLike.GradedOne.one_mem⟩ : 𝓐 0) := by
    apply (hRing.bijective 0).1
    rw [hRing.map_smul, hRing.map_one, Scheme.Modules.smul_unitSection]
    rw [← hr]
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ Q.structureMap.appLE ⊤ ⊤ le_top).hom r =
      (Q.structureMap.app ⊤).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨r, ?_⟩
  simpa only [Submodule.coe_smul, Algebra.smul_def, mul_one] using congrArg Subtype.val ha

lemma coordinates_generate (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A) = ⊤ := by
  exact Generation.adjoin_eq_top 𝓐 (gradedLead R Q A 𝓐 ι hRing) x y
    (gradedLead_mul R Q A 𝓐 ι hRing) z (gradedLead_drop R Q A 𝓐 ι hRing z hz)
    (graded_degree_zero R Q A 𝓐 ι hRing) (graded_degree_one R Q A 𝓐 ι hRing z hz)
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)


include hRing
lemma coordinates_aeval_surjective (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    Function.Surjective (MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]) := by
  apply (AlgHom.range_eq_top _).mp
  rw [← Algebra.adjoin_range_eq_range_aeval]
  have hr : Set.range ![(z:A),(x:A),(y:A)] = ({(z:A),(x:A),(y:A)} : Set A) := by
    ext a
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  rw [hr]
  exact coordinates_generate R Q A 𝓐 ι hRing z x y hz hx hy

lemma exists_surjective_polynomial_map_cubic :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      Function.Surjective (MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]) ∧
      MvPolynomial.aeval ![(z:A),(x:A),(y:A)] (weightedCubic R W) = 0 := by
  obtain ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx,hy,hrel⟩ := exists_sectionRing_cubic R Q A 𝓐 ι hRing
  refine ⟨z,x,y,⟨a1,a2,a3,a4,a6⟩,hz,hx,hy,coordinates_aeval_surjective R Q A 𝓐 ι hRing z x y hz hx hy, ?_⟩
  simpa [weightedCubic] using sub_eq_zero.mpr hrel


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Kernel
open Filtration GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (z : 𝓐 1)
variable (R)  [IsNoetherianRing R]  [Algebra ℚ R]
  (Q : FramedCurve R)
variable (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma graded_z_mul_injective (hz : ι 1 z = originDegreeOne R Q) (n : ℕ) :
    Function.Injective (fun a : 𝓐 n => (z:A)*a) := by
  intro a b hab
  have h : (⟨(a:A)*z,SetLike.mul_mem_graded a.2 z.2⟩ : 𝓐 (n+1)) =
      ⟨(b:A)*z,SetLike.mul_mem_graded b.2 z.2⟩ :=
    Subtype.ext (by simpa only [mul_comm] using hab)
  have he := congrArg (ι (n+1)) h
  rw [hRing.map_mul,hRing.map_mul,hz] at he
  apply (hRing.bijective n).1
  exact sectionMul_origin_injective R Q n he

lemma actual_z_mul_injective (hz : ι 1 z = originDegreeOne R Q) :
    Function.Injective (fun a : A => (z:A)*a) :=
  z_mul_injective 𝓐 z (graded_z_mul_injective (R := R) (𝓐 := 𝓐) (z := z) (Q := Q) (ι := ι) (hRing := hRing) hz)

lemma gradedLead_one : gradedLead R Q A 𝓐 ι hRing 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1 := by
  apply leadingCoefficient_normalized R Q 0
  change powerRestriction R Q 0 (ι 0 ⟨1,SetLike.GradedOne.one_mem⟩) = unitPower R 0
  rw [hRing.map_one]
  exact Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection
    Q.zero Q.zero.ker.invModule _ (identityLineFrame R Q)


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.Kernel

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Filtration Kernel
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_cubic_kernel (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (hrel : MvPolynomial.aeval ![(z:A),(x:A),(y:A)] (weightedCubic R W) = 0) :
    RingHom.ker (MvPolynomial.aeval ![(z:A),(x:A),(y:A)]).toRingHom =
      Ideal.span {weightedCubic R W} := by
  nontriviality R
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z = 0 := by
    change leadingCoefficient R Q 1 (ι 1 z) = 0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hmod := normalPair_mod_z 𝓐 lead (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R := R) (𝓐 := 𝓐) (Q := Q) (ι := ι) (hRing := hRing)) z x y hzlead
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)
  have hzinj := actual_z_mul_injective (R := R) (𝓐 := 𝓐) (z := z) (Q := Q) (ι := ι) (hRing := hRing) hz
  ext p
  rw [RingHom.mem_ker,Ideal.mem_span_singleton]
  exact weightedCubic_dvd_iff_eval_zero (x:A) (y:A) (z:A) W hzinj hmod hrel p

lemma exists_cubic_quotient_equiv :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
      (e : (MvPolynomial (Fin 3) R ⧸ Ideal.span {weightedCubic R W}) ≃ₐ[R] A),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      ∀ p : MvPolynomial (Fin 3) R,
        e (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ![(z:A),(x:A),(y:A)] p := by
  obtain ⟨z,x,y,W,hz,hx,hy,hsurj,hrel⟩ := exists_surjective_polynomial_map_cubic R Q A 𝓐 ι hRing
  let f := MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]
  have hk := actual_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hrel
  let e := (Ideal.quotientEquivAlgOfEq R hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨z,x,y,W,e,hz,hx,hy,?_⟩
  intro p
  change Ideal.quotientKerAlgEquivOfSurjective hsurj
    (Ideal.quotientEquivAlgOfEq R hk.symm (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hsurj p

omit hRing in
/-- The actual origin section ring has the constructed weighted cubic presentation. -/
theorem exists_origin_cubic_quotient :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R)
        (e : (MvPolynomial (Fin 3) R ⧸ Ideal.span {weightedCubic R W}) ≃ₐ[R] B),
        j 1 z = originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x) = unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y) = unitPower R 3 ∧
        ∀ p : MvPolynomial (Fin 3) R,
          e (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ![(z:B),(x:B),(y:B)] p := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,exists_cubic_quotient_equiv R Q B 𝓑 j hj⟩


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Filtration Kernel PlaneCoordinates
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_degree_three_basis (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    ∃ b : Module.Basis (Fin 3) R (𝓐 3),
      (fun i => ((b i : 𝓐 3) : A)) = ![(z:A)^3,(x:A)*z,(y:A)] := by
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hxlead := leadingCoefficient_normalized R Q 2 _ hx
  have hylead := leadingCoefficient_normalized R Q 3 _ hy
  exact ⟨degreeThreeBasis 𝓐 lead z x y (gradedLead_drop R Q A 𝓐 ι hRing z hz)
      (graded_degree_one R Q A 𝓐 ι hRing z hz) (gradedLead_mul R Q A 𝓐 ι hRing)
      (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
      (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
      hzlead hxlead hylead,
    degreeThreeBasis_coe 𝓐 lead z x y (gradedLead_drop R Q A 𝓐 ι hRing z hz)
      (graded_degree_one R Q A 𝓐 ι hRing z hz) (gradedLead_mul R Q A 𝓐 ι hRing)
      (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
      (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
      hzlead hxlead hylead⟩

lemma actual_third_veronese_generated (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (n : ℕ) (a : 𝓐 (3*n)) :
    (a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
  exact VeroneseGeneration.third_veronese_generated 𝓐 (gradedLead R Q A 𝓐 ι hRing) z x y
    (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
    (gradedLead_drop R Q A 𝓐 ι hRing z hz) (graded_degree_zero R Q A 𝓐 ι hRing)
    (graded_degree_one R Q A 𝓐 ι hRing z hz)
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy) n a


omit [IsNoetherianRing R] [Algebra ℚ R] hRing in
lemma plane_polynomial_aeval (W : WeierstrassCurve R) (z x y : A) :
    MvPolynomial.aeval ![x*z,y,z^3] W.toProjective.polynomial =
      z^3 * MvPolynomial.aeval ![z,x,y] (weightedCubic R W) := by
  simp [WeierstrassCurve.Projective.polynomial,weightedCubic]
  ring

lemma exists_plane_coordinate_data :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
      (b : Module.Basis (Fin 3) R (𝓐 3)),
      ι 1 z=originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x)=unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y)=unitPower R 3 ∧
      (fun i => ((b i : 𝓐 3) : A)) = ![(z:A)^3,(x:A)*z,(y:A)] ∧
      (∀ n (a : 𝓐 (3*n)), (a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A)) ∧
      MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] W.toProjective.polynomial=0 ∧
      RingHom.ker (MvPolynomial.aeval ![(z:A),(x:A),(y:A)]).toRingHom =
        Ideal.span {weightedCubic R W} := by
  obtain ⟨z,x,y,W,hz,hx,hy,hs,hrel⟩ := exists_surjective_polynomial_map_cubic R Q A 𝓐 ι hRing
  obtain ⟨b,hb⟩ := actual_degree_three_basis R Q A 𝓐 ι hRing z x y hz hx hy
  refine ⟨z,x,y,W,b,hz,hx,hy,hb,
    actual_third_veronese_generated R Q A 𝓐 ι hRing z x y hz hx hy,?_,
    actual_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hrel⟩
  rw [plane_polynomial_aeval R A W,hrel,mul_zero]


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration SectionFrames GeometricCubic
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)

lemma normalized_pullback_frame (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection Q.zero s) ⊤ := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m
  have hf := (unitPower_isFrame R m).map_iso η.symm
  have he : η.inv.app ⊤ (unitPower R m)=Scheme.Modules.pullbackLocalSection Q.zero s := by
    change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s)=unitPower R m at hs
    rw [← hs]
    change (η.hom ≫ η.inv).app ⊤ _ = _
    rw [η.hom_inv_id]
    rfl
  change Scheme.Modules.IsFrameOn (η.inv.app ⊤ (unitPower R m)) ⊤ at hf
  rw [he] at hf
  exact hf

lemma normalized_frame_open (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    ∃ V : Q.target.Opens, Set.range Q.zero ⊆ (V : Set Q.target) ∧
      Scheme.Modules.IsFrameOn s V := by
  let J := Scheme.Modules.zeroSchemeIdeal (sectionHom s)
  let V : Q.target.Opens := J.support.compl
  have hM := Q.zero_ideal_invertible.isInvertible_invModule.tensorPow m
  have hd : Disjoint (Set.range Q.zero) (J.support : Set Q.target) :=
    disjoint_range_zeroSchemeIdeal_of_pullback_frame Q.zero hM (sectionHom s) (by
      rw [sectionHom_app_one]
      exact normalized_pullback_frame R Q m s hs)
  refine ⟨V,?_,?_⟩
  · intro p hp
    exact fun h => Set.disjoint_left.mp hd hp h
  · have hf := hM.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal (sectionHom s) V
      (show Disjoint (V : Set Q.target) (J.support : Set Q.target) from (Set.disjoint_left.mpr (fun _ ha hb => ha hb)))
    change Scheme.Modules.IsFrameOn ((sectionHom s).app ⊤ (Scheme.Modules.unitSection ⊤)) V at hf
    rw [sectionHom_app_one] at hf
    exact hf

lemma origin_complement_frame :
    Scheme.Modules.IsFrameOn (originDegreeOne R Q) Q.zero.ker.support.compl := by
  exact (idealSectionRight_isFrameOn Q.zero.ker Q.zero_ideal_invertible (originPairing R Q)
    Q.zero.ker.support.compl (Set.disjoint_left.mpr (fun _ ha hb => ha hb))).tensorPowSection 1

variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)



include hRing
lemma planeZ_frame (z : 𝓐 1) (hz : ι 1 z=originDegreeOne R Q) :
    Scheme.Modules.IsFrameOn (ι 3 (planeZ R A 𝓐 z)) Q.zero.ker.support.compl := by
  have hf : Scheme.Modules.IsFrameOn (ι 1 z) Q.zero.ker.support.compl := by
    rw [hz]
    exact origin_complement_frame R Q
  let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
  have hff : Scheme.Modules.IsFrameOn (ι 2 zz) Q.zero.ker.support.compl := by
    rw [hRing.map_mul 1 1 z z]
    exact (hf.tensorSections hf).map_iso (Scheme.Modules.tensorPowAdd Q.zero.ker.invModule 1 1)
  rw [show planeZ R A 𝓐 z = ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩ from rfl,hRing.map_mul 2 1 zz z]
  exact (hff.tensorSections hf).map_iso (Scheme.Modules.tensorPowAdd Q.zero.ker.invModule 2 1)

lemma exists_plane_projPresentation (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z=originDegreeOne R Q)
    (hy : powerRestriction R Q 3 (ι 3 y)=unitPower R 3) :
    ∃ 𝔓 : Scheme.Modules.ProjPresentation (Q.zero.ker.invModule.tensorPow 3) Q.structureMap 2,
      𝔓.σ = ![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)] := by
  obtain ⟨V,hV,hframeV⟩ := normalized_frame_open R Q 3 (ι 3 y) hy
  let U := Q.zero.ker.support.compl
  have hframeU := planeZ_frame R Q A 𝓐 ι hRing z hz
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  have hsupport : (Q.zero.ker.support : Set Q.target)=Set.range Q.zero := by
    rw [Scheme.Hom.support_ker]
    exact Q.zero.isClosedEmbedding.isClosed_range.closure_eq
  have hUV : U ⊔ V=⊤ := by
    apply top_unique
    intro p _
    by_cases hp : p ∈ (Q.zero.ker.support : Set Q.target)
    · exact Or.inr (hV (hsupport ▸ hp))
    · exact Or.inl hp
  let σ : Fin 3 → Γ(Q.zero.ker.invModule.tensorPow 3,⊤) :=
    ![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)]
  let O : Fin 3 → Q.target.Opens := ![⊥,V,U]
  have hO : iSup O=⊤ := by
    apply top_unique
    rw [← hUV]
    exact sup_le (le_iSup O (2 : Fin 3)) (le_iSup O (1 : Fin 3))
  obtain ⟨𝔓,hσ,hpre⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top Q.structureMap
    (Q.zero.ker.invModule.tensorPow 3) 2 σ O hO (by
      intro i W hW
      fin_cases i
      · change W ≤ ⊥ at hW
        have he : W=⊥ := le_antisymm hW bot_le
        subst W
        letI := sections_empty_subsingleton (Q.zero.ker.invModule.tensorPow 3)
        exact ⟨fun a b _ => Subsingleton.elim a b,fun a => ⟨0,Subsingleton.elim _ _⟩⟩
      · exact hframeV.bijective le_top hW
      · exact hframeU.bijective le_top hW)
  exact ⟨𝔓,hσ⟩

omit hRing in
/-- A genuine plane morphism with the constructed Weierstrass coordinate relation,
starting only from the frozen geometric hypotheses. -/
theorem exists_origin_plane_map :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m,⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R)
        (𝔓 : Scheme.Modules.ProjPresentation (Q.zero.ker.invModule.tensorPow 3) Q.structureMap 2),
        j 1 z=originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x)=unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y)=unitPower R 3 ∧
        𝔓.σ = ![j 3 (planeX R B 𝓑 z x),j 3 y,j 3 (planeZ R B 𝓑 z)] ∧
        MvPolynomial.aeval ![(x:B)*z,(y:B),(z:B)^3] W.toProjective.polynomial=0 ∧
        RingHom.ker (MvPolynomial.aeval ![(z:B),(x:B),(y:B)]).toRingHom =
          Ideal.span {weightedCubic R W} := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  obtain ⟨z,x,y,W,b,hz,hx,hy,hb,hgen,hplane,hker⟩ := exists_plane_coordinate_data R Q B 𝓑 j hj
  obtain ⟨𝔓,hσ⟩ := exists_plane_projPresentation R Q B 𝓑 j hj z x y hz hy
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,z,x,y,W,𝔓,hz,hx,hy,hσ,hplane,hker⟩


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration CubicAlgebra Kernel
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_plane_cubic_kernel (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (hrel : MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] W.toProjective.polynomial=0) :
    RingHom.ker (MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3]).toRingHom =
      Ideal.span {W.toProjective.polynomial} := by
  nontriviality R
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  ext p
  rw [RingHom.mem_ker,Ideal.mem_span_singleton]
  apply PlaneKernel.planePolynomial_dvd_iff_eval_zero (x:A) (y:A) (z:A) W
    (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
    _ hrel
  intro i p a h
  exact PlaneKernel.polynomial_y_mul_x_mod_z 𝓐 lead (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing)) x y
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)
    z hzlead i p a h

lemma actual_plane_homogeneous_lift (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (n : ℕ) (a : 𝓐 (3*n)) :
    ∃ p : MvPolynomial (Fin 3) R, p.IsHomogeneous n ∧
      MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] p=(a:A) := by
  refine GradedEvaluation.exists_homogeneous_lift 𝓐 3 ![(x:A)*z,(y:A),(z:A)^3] ?_ (by decide) n a ?_
  · intro i
    fin_cases i
    · exact SetLike.mul_mem_graded x.2 z.2
    · exact y.2
    · exact SetLike.pow_mem_graded 3 z.2
  · have h := actual_third_veronese_generated R Q A 𝓐 ι hRing z x y hz hx hy n a
    have he : Set.range ![(x:A)*z,(y:A),(z:A)^3] = ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
      ext b
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · rintro (rfl|rfl|rfl)
        · exact ⟨2,rfl⟩
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [he]
    exact h


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.GeometricCubic

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration SectionFrames
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
lemma normalized_affine_cover (m : ℕ) (hm : 1 ≤ m)
    (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    ∃ U V : Q.target.Opens,
      IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V=⊤ ∧
      (∀ q : Q.target, q ∈ U ↔ q ∉ Set.range Q.zero) ∧
      (∀ q : Q.target, q ∈ V ↔ q ∉ (Scheme.Modules.zeroSchemeIdeal (sectionHom s)).support) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
  letI : GeometricallyIntegral Q.structureMap := Q.geometry.geometricallyIntegral_of_commRing
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible m
  let t : 𝟙_ Q.target.Modules ⟶ (Q.zero.ker^m).invModule := sectionHom s ≫ δ.inv
  have htzero : Scheme.Modules.zeroSchemeIdeal t = Scheme.Modules.zeroSchemeIdeal (sectionHom s) :=
    Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (sectionHom s) δ.inv
  have hd := disjoint_range_zeroSchemeIdeal_of_pullback_frame Q.zero
    (Scheme.Modules.IsInvertible.tensorPow Q.zero_ideal_invertible.isInvertible_invModule m)
    (sectionHom s) (by rw [sectionHom_app_one]; exact normalized_pullback_frame R Q m s hs)
  have ht : ∀ q ∈ Set.range Q.zero, q ∉ (Scheme.Modules.zeroSchemeIdeal t).support := by
    rw [htzero]
    exact fun q hq => fun hh => Set.disjoint_left.mp hd hq hh
  let ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) Q.structureMap := ⟨Q.zero,Q.zero_over⟩
  obtain ⟨U,V,hcov,hU,hV,f,g,hf,hg,hfg,_⟩ :=
    SmoothProperCurve.exists_twoChart_of_section_invModule_global R Q.structureMap ε m hm t ht
  have hεV : ∀ q ∈ Set.range ε.val.base, q ∈ V := by
    intro q hq
    exact (hV q).mpr (ht q hq)
  obtain ⟨htrU,htrV⟩ := SmoothProperCurve.transcendental_app_of_twoChart_of_section_mem_global
    R Q.structureMap ε U V hcov hU hεV f g hf hg hfg
  exact ⟨U,V,(Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart Q.structureMap U V f g hcov hg hfg htrU).1,
    (Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right Q.structureMap U V f g hcov hf hfg htrV).1,
    hcov,hU,by simpa only [htzero] using hV⟩


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration GeometricCubic
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma plane_restriction_at_identity (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z=originDegreeOne R Q)
    (hy : powerRestriction R Q 3 (ι 3 y)=unitPower R 3) :
    (fun i : Fin 3 => powerRestriction R Q 3
      (![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)] i)) =
      ![0,unitPower R 3,0] := by
  have hzlead : gradedLead R Q A 𝓐 ι hRing 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hxz : powerRestriction R Q 3 (ι 3 (planeX R A 𝓐 z x))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    change gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(x:A)*z,SetLike.mul_mem_graded x.2 z.2⟩=0
    rw [gradedLead_mul R Q A 𝓐 ι hRing 2 1 x z,hzlead,mul_zero]
  have hzzz : powerRestriction R Q 3 (ι 3 (planeZ R A 𝓐 z))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
    change gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩=0
    rw [gradedLead_mul R Q A 𝓐 ι hRing 2 1 zz z,hzlead,mul_zero]
  funext i
  fin_cases i
  · exact hxz
  · exact hy
  · exact hzzz


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration SectionFrames
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
open AlgebraicGeometry.Scheme.Modules
lemma origin_support_eq_range : (Q.zero.ker.support : Set Q.target)=Set.range Q.zero := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  rw [Scheme.Hom.support_ker]
  exact Q.zero.isClosedEmbedding.isClosed_range.closure_eq

lemma pullback_zero_of_powerRestriction_zero (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=0) : pullbackLocalSection Q.zero s=0 := by
  let e := pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫ tensorPowMapIso (identityLineFrame R Q) m
  have h := congrArg (e.inv.app ⊤) hs
  change e.inv.app ⊤ (e.hom.app ⊤ (pullbackLocalSection Q.zero s))=e.inv.app ⊤ 0 at h
  change (e.hom ≫ e.inv).app ⊤ (pullbackLocalSection Q.zero s)=e.inv.app ⊤ 0 at h
  rw [e.hom_inv_id,map_zero] at h
  exact h

lemma normalized_affine_loci (m : ℕ) (hm : 1 ≤ m) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    IsAffineOpen Q.zero.ker.support.compl ∧ IsAffineOpen (zeroSchemeIdeal (sectionHom s)).support.compl := by
  obtain ⟨U,V,hU,hV,_,heU,heV⟩ := normalized_affine_cover R Q m hm s hs
  have hUeq : U=Q.zero.ker.support.compl := by
    ext q
    change q ∈ U ↔ q ∉ (Q.zero.ker.support : Set Q.target)
    rw [origin_support_eq_range R Q]
    exact heU q
  have hVeq : V=(zeroSchemeIdeal (sectionHom s)).support.compl := by
    ext q
    exact heV q
  exact ⟨hUeq ▸ hU,hVeq ▸ hV⟩

variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m,⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma planeZ_frame_locus (z : 𝓐 1) (hz : ι 1 z=originDegreeOne R Q) :
    (zeroSchemeIdeal (sectionHom (ι 3 (planeZ R A 𝓐 z)))).support.compl=Q.zero.ker.support.compl := by
  have hzlead : GeometricCubic.gradedLead R Q A 𝓐 ι hRing 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hzzz : powerRestriction R Q 3 (ι 3 (planeZ R A 𝓐 z))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
    change GeometricCubic.gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩=0
    rw [GeometricCubic.gradedLead_mul R Q A 𝓐 ι hRing 2 1 zz z,hzlead,mul_zero]
  have hM := Q.zero_ideal_invertible.isInvertible_invModule.tensorPow 3
  have hsub := range_subset_support_of_pullback_zero Q.zero hM
    (sectionHom (ι 3 (planeZ R A 𝓐 z))) (by
      rw [sectionHom_app_one]
      exact pullback_zero_of_powerRestriction_zero R Q 3 _ hzzz)
  have hd := frame_disjoint_support hM (ι 3 (planeZ R A 𝓐 z)) Q.zero.ker.support.compl
    (planeZ_frame R Q A 𝓐 ι hRing z hz)
  ext q
  constructor
  · intro hq hqi
    apply hq
    exact hsub ((origin_support_eq_range R Q) ▸ hqi)
  · intro hq hqs
    exact Set.disjoint_left.mp hd hq hqs


end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Filtration GeometricCubic CubicCanonicalMap
variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
lemma exists_cubic_isomorphism :
    ∃ (W : WeierstrassCurve R) (e : Q.target ≅ WeierstrassProjModel.projModelCR W.toProjective),
      e.hom ≫ WeierstrassProjModel.projModelStrCR W.toProjective = Q.structureMap := by
  obtain ⟨A,hA,hRA,𝓐,h𝓐,ι,hRing⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hA
  letI := hRA
  letI := h𝓐
  obtain ⟨z,x,y,W,b,hz,hx,hy,hb,hgen,hplane,hker⟩ := exists_plane_coordinate_data R Q A 𝓐 ι hRing
  let a : Fin 3 → 𝓐 3 := ![planeX R A 𝓐 z x,y,planeZ R A 𝓐 z]
  have ha : (fun i => (a i:A)) = ![(x:A)*z,(y:A),(z:A)^3] := by
    funext i
    fin_cases i <;> simp [a,planeX,planeZ,pow_succ]
  have hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial} := by
    rw [ha]
    exact actual_plane_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hplane
  have hlift : ∀ n (b : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
      p.IsHomogeneous n ∧ MvPolynomial.aeval (fun i => (a i:A)) p=(b:A) := by
    rw [ha]
    exact actual_plane_homogeneous_lift R Q A 𝓐 ι hRing z x y hz hx hy
  obtain ⟨𝔓,hσ⟩ := exists_plane_projPresentation R Q A 𝓐 ι hRing z x y hz hy
  obtain ⟨θ,hθ⟩ := exists_canonical Q.structureMap Q.zero.ker.invModule 𝓐 ι hRing a W hk hlift 𝔓 (by
    intro i
    rw [hσ]
    fin_cases i <;> rfl)
  have haf := normalized_affine_loci R Q 3 (by decide) (ι 3 y) hy
  haveI : IsIso θ := isIso_of_affine_loci Q.structureMap Q.zero.ker.invModule 𝓐 ι hRing a W hk hlift θ hθ
    Q.zero_ideal_invertible.isInvertible_invModule haf.2 (by
      change IsAffineOpen (Scheme.Modules.zeroSchemeIdeal (SectionFrames.sectionHom (ι 3 (planeZ R A 𝓐 z)))).support.compl
      rw [planeZ_frame_locus R Q A 𝓐 ι hRing z hz]
      exact haf.1)
  exact ⟨W,asIso θ,canonical_over_base Q.structureMap Q.zero.ker.invModule 𝓐 ι a W hk θ hθ⟩

end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.ProjectiveMap

namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.PointedIso
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PointedIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of R)}

variable (R : Type u) [CommRing R]  [IsNoetherianRing R]
   [Algebra ℚ R] (Q : FramedCurve R)
lemma exists_pointed_cubic_isomorphism :
    ∃ (W : WeierstrassCurve R) (e : Q.target ≅ ArithmeticThetaRelativeKatoR0169.Curve R W),
      e.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W=Q.structureMap ∧
      Q.zero ≫ e.hom=ArithmeticThetaRelativeKatoR0169.origin R W := by
  obtain ⟨W,e,he⟩ := ProjectiveMap.exists_cubic_isomorphism R Q
  obtain ⟨e',he',hz⟩ := adjust_identity Q.law e he (WeierstrassProjModel.kwZeroSect R W).val
    (WeierstrassProjModel.kwZeroSect R W).property
  exact ⟨W,e',he',hz⟩

end ArithmeticThetaLocalWeierstrassR0203.NoetherianFramedPresentation.PointedIso

namespace ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
/-- Pointed Weierstrass presentation over every Noetherian rational ring. -/
theorem noetherian_framed_presentation
    (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (Q : FramedCurve R) :
    ∃ (W : WeierstrassCurve R) (hW : W.IsElliptic)
      (e : CategoryTheory.Iso Q.target (ArithmeticThetaRelativeKatoR0169.Curve R W)),
      e.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W = Q.structureMap ∧
      Q.zero ≫ e.hom = ArithmeticThetaRelativeKatoR0169.origin R W := by
  obtain ⟨W,e,he,hzero⟩ := NoetherianFramedPresentation.PointedIso.exists_pointed_cubic_isomorphism R Q
  haveI : Smooth Q.structureMap := Q.geometry.smooth
  have hstr : WeierstrassProjModel.projModelStrCR W.toProjective = e.inv ≫ Q.structureMap := by
    rw [← he, e.inv_hom_id_assoc]
    rfl
  haveI : Smooth (WeierstrassProjModel.projModelStrCR W.toProjective) := by
    rw [hstr]
    infer_instance
  haveI := SmoothHypersurface.smooth_coordinateRing W
  exact ⟨W, ⟨arbitrary_smooth_discriminant R W⟩, e, he, hzero⟩
#print axioms noetherian_framed_presentation
end ArithmeticThetaLocalWeierstrassR0203
