module

public import SchemeDiscriminantDefinitionsR0244

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeDiscriminantR0244
namespace FrameUniqueness
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171 hiding Base
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

lemma iso_frame_reflect {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {U : X.Opens} (s : Γ(M, U)) (hs : IsFrame N U (e.hom.app U s)) :
    IsFrame M U s := by
  have h := frame_iso e.symm _ hs
  simpa only [Iso.symm_hom, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply] using h

lemma frame_on_image {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (N : Y.Modules) (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (s : Γ(M, ⊤))
    (hs : IsFrame N ⊤ (res N (by simp) (e.hom.app _
      (Scheme.Modules.pullbackLocalSection f s)))) :
    IsFrame M f.opensRange (res M le_top s) := by
  have hn := frame_restrict N (V := f ⁻¹ᵁ ⊤) le_top _ hs
  rw [InitialHodgeSection.res_res, res_refl] at hn
  have hm := iso_frame_reflect e _ hn
  apply frame_of_pullback_open f M f.opensRange le_rfl
  rw [← InitialSectionNaturality.pullback_res]
  exact frame_restrict _ (show f ⁻¹ᵁ f.opensRange ≤ f ⁻¹ᵁ ⊤ from fun _ _ => trivial) _ hm

lemma comparison_frame {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} [IsOpenImmersion b] (C : Comparison E F b) (d : Sections E)
    (h : IsFrame (Power F) ⊤ (pull C d)) :
    IsFrame (Power E) b.opensRange (res (Power E) le_top d) :=
  frame_on_image b (Power E) (Power F) (powerIso C) d h

section Presentation
variable {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    {σ : S ⟶ Base k} {E : Family S} (P : LocalPresentation k S σ E)

local instance : CommRing P.ring := P.commRing
local instance : Algebra k P.ring := P.algebra
local instance : P.equation.IsElliptic := P.elliptic

/-- The accepted presentation gives exactly the pointed Cartesian test. -/
def comparison : Comparison E (weierstrassFamily P.ring P.equation P.law P.originLaw) P.base where
  map := P.comparison
  cartesian := P.cartesian
  pointed := by
    have hz : (weierstrassFamily P.ring P.equation P.law P.originLaw).zero =
        origin P.ring P.equation := by
      change (P.law.one (𝟙 (Base P.ring))).val = _
      simpa only [Category.id_comp] using P.originLaw.1 (𝟙 (Base P.ring))
    rw [hz]
    exact P.zero_eq

def testValue (d : Sections E) :=
  weierstrassValue P.ring P.equation P.law P.originLaw (pull (comparison P) d)

lemma test_frame (d : Sections E) (hd : IsD2 k σ E d) :
    IsFrame (HodgePower P.ring P.equation 24) ⊤ (testValue P d) := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  have h := hd P.ring P.equation P.law P.originLaw P.base P.base_eq (comparison P)
  obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model
    P.ring P.equation
  rw [show testValue P d = ArithmeticThetaArbitraryDiscriminantR0243.value M from h M]
  exact ArithmeticThetaArbitraryDiscriminantR0243.NormalDiscriminantIndependence.value_frame M

lemma test_eq (d e : Sections E) (hd : IsD2 k σ E d) (he : IsD2 k σ E e) :
    testValue P d = testValue P e := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model
    P.ring P.equation
  exact (hd P.ring P.equation P.law P.originLaw P.base P.base_eq (comparison P) M).trans
    (he P.ring P.equation P.law P.originLaw P.base P.base_eq (comparison P) M).symm

omit [CharZero k] in
lemma pull_eq (d e : Sections E) (h : testValue P d = testValue P e) :
    Scheme.Modules.pullbackLocalSection P.base d =
      Scheme.Modules.pullbackLocalSection P.base e := by
  apply (ConcreteCategory.bijective_of_isIso ((powerIso (comparison P)).hom.app _)).injective
  apply (res_bijective _ (show ⊤ ≤ P.base ⁻¹ᵁ ⊤ by simp) le_top).injective
  apply (ConcreteCategory.bijective_of_isIso
    ((powerCongr (Base P.ring) (weierstrassHodgeIso P.ring P.equation P.law P.originLaw) 24).hom.app ⊤)).injective
  exact h

set_option backward.isDefEq.respectTransparency true in
lemma image_frame (d : Sections E) (hd : IsD2 k σ E d) :
    letI := P.openImmersion
    IsFrame (Power E) P.base.opensRange (res (Power E) le_top d) := by
  letI := P.openImmersion
  have h : IsFrame (Power (weierstrassFamily P.ring P.equation P.law P.originLaw))
      ⊤ (pull (comparison P) d) :=
    iso_frame_reflect
      (powerCongr (Base P.ring) (weierstrassHodgeIso P.ring P.equation P.law P.originLaw) 24)
      (pull (comparison P) d) (test_frame P d hd)
  exact comparison_frame (comparison P) d h

end Presentation
end FrameUniqueness

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeDiscriminantR0171 hiding Base
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Universal affine normalization forces an all-open frame and uniquely detects
its global section, using the actual covering presentations of the family. -/
theorem scheme_discriminant_frame_uniqueness
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ Base k) (E : Family S) (d : Sections E) (hd : IsD2 k σ E d) :
    IsFrame (Power E) ⊤ d ∧ ∀ e : Sections E, IsD2 k σ E e → e = d := by
  classical
  let P := fun x : S => (scheme_local_weierstrass k S σ E x).choose
  have hP : ∀ x : S, x ∈ Set.range (P x).base :=
    fun x => (scheme_local_weierstrass k S σ E x).choose_spec
  let V : S → S.Opens := fun x => by
    letI := (P x).openImmersion
    exact (P x).base.opensRange
  have hc : (⨆ x, V x) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hP x⟩
  constructor
  · exact frame_glue_cover (Power E) V hc d (fun x => FrameUniqueness.image_frame (P x) d hd)
  · intro e he
    apply sections_eq_local (Power E) ⊤ e d
    intro x _
    letI := (P x).commRing
    letI := (P x).openImmersion
    refine ⟨V x, hP x, le_top, ?_⟩
    exact restriction_eq_of_pullback_eq (P x).base (Power E) ⊤ le_top e d
      (FrameUniqueness.pull_eq (P x) e d (FrameUniqueness.test_eq (P x) e d he hd))

#print axioms scheme_discriminant_frame_uniqueness
end ArithmeticThetaSchemeDiscriminantR0244
