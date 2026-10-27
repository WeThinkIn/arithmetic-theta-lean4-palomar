import RelativeIdentityTorsionNeighborhoodR0171
import RelativeConormalHodgeGeneratorR0171
import TensorPowerLaws

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRelativeDiscriminantR0171
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaLineRoot
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential

namespace InitialHodgeSection

lemma res_res {X : Scheme.{u}} (F : X.Modules) {U V T : X.Opens}
    (h : V ≤ U) (k : T ≤ V) (s : Γ(F,U)) :
    res F k (res F h s) = res F (k.trans h) s := by
  exact (F.presheaf.map_comp_apply (homOfLE h).op (homOfLE k).op s).symm

lemma res_self {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (s : Γ(F,U)) :
    res F le_rfl s = s := F.presheaf.map_id_apply _ s

lemma res_smul {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (a : Γ(X,U)) (s : Γ(F,U)) :
    res F h (a • s) = X.presheaf.map (homOfLE h).op a • res F h s :=
  Scheme.Modules.map_smul _ _ _ _

/-- A frame in the frozen predicate supplies a natural local trivialization. -/
def frame {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (s : Γ(F,U))
    (hs : IsFrame F U s) : LocalFrame X F U where
  equiv V h := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Γ(X,V) Γ(F,V) (res F h s)) (hs V h)
  naturality V T k h a := by
    change res F k (a • res F h s) = _
    rw [res_smul, res_res]
    rfl

lemma tensor_smul (X : Scheme.{u}) (F : X.Modules) (n : ℕ) (U : X.Opens)
    (a : Γ(X,U)) (s : Γ(F,U)) :
    tensorPowerSection X F n U (a • s) = a^n • tensorPowerSection X F n U s := by
  induction n with
  | zero => simp [tensorPowerSection]
  | succ n ih =>
    simp only [tensorPowerSection, ih, tensorSection, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, map_smul, smul_smul, pow_succ, mul_comm]

lemma tensor_frame {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (s : Γ(F,U))
    (hs : IsFrame F U s) (n : ℕ) :
    IsFrame (tensorPower X F n) U (tensorPowerSection X F n U s) := by
  intro V h
  let e := frame F s hs
  have he : e.equiv V h 1 = res F h s := one_smul _ _
  have ht := tensorPowerSection_frame X F U e n V h 1
  rw [one_pow, he] at ht
  have hmap : res (tensorPower X F n) h (tensorPowerSection X F n U s) =
      (tensorPowerFrame X F U e n).equiv V h 1 :=
    (tensorPowerSection_restrict X F n U V h s).trans ht
  rw [hmap]
  simpa only [← map_smul, smul_eq_mul, mul_one] using
    (tensorPowerFrame X F U e n).equiv V h |>.bijective

lemma unit_frame {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (s : Γ(F,U))
    (hs : IsFrame F U s) (e : Γ(X,U)ˣ) : IsFrame F U ((e : Γ(X,U)) • s) := by
  intro V h
  rw [res_smul]
  let v := e.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
  have hv : Function.Bijective (fun a : Γ(X,V) => a * (v : Γ(X,V))) :=
    v.mulRight_bijective
  have hh := (hs V h).comp hv
  change Function.Bijective (fun x : Γ(X,V) =>
    (x * (X.presheaf.map (homOfLE h).op (e : Γ(X,U)))) • res F h s) at hh
  simpa only [mul_smul] using hh

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)

lemma differential_res {U V : (Curve R W).Opens} (h : V ≤ U) (a : Γ(Curve R W,U)) :
    res (Hodge R W) (show origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ U from fun _ hx => h hx)
      (localDifferential R W U a) =
    localDifferential R W V ((Curve R W).presheaf.map (homOfLE h).op a) := by
  unfold res localDifferential
  rw [Scheme.Modules.map_homOfLE_pullbackLocalSection (origin R W) h, relativeD_restrict]

lemma power_res (n : ℕ) {U V : (Curve R W).Opens} (h : V ≤ U) (a : Γ(Curve R W,U)) :
    res (HodgePower R W n) (show origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ U from fun _ hx => h hx)
      (localPower R W n U a) =
    localPower R W n V ((Curve R W).presheaf.map (homOfLE h).op a) := by
  unfold localPower
  rw [show res (HodgePower R W n) _ _ = _ from
    tensorPowerSection_restrict (Base R) (Hodge R W) n _ _ _ _]
  rw [← differential_res R W h a]
  rfl

lemma differential_mul (U : (Curve R W).Opens) (r a : Γ(Curve R W,U))
    (ha : (origin R W).app U a = 0) :
    localDifferential R W U (r*a) =
      (origin R W).app U r • localDifferential R W U a := by
  simp only [localDifferential, relativeD_mul, Scheme.Modules.pullbackLocalSection_add,
    Scheme.Modules.pullbackLocalSection_smul, ha, zero_smul, add_zero]

lemma power_mul (n : ℕ) (U : (Curve R W).Opens) (r a : Γ(Curve R W,U))
    (ha : (origin R W).app U a = 0) :
    localPower R W n U (r*a) =
      ((origin R W).app U r)^n • localPower R W n U a := by
  unfold localPower
  rw [differential_mul R W U r a ha, tensor_smul]


variable [IsDomain R] [IsIntegral (Curve R W)]

lemma generator_vanishes (U : (Curve R W).affineOpens) (a : Γ(Curve R W,U.1))
    (ha : (identityIdeal R W).ideal U = Ideal.span {a}) : (origin R W).app U.1 a = 0 := by
  change ((origin R W).app U.1).hom a = 0
  apply RingHom.mem_ker.mp
  rw [← Scheme.Hom.ker_apply]
  change a ∈ (identityIdeal R W).ideal U
  rw [ha]
  exact Ideal.subset_span (Set.mem_singleton a)

lemma chart_restrict (G : Law R W) (c : ℕ) (U V : (Curve R W).affineOpens)
    [Nonempty U.1] [Nonempty V.1] (h : V.1 ≤ U.1) (a : Γ(Curve R W,U.1))
    (ha : IdentityChart R W G c U a) :
    IdentityChart R W G c V ((Curve R W).presheaf.map (homOfLE h).op a) := by
  refine ⟨?_, ?_, ?_⟩
  · apply isRegular_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (map_injective_of_isIntegral (Curve R W) (homOfLE h))).mpr
      (nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha.1))
  · rw [← (identityIdeal R W).map_ideal h, ha.2.1, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← (torsionIdeal R W G c).map_ideal h, ← (identityIdeal R W).map_ideal h, ha.2.2]

/-- Cancellation in the actual function field gives the transformation law
for the leading coefficient; the generator vanishes under the origin map. -/
lemma value_eq (G : Law R W) (c n : ℕ) (g : (Curve R W).functionField)
    (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a b : Γ(Curve R W,U.1)) (ha : IdentityChart R W G c U a)
    (hb : IdentityChart R W G c U b) (e f : Γ(Curve R W,U.1))
    (he : (Curve R W).germToFunctionField U.1 (e*a^n) = g)
    (hf : (Curve R W).germToFunctionField U.1 (f*b^n) = g) :
    (origin R W).app U.1 e • localPower R W n U.1 a =
    (origin R W).app U.1 f • localPower R W n U.1 b := by
  have hba : b ∈ Ideal.span {a} := by
    rw [← ha.2.1, hb.2.1]
    exact Ideal.subset_span (Set.mem_singleton b)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hba
  have hb' : b = r*a := by rw [hr, mul_comm]
  have hcoeff : e = f*r^n := by
    apply mul_right_cancel₀ (pow_ne_zero n
      (nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha.1)))
    have hh := (Curve R W).germToFunctionField_injective U.1 (he.trans hf.symm)
    rw [hb', mul_pow, ← mul_assoc] at hh
    exact hh
  rw [hb', power_mul R W n U.1 r a (generator_vanishes R W U a ha.2.1),
    smul_smul, hcoeff, map_mul, map_pow]

/-- Restriction of an evaluated local initial tensor. -/
lemma value_res (n : ℕ) {U V : (Curve R W).Opens} (h : V ≤ U)
    (e a : Γ(Curve R W,U)) :
    res (HodgePower R W n) (show origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ U from fun _ hx => h hx)
      ((origin R W).app U e • localPower R W n U a) =
    (origin R W).app V ((Curve R W).presheaf.map (homOfLE h).op e) •
      localPower R W n V ((Curve R W).presheaf.map (homOfLE h).op a) := by
  rw [res_smul, power_res R W n h]
  congr 1
  exact ConcreteCategory.congr_hom ((origin R W).naturality (homOfLE h).op).symm e

lemma overlap (G : Law R W) (c n : ℕ) (g : (Curve R W).functionField)
    [IsSeparated (structureMap R W)]
    (U V : (Curve R W).affineOpens) [Nonempty U.1] [Nonempty V.1]
    (a : Γ(Curve R W,U.1)) (b : Γ(Curve R W,V.1))
    (ha : IdentityChart R W G c U a) (hb : IdentityChart R W G c V b)
    (e : Γ(Curve R W,U.1)) (f : Γ(Curve R W,V.1))
    (he : (Curve R W).germToFunctionField U.1 (e*a^n) = g)
    (hf : (Curve R W).germToFunctionField V.1 (f*b^n) = g) :
    res (HodgePower R W n) inf_le_left
      ((origin R W).app U.1 e • localPower R W n U.1 a) =
    res (HodgePower R W n) inf_le_right
      ((origin R W).app V.1 f • localPower R W n V.1 b) := by
  letI : (Curve R W).IsSeparated := ⟨by
    haveI : IsSeparated (structureMap R W ≫ Limits.terminal.from (Base R)) := inferInstance
    simpa only [Limits.terminal.comp_from] using this⟩
  let T : (Curve R W).affineOpens := ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
  letI : Nonempty T.1 := overlap_nonempty (Curve R W) U.1 V.1
  have hU : T.1 ≤ U.1 := inf_le_left
  have hV : T.1 ≤ V.1 := inf_le_right
  change res (HodgePower R W n) (show origin R W ⁻¹ᵁ T.1 ≤ origin R W ⁻¹ᵁ U.1 from fun _ hx => hx.1) _ =
    res (HodgePower R W n) (show origin R W ⁻¹ᵁ T.1 ≤ origin R W ⁻¹ᵁ V.1 from fun _ hx => hx.2) _
  rw [value_res R W n hU, value_res R W n hV]
  apply value_eq R W G c n g T _ _
    (chart_restrict R W G c U T hU a ha) (chart_restrict R W G c V T hV b hb)
  · rw [← map_pow, ← map_mul, germ_restrict]
    exact he
  · rw [← map_pow, ← map_mul, germ_restrict]
    exact hf


lemma frame_glue {X : Scheme.{u}} (F : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (hcover : (⨆ i, V i) = ⊤) (s : Γ(F,⊤))
    (h : ∀ i, IsFrame F (V i) (res F le_top s)) : IsFrame F ⊤ s := by
  have hs : ∀ i, Scheme.Modules.IsFrameOn s (V i) := by
    intro i T hT hTi
    have hh := h i T hTi
    change Function.Bijective (fun a : Γ(X,T) => a • res F hT s)
    simpa only [res_res] using hh
  have ht := Scheme.Modules.IsFrameOn.of_iSup V hs
  rw [hcover] at ht
  exact fun T hT => ht hT hT

end InitialHodgeSection

/-- The intrinsic initial Hodge tensor is obtained by gluing the actual
unit quotients times the differential powers on every identity chart. -/
theorem relative_initial_hodge_section :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g), ∃! d : (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W (c^2-1)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaRelativeDiscriminantR0171.RepresentsInitial R W G c g d ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W (c^2-1)) ⊤ d := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG c hc hc6 g hg
  classical
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  let I := Σ U : (Curve R W).affineOpens,
    {a : Γ(Curve R W,U.1) // Nonempty U.1 ∧ IdentityChart R W G c U a}
  letI (i : I) : Nonempty i.1.1 := i.2.property.1
  let V : I → (Base R).Opens := fun i => origin R W ⁻¹ᵁ i.1.1
  have hcovers : (⨆ i, V i) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U,a,hx,ha⟩ := relative_identity_torsion_neighborhood R W G hG c (by omega) x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨U, a, ⟨⟨origin R W x,hx⟩⟩, ha⟩, hx⟩
  have hu (i : I) : ∃! e : Γ(Curve R W,i.1.1)ˣ,
      (c : (Curve R W).functionField)*g =
        (Curve R W).germToFunctionField i.1.1 ((e : _) * i.2.val^(c^2-1)) := by
    letI := i.2.property.1
    exact relative_initial_unit R W G hG c hc hc6 g hg i.1 i.2.val i.2.property.2
  let e (i : I) := (hu i).exists.choose
  have he (i : I) : (c : (Curve R W).functionField)*g =
      (Curve R W).germToFunctionField i.1.1 ((e i : _) * i.2.val^(c^2-1)) :=
    (hu i).exists.choose_spec
  let s (i : I) : Γ(HodgePower R W (c^2-1),V i) :=
    (origin R W).app i.1.1 (e i : _) • localPower R W (c^2-1) i.1.1 i.2.val
  have hcomp : TopCat.Presheaf.IsCompatible (HodgePower R W (c^2-1)).presheaf V s := by
    intro i j
    letI := i.2.property.1
    letI := j.2.property.1
    exact InitialHodgeSection.overlap R W G c (c^2-1) ((c : (Curve R W).functionField)*g)
      i.1 j.1 i.2.val j.2.val i.2.property.2 j.2.property.2 (e i) (e j)
      (he i).symm (he j).symm
  obtain ⟨d,hd,hunique⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(HodgePower R W (c^2-1)).presheaf, (HodgePower R W (c^2-1)).isSheaf⟩
    V ⊤ (fun _ => homOfLE le_top) hcovers.ge s hcomp
  have hrepr : RepresentsInitial R W G c g d := by
    intro U hU a ha
    let i : I := ⟨U,a,hU,ha⟩
    exact ⟨e i, he i, hd i⟩
  have hframe : IsFrame (HodgePower R W (c^2-1)) ⊤ d := by
    apply InitialHodgeSection.frame_glue _ V hcovers d
    intro i
    change IsFrame _ (V i) ((HodgePower R W (c^2-1)).presheaf.map (homOfLE le_top).op d)
    rw [hd i]
    letI := i.2.property.1
    have hda := relative_conormal_hodge_generator R W G hG i.1 i.2.val
      i.2.property.2.1 i.2.property.2.2.1
    have hp := InitialHodgeSection.tensor_frame (Hodge R W) _ hda (c^2-1)
    exact InitialHodgeSection.unit_frame _ _ hp
      ((e i).map ((origin R W).app i.1.1).hom.toMonoidHom)
  refine ⟨d, ⟨hrepr,hframe⟩, ?_⟩
  intro d' hd'
  apply hunique
  intro i
  letI := i.2.property.1
  obtain ⟨e',he',hd'e⟩ := hd'.1 i.1 i.2.val i.2.property.2
  have heq : e' = e i := (hu i).unique he' (he i)
  exact hd'e.trans (by rw [heq])

#print axioms relative_initial_hodge_section
end ArithmeticThetaRelativeDiscriminantR0171
