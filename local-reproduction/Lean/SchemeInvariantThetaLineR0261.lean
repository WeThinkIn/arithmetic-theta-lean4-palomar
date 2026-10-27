import SchemeThetaPushforwardBaseChangeR0261
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne

/-! Local algebra and canonical section comparisons for the invariant theta line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaSchemeSchrodingerR0261
namespace SchemeInvariantThetaLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeSchrodingerR0257
open scoped TensorProduct

/-- Geometric rank one implies rank one over every field, via its algebraic closure. -/
theorem field_rank_one {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (h : FiniteProjectiveRank R M 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] M) = 1 := by
  let L := AlgebraicClosure K
  let e : L ⊗[K] (K ⊗[R] M) ≃ₗ[L] L ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M
  rw [← Module.finrank_baseChange (R := L) (S := K) (M' := K ⊗[R] M)]
  exact e.finrank_eq.trans (h.2.2 L).2

/-- The accepted module calculation produces an actual invertible tilde sheaf. -/
theorem fixed_tilde_invertible {R : CommRingCat.{u}} [Algebra ℚ R]
    (M : ModuleCat.{u} R) (m : ℕ) (hm : 0 < m) (hM : FiniteProjectiveRank R M m)
    (A B : Module.End R M) (c : Rˣ) (hA : A ^ m = 1) (hB : B ^ m = 1)
    (hAB : A * B = (c : R) • (B * A))
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    Scheme.Modules.IsInvertible (tilde (ModuleCat.of R (Fixed R M A))) := by
  have h := RelativeSchrodingerModule.fixed_rank_one m hm hM A B c hA hB hAB hc
  letI := h.1
  letI := h.2.1
  exact Scheme.Modules.isInvertible_tilde_of_projective_rankOne
    (ModuleCat.of R (Fixed R M A)) (field_rank_one h)

/-- Sections on an open, with their actual structure-sheaf scalar action. -/
def sectionsFunctor (S : Scheme.{u}) (U : S.Opens) :
    S.Modules ⥤ ModuleCat Γ(S, U) :=
  Scheme.Modules.toPresheafOfModules S ⋙
    PresheafOfModules.evaluation S.ringCatSheaf.obj (Opposite.op U)

instance (S : Scheme.{u}) (U : S.Opens) :
    PreservesFiniteLimits (sectionsFunctor S U) := by
  letI : PreservesFiniteLimits (Scheme.Modules.toPresheafOfModules S) :=
    (inferInstance : PreservesFiniteLimits (SheafOfModules.forget S.ringCatSheaf))
  letI := PresheafOfModules.evaluation_preservesFiniteLimits S.ringCatSheaf.obj (Opposite.op U)
  exact comp_preservesFiniteLimits _ _

instance (S : Scheme.{u}) (U : S.Opens) :
    (sectionsFunctor S U).Additive := by
  exact { map_add := rfl }

/-- Taking sections identifies the categorical kernel with the linear fixed submodule. -/
def fixedSectionsIso {S : Scheme.{u}} {W : S.Modules} (A : End W) (U : S.Opens) :
    (sectionsFunctor S U).obj (fixed A) ≅
      ModuleCat.of Γ(S, U) (Fixed Γ(S, U) Γ(W, U) (A.val.app (Opposite.op U)).hom) := by
  let F := sectionsFunctor S U
  refine PreservesKernel.iso F (A - 1) ≪≫ ModuleCat.kernelIsoKer (F.map (A - 1)) ≪≫ ?_
  exact (LinearEquiv.ofEq _ _ (by
    ext x
    rw [Module.End.mem_eigenspace_iff, one_smul]
    dsimp [F, sectionsFunctor, Scheme.Modules.toPresheafOfModules] at x ⊢
    change Γ(W, U) at x
    change (A.app U x : Γ(W, U)) - x = 0 ↔ A.app U x = x
    exact sub_eq_zero)).toModuleIso

/-- Evaluation of endomorphisms retains multiplication order and scalar action. -/
def sectionsEnd {S : Scheme.{u}} (W : S.Modules) (U : S.Opens) :
    End W →+* Module.End Γ(S, U) Γ(W, U) where
  toFun A := (A.val.app (Opposite.op U)).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The primitive scalar remains primitive after restriction to any open. -/
theorem primitive_restrict {S : Scheme.{u}} (m : ℕ) (c : Γ(S, ⊤)ˣ)
    (hc : ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c)
    (U : S.Opens) :
    ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m
      (Units.map (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.toMonoidHom c) := by
  let r := (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
  constructor
  · exact (map_pow (Units.map r.toMonoidHom) c m).symm.trans
      ((congrArg (Units.map r.toMonoidHom) hc.1).trans (map_one _))
  · intro i hi
    change IsUnit (r (c : Γ(S, ⊤)) ^ i.val - 1)
    simpa only [map_sub, map_pow, map_one] using (hc.2 i hi).map r

/-- The categorical Heisenberg relations give precisely the accepted linear ones. -/
theorem section_relations {S : Scheme.{u}} {W : S.Modules} (m : ℕ)
    (A B : End W) (c : Γ(S, ⊤)ˣ) (h : Relations m A B c) (U : S.Opens) :
    sectionsEnd W U A ^ m = 1 ∧ sectionsEnd W U B ^ m = 1 ∧
    sectionsEnd W U A * sectionsEnd W U B =
      (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (c : Γ(S, ⊤))) •
        (sectionsEnd W U B * sectionsEnd W U A) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg (sectionsEnd W U) h.1
  · simpa only [map_pow, map_one] using congrArg (sectionsEnd W U) h.2.1
  · have hh := congrArg (sectionsEnd W U) h.2.2
    simp only [map_mul] at hh
    rw [hh]
    rfl

/-- Rank one for the sections of the actual categorical kernel, whenever the
ambient sections satisfy the finite projective rank hypothesis. -/
theorem fixed_sections_rank {S : Scheme.{u}} {W : S.Modules} (m : ℕ) (hm : 0 < m)
    (A B : End W) (c : Γ(S, ⊤)ˣ) (h : Relations m A B c)
    (hc : ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c)
    (U : S.Opens) [Algebra ℚ Γ(S, U)]
    (hW : FiniteProjectiveRank Γ(S, U) Γ(W, U) m) :
    FiniteProjectiveRank Γ(S, U) Γ(fixed A, U) 1 := by
  obtain ⟨hA, hB, hAB⟩ := section_relations m A B c h U
  have hf := RelativeSchrodingerModule.fixed_rank_one m hm hW
    (sectionsEnd W U A) (sectionsEnd W U B)
    (Units.map (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.toMonoidHom c)
    hA hB hAB (primitive_restrict m c hc U)
  exact ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.finiteProjectiveRank_equiv
    (fixedSectionsIso A U).toLinearEquiv.symm 1 hf

open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
  (smulHom smulHom_app_apply)

/-- The averaging endomorphism is formed from actual sheaf maps. -/
def sheafAverage {S : Scheme.{u}} [Algebra ℚ Γ(S, ⊤)] {W : S.Modules}
    (m : ℕ) (A : End W) : End W :=
  (∑ j ∈ Finset.range m, A ^ j) ≫ smulHom (algebraMap ℚ Γ(S, ⊤) ((m : ℚ)⁻¹)) W

/-- Restriction of the sheaf average is the accepted module average. -/
theorem sheafAverage_app {S : Scheme.{u}} [Algebra ℚ Γ(S, ⊤)] {W : S.Modules}
    (m : ℕ) (A : End W) (U : S.Opens) :
    letI : Algebra ℚ Γ(S, U) :=
      ((S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
        (algebraMap ℚ Γ(S, ⊤))).toAlgebra
    sectionsEnd W U (sheafAverage m A) =
      RelativeSchrodingerModule.average m (sectionsEnd W U A) := by
  letI : Algebra ℚ Γ(S, U) :=
    ((S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      (algebraMap ℚ Γ(S, ⊤))).toAlgebra
  have hs := map_sum (sectionsEnd W U) (fun j => A ^ j) (Finset.range m)
  simp only [map_pow] at hs
  ext x
  change (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
      (algebraMap ℚ Γ(S, ⊤) ((m : ℚ)⁻¹)) •
      (sectionsEnd W U (∑ j ∈ Finset.range m, A ^ j)) x = _
  rw [hs]
  rfl

/-- The sheaf average lands in the actual categorical fixed kernel. -/
theorem sheafAverage_condition {S : Scheme.{u}} [Algebra ℚ Γ(S, ⊤)] {W : S.Modules}
    (m : ℕ) (A : End W) (hA : A ^ m = 1) : sheafAverage m A ≫ (A - 1) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  letI : Algebra ℚ Γ(S, U) :=
    ((S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      (algebraMap ℚ Γ(S, ⊤))).toAlgebra
  have ha : sectionsEnd W U A ^ m = 1 := by
    simpa only [map_pow, map_one] using congrArg (sectionsEnd W U) hA
  have hh := RelativeSchrodingerModule.average_fixed m (sectionsEnd W U A) ha x
  change (sectionsEnd W U A) ((sectionsEnd W U (sheafAverage m A)) x) -
    (sectionsEnd W U (sheafAverage m A)) x = 0
  rw [sheafAverage_app, hh, sub_self]

/-- Cyclic averaging splits the inclusion of the fixed subsheaf. -/
def fixedRetraction {S : Scheme.{u}} [Algebra ℚ Γ(S, ⊤)] {W : S.Modules}
    (m : ℕ) (hm : 0 < m) (A : End W) (hA : A ^ m = 1) : Retract (fixed A) W where
  i := fixedι A
  r := kernel.lift (A - 1) (sheafAverage m A) (sheafAverage_condition m A hA)
  retract := by
    apply (cancel_mono (fixedι A)).1
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    letI : Algebra ℚ Γ(S, U) :=
      ((S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
        (algebraMap ℚ Γ(S, ⊤))).toAlgebra
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f => Scheme.Modules.Hom.app f U) (kernel.condition (A - 1))) x
    have hx : (sectionsEnd W U A) ((fixedι A).app U x) = (fixedι A).app U x := by
      change (A.app U ((fixedι A).app U x) : Γ(W, U)) - (fixedι A).app U x = 0 at hh
      exact sub_eq_zero.mp hh
    change (sectionsEnd W U (sheafAverage m A)) ((fixedι A).app U x) = _
    rw [sheafAverage_app]
    exact RelativeSchrodingerModule.average_of_fixed m hm (sectionsEnd W U A) _ hx

/-- The affine counit is an isomorphism on a retract of an object on which it
is an isomorphism. This proves quasicoherence of the fixed sheaf, not merely rank. -/
theorem fromTilde_retract {R : CommRingCat.{u}} {K W : (Spec R).Modules}
    (e : Retract K W) (hW : IsIso (Scheme.Modules.fromTildeΓ W)) :
    IsIso (Scheme.Modules.fromTildeΓ K) := by
  let F := moduleSpecΓFunctor (R := R) ⋙ tilde.functor R
  let η : F ⟶ 𝟭 _ := Scheme.Modules.fromTildeΓNatTrans
  have he : RetractArrow (η.app K) (η.app W) :=
    { i := Arrow.homMk (F.map e.i) e.i (η.naturality e.i)
      r := Arrow.homMk (F.map e.r) e.r (η.naturality e.r)
      retract := by
        ext <;> simp [← Functor.map_comp, e.retract] }
  exact (MorphismProperty.isomorphisms _).of_retract he hW

/-- An affine finite-order fixed sheaf is quasicoherent whenever the ambient
sheaf is, by its explicit averaging retraction. -/
theorem fixed_fromTilde {R : CommRingCat.{u}} [Algebra ℚ Γ(Spec R, ⊤)]
    {W : (Spec R).Modules} (m : ℕ) (hm : 0 < m) (A : End W) (hA : A ^ m = 1)
    (hW : W.IsQuasicoherent) : IsIso (Scheme.Modules.fromTildeΓ (fixed A)) :=
  fromTilde_retract (fixedRetraction m hm A hA)
    ((isQuasicoherent_iff_isIso_fromTildeΓ W).mp hW)

/-- The same canonical kernel comparison for any additive left-exact module-valued functor. -/
def functorFixedIso {S : Scheme.{u}} {R : Type u} [CommRing R]
    (F : S.Modules ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteLimits F]
    {W : S.Modules} (A : End W) :
    F.obj (fixed A) ≅ ModuleCat.of R (Fixed R (F.obj W) (F.map A).hom) := by
  refine PreservesKernel.iso F (A - 1) ≪≫ ModuleCat.kernelIsoKer (F.map (A - 1)) ≪≫ ?_
  exact (LinearEquiv.ofEq _ _ (by
    ext x
    rw [Module.End.mem_eigenspace_iff, one_smul]
    change (F.map ((show W ⟶ W from A) - 𝟙 W)).hom x = 0 ↔ _
    rw [F.map_sub, F.map_id]
    change (F.map A).hom x - x = 0 ↔ (F.map A).hom x = x
    exact sub_eq_zero)).toModuleIso

/-- Isomorphisms preserve the concrete local-trivialization predicate. -/
theorem invertible_of_iso {S : Scheme.{u}} {K W : S.Modules} (e : K ≅ W)
    (h : Scheme.Modules.IsInvertible K) : Scheme.Modules.IsInvertible W := by
  constructor
  intro x
  obtain ⟨U, hx, ⟨i⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ i⟩⟩

/-- The affine global-section functor is left exact as the right adjoint of tilde. -/
instance specSections_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) := by
  letI := (tilde.adjunction (R := R)).isRightAdjoint
  infer_instance

instance specSections_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive := { map_add := rfl }

def functorEnd {S : Scheme.{u}} {R : Type u} [CommRing R]
    (F : S.Modules ⥤ ModuleCat.{u} R) [F.Additive] (W : S.Modules) :
    End W →+* Module.End R (F.obj W) where
  toFun A := (F.map A).hom
  map_zero' := by rw [F.map_zero]; rfl
  map_one' := by change (F.map (𝟙 W)).hom = _; rw [F.map_id]; rfl
  map_add' A B := by rw [F.map_add]; rfl
  map_mul' A B := by change (F.map (B ≫ A)).hom = _; rw [F.map_comp]; rfl

/-- The top-section scalar is transported by the canonical Spec global-section isomorphism. -/
theorem spec_unitAction {R : CommRingCat.{u}} (W : (Spec R).Modules)
    (c : Γ(Spec R, ⊤)ˣ) :
    functorEnd (moduleSpecΓFunctor (R := R)) W (unitAction W c) =
      (Scheme.ΓSpecIso R).hom.hom (c : Γ(Spec R, ⊤)) • 1 := by
  ext x
  change ((Spec R).presheaf.map (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op
      (c : Γ(Spec R, ⊤))) • (show Γ(W, ⊤) from x) =
    ((Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom (c : Γ(Spec R, ⊤)))) •
      (show Γ(W, ⊤) from x)
  simp

/-- Affine invertibility of the actual fixed kernel, using its counit and its
canonical section comparison. -/
theorem affine_fixed_invertible {R : CommRingCat.{u}} [Algebra ℚ R]
    (W : (Spec R).Modules) (m : ℕ) (hm : 0 < m)
    (hW : W.IsQuasicoherent)
    (hM : FiniteProjectiveRank R ((moduleSpecΓFunctor (R := R)).obj W) m)
    (A B : End W) (c : Γ(Spec R, ⊤)ˣ) (h : Relations m A B c)
    (hc : ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := Spec R) m c) :
    Scheme.Modules.IsInvertible (fixed A) := by
  let F := moduleSpecΓFunctor (R := R)
  let γ := functorEnd F W
  let cR := Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom c
  have hA : γ A ^ m = 1 := by simpa only [map_pow, map_one] using congrArg γ h.1
  have hB : γ B ^ m = 1 := by simpa only [map_pow, map_one] using congrArg γ h.2.1
  have hAB : γ A * γ B = (cR : R) • (γ B * γ A) := by
    have hh := congrArg γ h.2.2
    simp only [map_mul] at hh
    rw [hh]
    change functorEnd F W (unitAction W c) * _ = _
    rw [spec_unitAction, smul_mul_assoc, one_mul]
    rfl
  have hcR : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m cR := by
    constructor
    · exact (map_pow (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom) c m).symm.trans
        ((congrArg (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom) hc.1).trans (map_one _))
    · intro i hi
      change IsUnit ((Scheme.ΓSpecIso R).hom.hom (c : Γ(Spec R, ⊤)) ^ i.val - 1)
      simpa only [map_sub, map_pow, map_one] using (hc.2 i hi).map (Scheme.ΓSpecIso R).hom.hom
  have ht := fixed_tilde_invertible (F.obj W) m hm hM (γ A) (γ B) cR hA hB hAB hcR
  letI : Algebra ℚ Γ(Spec R, ⊤) :=
    ((Scheme.ΓSpecIso R).inv.hom.comp (algebraMap ℚ R)).toAlgebra
  letI := fixed_fromTilde m hm A h.1 hW
  let e : tilde (ModuleCat.of R (Fixed R (F.obj W) (γ A))) ≅ fixed A :=
    (tilde.functor R).mapIso (functorFixedIso F A).symm ≪≫
      asIso (Scheme.Modules.fromTildeΓ (fixed A))
  exact invertible_of_iso e ht

/-- Open restriction preserves the categorical kernel. -/
theorem pullback_open_leftExact {S T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b] :
    PreservesFiniteLimits (Scheme.Modules.pullback b) := by
  letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor b) := by
    let G := Scheme.Modules.toPresheaf T
    let H := (Functor.whiskeringLeft T.Opensᵒᵖ S.Opensᵒᵖ AddCommGrpCat.{u}).obj b.opensFunctor.op
    letI : PreservesFiniteLimits H := { preservesFiniteLimits := fun J _ _ =>
      whiskeringLeft_preservesLimitsOfShape J b.opensFunctor.op }
    letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor b ⋙ G) := by
      change PreservesFiniteLimits (Scheme.Modules.toPresheaf S ⋙ H)
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves (Scheme.Modules.restrictFunctor b) G
  exact preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback b)

/-- Canonical identification of the fixed kernel after an open restriction. -/
def fixedOpenIso {S T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b]
    {W : S.Modules} (A : End W) :
    (Scheme.Modules.pullback b).obj (fixed A) ≅ fixed ((Scheme.Modules.pullback b).map A) := by
  let F := Scheme.Modules.pullback b
  letI := pullback_open_leftExact b
  refine PreservesKernel.iso F (A - 1) ≪≫ eqToIso ?_
  congr 1
  change F.map ((show W ⟶ W from A) - 𝟙 W) = _
  rw [F.map_sub, F.map_id]
  rfl

/-- Pullback retains the precise Heisenberg scalar. -/
theorem relations_pullback {S T : Scheme.{u}} (b : T ⟶ S)
    {W : S.Modules} (m : ℕ) (A B : End W) (c : Γ(S, ⊤)ˣ) (h : Relations m A B c) :
    Relations m ((Scheme.Modules.pullback b).map A) ((Scheme.Modules.pullback b).map B)
      (Units.map b.appTop.hom.toMonoidHom c) := by
  let F := Scheme.Modules.pullback b
  refine ⟨?_, ?_, ?_⟩
  · exact (map_pow (F.mapEnd W) A m).symm.trans ((congrArg (F.mapEnd W) h.1).trans (map_one _))
  · exact (map_pow (F.mapEnd W) B m).symm.trans ((congrArg (F.mapEnd W) h.2.1).trans (map_one _))
  · have hh := congrArg (F.mapEnd W) h.2.2
    simp only [map_mul] at hh
    change (F.mapEnd W) A * (F.mapEnd W) B = _
    rw [hh]
    congr 1
    exact congrArg Iso.hom
      (P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.pullback_mapIso_smulIso b c W)

/-- Primitivity is preserved by the actual map on base sections. -/
theorem primitive_pullback {S T : Scheme.{u}} (b : T ⟶ S) (m : ℕ) (c : Γ(S, ⊤)ˣ)
    (hc : ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c) :
    ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := T) m
      (Units.map b.appTop.hom.toMonoidHom c) := by
  constructor
  · exact (map_pow (Units.map b.appTop.hom.toMonoidHom) c m).symm.trans
      ((congrArg (Units.map b.appTop.hom.toMonoidHom) hc.1).trans (map_one _))
  · intro i hi
    change IsUnit (b.appTop.hom (c : Γ(S, ⊤)) ^ i.val - 1)
    simpa only [map_sub, map_pow, map_one] using (hc.2 i hi).map b.appTop.hom

open ArithmeticThetaLocalWeierstrassR0203
open P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom.AlgebraicGeometry.Scheme.Modules
  (globalSectionsEquiv)

/-- Every affine open test of the actual fixed sheaf is invertible. -/
theorem affine_open_fixed (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m)
    (A B : End (V E m)) (c : Γ(S, ⊤)ˣ) (h : Relations m A B c)
    (hc : ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c)
    (R : Type u) [CommRing R] (b : Base R ⟶ S) [IsOpenImmersion b] :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback b).obj (fixed A)) := by
  letI : Algebra k R := (Spec.preimage (b ≫ σ)).hom.toAlgebra
  letI : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ k)
  let W := (Scheme.Modules.pullback b).obj (V E m)
  let F := moduleSpecΓFunctor (R := .of R)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Base R)) W ⊤
  let e₀ : (Scheme.Modules.pushforward (𝟙 (Base R))).obj W ≅ W :=
    (Scheme.Modules.pushforwardId (Base R)).app W
  let ε : F.obj W ≃ₗ[R] Γ(W, ⊤) :=
    ((F.mapIso e₀).toLinearEquiv.symm).trans (globalSectionsEquiv (𝟙 (Base R)) W)
  have hM : FiniteProjectiveRank R (F.obj W) m :=
    ArithmeticThetaSchemeThetaMarkingR0259.SchemeThetaSectionCohomology.finiteProjectiveRank_equiv
      ε.symm m (SchemeThetaPushforwardBaseChange.bundleRank k σ E m hm R b)
  have hi := affine_fixed_invertible W m hm
    (SchemeThetaPushforwardBaseChange.affine_pullback_quasicoherent k σ E m hm R b) hM
    ((Scheme.Modules.pullback b).map A) ((Scheme.Modules.pullback b).map B)
    (Units.map b.appTop.hom.toMonoidHom c) (relations_pullback b m A B c h)
    (primitive_pullback b m c hc)
  exact invertible_of_iso (fixedOpenIso b A).symm hi

/-- A trivialization after an open immersion gives a trivialization on its
actual image neighborhood. -/
theorem trivialization_at_image {S T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b]
    (W : S.Modules) (h : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback b).obj W))
    (t : T) : ∃ U : S.Opens, b t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj W ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨V, ht, ⟨e⟩⟩ := h.exists_trivialization t
  let f : V.toScheme ⟶ S := V.ι ≫ b
  let U := f.opensRange
  have hr : Set.range f = Set.range U.ι := by
    exact (Subtype.range_coe_subtype).symm
  let j := IsOpenImmersion.isoOfRangeEq f U.ι hr
  have hj : j.inv ≫ f = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hr
  have he : (Scheme.Modules.pullback f).obj W ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.pullbackComp V.ι b).app W).symm ≪≫ e
  refine ⟨U, ⟨⟨t, ht⟩, rfl⟩, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackCongr hj).app W).symm ≪≫
    ((Scheme.Modules.pullbackComp j.inv f).app W).symm ≪≫
    (Scheme.Modules.pullback j.inv).mapIso he ≪≫ Scheme.Modules.pullbackUnitIso j.inv

end SchemeInvariantThetaLine

open CategoryTheory AlgebraicGeometry
/-- The invariant common line is the actual categorical kernel of A - id. -/
theorem scheme_invariant_theta_line :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ∀ E : ArithmeticThetaLocalWeierstrassR0203.Family S, ∀ (m : ℕ), 0 < m →
      ∀ (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V E m))
        (c : (S.presheaf.obj (Opposite.op ⊤))ˣ),
      ArithmeticThetaSchemeSchrodingerR0261.Relations m A B c →
      ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c →
      AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSchemeSchrodingerR0261.fixed A) := by
  intro k _ _ S σ E m hm A B c h hc
  constructor
  intro x
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show x ∈ (⊤ : S.Opens) from trivial)
  let t := hU.isoSpec.hom ⟨x, hx⟩
  have ht : hU.fromSpec t = x := by
    change (hU.isoSpec.inv ≫ Scheme.Opens.ι U) (hU.isoSpec.hom ⟨x, hx⟩) = x
    simp [← Scheme.Hom.comp_apply]
  have hi := SchemeInvariantThetaLine.affine_open_fixed k σ E m hm A B c h hc Γ(S, U) hU.fromSpec
  simpa only [ht] using SchemeInvariantThetaLine.trivialization_at_image hU.fromSpec (fixed A) hi t

end ArithmeticThetaSchemeSchrodingerR0261

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.fixed_tilde_invertible
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.fixedSectionsIso

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.fixed_sections_rank

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.fixedRetraction

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.fixed_fromTilde

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeInvariantThetaLine.affine_fixed_invertible

#print axioms ArithmeticThetaSchemeSchrodingerR0261.scheme_invariant_theta_line
