module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section elab "matcher2087" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
section Package00
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
theorem instAlgebraSubtypeMemValuationSubring_definitions._proof_3.{u_1, u_2} : ∀ {K : Type u_2} {L : Type u_1} [inst : Field.{u_2} K] [inst_1 : Semiring.{u_1} L] (O : @ValuationSubring.{u_2} K inst) [inst_2 : @Algebra.{u_2, u_1} K L (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) inst_1] (x : ↥O) (x_1 : L), @Eq.{u_1 + 1} L (@HSMul.hSMul.{u_2, u_1, u_1} (↥O) L L (@instHSMul.{u_2, u_1} (↥O) L (@SMul.mk.{u_2, u_1} (↥O) L fun r x => @HSMul.hSMul.{u_2, u_1, u_1} K L L (@instHSMul.{u_2, u_1} K L (@Algebra.toSMul.{u_2, u_1} K L (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) inst_1 inst_2)) (@Subtype.val.{u_2 + 1} K (fun x => @Membership.mem.{u_2, u_2} K (@ValuationSubring.{u_2} K inst) (@SetLike.instMembership.{u_2, u_2} (@ValuationSubring.{u_2} K inst) K (@ValuationSubring.instSetLike.{u_2} K inst)) O x) r) x)) x x_1) (@HMul.hMul.{u_1, u_1, u_1} L L L (@instHMul.{u_1} L (@Distrib.toMul.{u_1} L (@instDistribOfSemiring.{u_1} L inst_1))) (@DFunLike.coe.{max (u_2 + 1) (u_1 + 1), u_2 + 1, u_1 + 1} (@RingHom.{u_2, u_1} (↥O) L (@Semiring.toNonAssocSemiring.{u_2} (↥O) (@CommSemiring.toSemiring.{u_2} (↥O) (@SubsemiringClass.toCommSemiring.{u_2, u_2} (@ValuationSubring.{u_2} K inst) O K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) (@ValuationSubring.instSetLike.{u_2} K inst) (@SubringClass.toSubsemiringClass.{u_2, u_2} (@ValuationSubring.{u_2} K inst) K (@NonAssocCommRing.toNonAssocRing.{u_2} K (@CommRing.toNonAssocCommRing.{u_2} K (@Field.toCommRing.{u_2} K inst))) (@ValuationSubring.instSetLike.{u_2} K inst) (@ValuationSubring.instSubringClass.{u_2} K inst))))) (@Semiring.toNonAssocSemiring.{u_1} L inst_1)) (↥O) (fun x => L) (@RingHom.instFunLike.{u_2, u_1} (↥O) L (@Semiring.toNonAssocSemiring.{u_2} (↥O) (@CommSemiring.toSemiring.{u_2} (↥O) (@SubsemiringClass.toCommSemiring.{u_2, u_2} (@ValuationSubring.{u_2} K inst) O K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) (@ValuationSubring.instSetLike.{u_2} K inst) (@SubringClass.toSubsemiringClass.{u_2, u_2} (@ValuationSubring.{u_2} K inst) K (@NonAssocCommRing.toNonAssocRing.{u_2} K (@CommRing.toNonAssocCommRing.{u_2} K (@Field.toCommRing.{u_2} K inst))) (@ValuationSubring.instSetLike.{u_2} K inst) (@ValuationSubring.instSubringClass.{u_2} K inst))))) (@Semiring.toNonAssocSemiring.{u_1} L inst_1)) (@RingHom.comp.{u_2, u_2, u_1} (↥O) K L (@Semiring.toNonAssocSemiring.{u_2} (↥O) (@CommSemiring.toSemiring.{u_2} (↥O) (@SubsemiringClass.toCommSemiring.{u_2, u_2} (@ValuationSubring.{u_2} K inst) O K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) (@ValuationSubring.instSetLike.{u_2} K inst) (@SubringClass.toSubsemiringClass.{u_2, u_2} (@ValuationSubring.{u_2} K inst) K (@NonAssocCommRing.toNonAssocRing.{u_2} K (@CommRing.toNonAssocCommRing.{u_2} K (@Field.toCommRing.{u_2} K inst))) (@ValuationSubring.instSetLike.{u_2} K inst) (@ValuationSubring.instSubringClass.{u_2} K inst))))) (@Semiring.toNonAssocSemiring.{u_2} K (@CommSemiring.toSemiring.{u_2} K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))) (@Semiring.toNonAssocSemiring.{u_1} L inst_1) (@algebraMap.{u_2, u_1} K L (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) inst_1 inst_2) (@algebraMap.{u_2, u_2} (↥O) K (@SubsemiringClass.toCommSemiring.{u_2, u_2} (@ValuationSubring.{u_2} K inst) O K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)) (@ValuationSubring.instSetLike.{u_2} K inst) (@SubringClass.toSubsemiringClass.{u_2, u_2} (@ValuationSubring.{u_2} K inst) K (@NonAssocCommRing.toNonAssocRing.{u_2} K (@CommRing.toNonAssocCommRing.{u_2} K (@Field.toCommRing.{u_2} K inst))) (@ValuationSubring.instSetLike.{u_2} K inst) (@ValuationSubring.instSubringClass.{u_2} K inst))) (@CommSemiring.toSemiring.{u_2} K (@Semifield.toCommSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst))) (@ValuationSubring.instAlgebraSubtypeMem.{u_2} K inst O))) x) x_1) := sorry instance instAlgebraSubtypeMemValuationSubring_definitions {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] : Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' x y := instAlgebraSubtypeMemValuationSubring_definitions._proof_3 O x y
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom
namespace AlgebraicGeometry run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
end AlgebraicGeometry namespace ArithmeticThetaSheafTensor run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
variable (X : Scheme.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
def tensorPresheaf (H K : X.Modules) : X.PresheafOfModules := H.val ⊗ K.val
def sheafTensor (H K : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)
def tensorUnitMap (H K : X.Modules) : tensorPresheaf X H K ⟶ (sheafTensor X H K).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _
def tensorSection (H K : X.Modules) (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) : Γ(sheafTensor X H K, U) :=
  (tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X, U)] t)
variable (U : X.Opens)
def presheafOver : X.PresheafOfModules ⥤ PresheafOfModules.{u} (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj
end ArithmeticThetaSheafTensor namespace ArithmeticThetaTensorPower run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaSheafTensor
def tensorPower (X : Scheme.{u}) (H : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => sheafTensor X (tensorPower X H n) H
def tensorPowerSection (X : Scheme.{u}) (H : X.Modules) : (n : ℕ) → (U : X.Opens) → Γ(H, U) → Γ(tensorPower X H n, U)
  | 0, U, _ => (1 : Γ(X, U))
  | n + 1, U, s => tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s
end ArithmeticThetaTensorPower
namespace ArithmeticThetaPullback run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
section OriginalUnitContext
attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
def pullback_unit_iso (X Y : Scheme.{u}) (p : X ⟶ Y) : (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map p.base).Final := by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
end OriginalUnitContext
def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) :=
  fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
def sheafTensorMap (X : Scheme.{u}) {H H' K K' : X.Modules}
    (f : H ⟶ H') (g : K ⟶ K') : sheafTensor X H K ⟶ sheafTensor X H' K' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)
def sheafTensorCongr (X : Scheme.{u}) {H H' K K' : X.Modules} (e : H ≅ H') (d : K ≅ K') : sheafTensor X H K ≅ sheafTensor X H' K' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso d))
def tensorCurryAt (X : Scheme.{u}) (M N : X.PresheafOfModules) (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) :
    (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val where
  app V := ModuleCat.ofHom ((g.app (op V.unop.left)).hom.comp
    ((TensorProduct.mk (X.presheaf.obj (op V.unop.left)) _ _).flip
      (N.map V.unop.hom.op n)))
  naturality {V W} a := by
    ext m
    change g.app (op W.unop.left)
      (M.map a.unop.left.op m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n) =
      P.val.map a.unop.left.op
        (g.app (op V.unop.left) (m ⊗ₜ[Γ(X, V.unop.left)] N.map V.unop.hom.op n))
    rw [← PresheafOfModules.naturality_apply]
    change _ = g.app (op W.unop.left)
      (M.map a.unop.left.op m ⊗ₜ[Γ(X, W.unop.left)]
        N.map a.unop.left.op (N.map V.unop.hom.op n))
    rw [← PresheafOfModules.map_comp_apply]
    rfl
def localHomEquiv (X : Scheme.{u}) {M M' : X.PresheafOfModules} (f : M ⟶ M') [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] (P : X.Modules) (U : X.Opens) :
    ((presheafOver X U).obj M' ⟶ (SheafOfModules.over P U).val) ≃ ((presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) := by
  let J := Opens.grothendieckTopology X
  let f₀ := (PresheafOfModules.toPresheaf _).map f
  letI : PresheafOfModules.IsLocallySurjective (J.over U) ((presheafOver X U).map f) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) f₀
  letI : PresheafOfModules.IsLocallyInjective (J.over U) ((presheafOver X U).map f) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) f₀
  exact PresheafOfModules.homEquivOfIsLocallyBijective ((presheafOver X U).map f)
    (SheafOfModules.isSheaf (SheafOfModules.over P U))
def tensorCurryExtend (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) : (presheafOver X U).obj M' ⟶ (SheafOfModules.over P U).val :=
  (localHomEquiv X f P U).symm (tensorCurryAt X M N P g U n)
theorem tensorCurryExtend_fac (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) :
    (presheafOver X U).map f ≫ tensorCurryExtend X f P g U n = tensorCurryAt X M N P g U n :=
  (localHomEquiv X f P U).apply_symm_apply _
def localHomRestrict (X : Scheme.{u}) {M : X.PresheafOfModules} {P : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (k : (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) : (presheafOver X V).obj M ⟶ (SheafOfModules.over P V).val where
  app W := k.app (op (Over.mk (W.unop.hom ≫ homOfLE hVU)))
  naturality {W Z} a := by
    exact k.naturality ((Over.map (homOfLE hVU)).map a.unop).op
def localHomSMul (X : Scheme.{u}) {M : X.PresheafOfModules} {P : X.Modules} {U : X.Opens} (r : Γ(X, U))
    (k : (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) : (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val where
  app W := ModuleCat.ofHom ((X.presheaf.map W.unop.hom.op r) • (k.app W).hom)
  naturality {W Z} a := by
    ext m
    change (X.presheaf.map Z.unop.hom.op r) • k.app Z (M.map a.unop.left.op m) =
      P.val.map a.unop.left.op ((X.presheaf.map W.unop.hom.op r) • k.app W m)
    rw [PresheafOfModules.map_smul]
    have hk := PresheafOfModules.naturality_apply k a m
    change k.app Z (M.map a.unop.left.op m) = P.val.map a.unop.left.op (k.app W m) at hk
    rw [hk]
    congr 1
    change X.presheaf.map Z.unop.hom.op r =
      X.presheaf.map a.unop.left.op (X.presheaf.map W.unop.hom.op r)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
theorem tensorCurryExtend_restrict (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) {U V : X.Opens} (hVU : V ≤ U) (n : N.obj (op U)) : localHomRestrict X hVU (tensorCurryExtend X f P g U n) =
      tensorCurryExtend X f P g V (N.map (homOfLE hVU).op n) := by
  apply (localHomEquiv X f P V).injective
  change (presheafOver X V).map f ≫ _ = (presheafOver X V).map f ≫ _
  rw [tensorCurryExtend_fac]
  ext W m
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op (Over.mk (W.unop.hom ≫ homOfLE hVU))))
      (tensorCurryExtend_fac X f P g U n)) m
  change _ = g.app (op W.unop.left)
    (m ⊗ₜ[Γ(X, W.unop.left)] N.map (W.unop.hom ≫ homOfLE hVU).op n) at h
  rw [op_comp, PresheafOfModules.map_comp_apply] at h
  exact h
theorem tensorCurryExtend_add (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n n' : N.obj (op U)) : tensorCurryExtend X f P g U (n + n') =
      tensorCurryExtend X f P g U n + tensorCurryExtend X f P g U n' := by
  apply (localHomEquiv X f P U).injective
  change (presheafOver X U).map f ≫ _ = (presheafOver X U).map f ≫ _
  rw [Preadditive.comp_add, tensorCurryExtend_fac, tensorCurryExtend_fac, tensorCurryExtend_fac]
  ext W m
  change g.app (op W.unop.left) (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op (n + n')) =
    g.app (op W.unop.left) (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n) +
    g.app (op W.unop.left) (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n')
  rw [map_add, TensorProduct.tmul_add, map_add]
theorem tensorCurryExtend_smul (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (r : Γ(X, U)) (n : N.obj (op U)) : tensorCurryExtend X f P g U (r • n) =
      localHomSMul X r (tensorCurryExtend X f P g U n) := by
  apply (localHomEquiv X f P U).injective
  change (presheafOver X U).map f ≫ _ = (presheafOver X U).map f ≫ _
  rw [tensorCurryExtend_fac]
  ext W m
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app W) (tensorCurryExtend_fac X f P g U n)) m
  change g.app (op W.unop.left)
    (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op (r • n)) =
    (X.presheaf.map W.unop.hom.op r) •
      (tensorCurryExtend X f P g U n).app W (f.app (op W.unop.left) m)
  change (tensorCurryExtend X f P g U n).app W (f.app (op W.unop.left) m) =
    g.app (op W.unop.left) (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n) at h
  rw [h, PresheafOfModules.map_smul]
  change g.app (op W.unop.left)
    (m ⊗ₜ[Γ(X, W.unop.left)] ((X.presheaf.map W.unop.hom.op r) • N.map W.unop.hom.op n)) =
    (X.presheaf.map W.unop.hom.op r) •
      g.app (op W.unop.left) (m ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n)
  rw [TensorProduct.tmul_smul, map_smul]
def tensorExtendLeft (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) : M' ⊗ N ⟶ P.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ (tensorCurryExtend X f P g U.unop n).app (op (Over.mk (𝟙 U.unop))) m)
    (by intros; exact map_add _ _ _)
    (by intros; exact map_smul _ _ _)
    (by
      intro m n n'
      have h := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 U.unop))))
        (tensorCurryExtend_add X f P g U.unop n n')
      exact ConcreteCategory.congr_hom h m)
    (by
      intro r m n
      have h := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 U.unop))))
        (tensorCurryExtend_smul X f P g U.unop r n)
      have h' := ConcreteCategory.congr_hom h m
      change (tensorCurryExtend X f P g U.unop (r • n)).app (op (Over.mk (𝟙 U.unop))) m =
        (X.presheaf.map (𝟙 U.unop).op r) •
          (tensorCurryExtend X f P g U.unop n).app (op (Over.mk (𝟙 U.unop))) m at h'
      rw [show X.presheaf.map (𝟙 U.unop).op r = r from by
        rw [op_id, X.presheaf.map_id]; rfl] at h'
      exact h')
  naturality {U V} a := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    have h := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 V.unop))))
      (tensorCurryExtend_restrict X f P g (leOfHom a.unop) n)
    have h' := ConcreteCategory.congr_hom h (M'.map a m)
    change (tensorCurryExtend X f P g U.unop n).app (op (Over.mk a.unop))
        (M'.map a m) =
      (tensorCurryExtend X f P g V.unop (N.map a n)).app (op (Over.mk (𝟙 V.unop)))
        (M'.map a m) at h'
    change (tensorCurryExtend X f P g V.unop (N.map a n)).app (op (Over.mk (𝟙 V.unop)))
        (M'.map a m) =
      P.val.map a ((tensorCurryExtend X f P g U.unop n).app (op (Over.mk (𝟙 U.unop))) m)
    rw [← h']
    exact PresheafOfModules.naturality_apply (tensorCurryExtend X f P g U.unop n)
      (Over.homMk (V := Over.mk (𝟙 U.unop)) (U := Over.mk a.unop) a.unop).op m
theorem tensorExtendLeft_fac (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) : (f ⊗ₘ 𝟙 N) ≫ tensorExtendLeft X f P g = g := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  have h := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 U.unop))))
    (tensorCurryExtend_fac X f P g U.unop n)
  have h' := ConcreteCategory.congr_hom h m
  change (tensorCurryExtend X f P g U.unop n).app (op (Over.mk (𝟙 U.unop))) (f.app U m) =
    g.app U (m ⊗ₜ[Γ(X, U.unop)] N.map (𝟙 U.unop).op n) at h'
  rw [show N.map (𝟙 U.unop).op n = n from by rw [op_id, N.map_id]; rfl] at h'
  exact h'
theorem tensor_precomp_injective (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) : Function.Injective (fun g : M' ⊗ N ⟶ P.val ↦ (f ⊗ₘ 𝟙 N) ≫ g) := by
  intro g g' h
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  have hc : tensorCurryAt X M' N P g U.unop n = tensorCurryAt X M' N P g' U.unop n := by
    apply (localHomEquiv X f P U.unop).injective
    change (presheafOver X U.unop).map f ≫ _ = (presheafOver X U.unop).map f ≫ _
    ext W x
    have he := congrArg (fun k ↦ k.app (op W.unop.left)) h
    exact ConcreteCategory.congr_hom he (x ⊗ₜ[Γ(X, W.unop.left)] N.map W.unop.hom.op n)
  have he := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 U.unop)))) hc
  have he' := ConcreteCategory.congr_hom he m
  change g.app U (m ⊗ₜ[Γ(X, U.unop)] N.map (𝟙 U.unop).op n) =
    g'.app U (m ⊗ₜ[Γ(X, U.unop)] N.map (𝟙 U.unop).op n) at he'
  rw [show N.map (𝟙 U.unop).op n = n from by rw [op_id, N.map_id]; rfl] at he'
  exact he'
def tensorHomEquivOfLocallyBijective (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) : (M' ⊗ N ⟶ P.val) ≃ (M ⊗ N ⟶ P.val) where
  toFun g := (f ⊗ₘ 𝟙 N) ≫ g
  invFun g := tensorExtendLeft X f P g
  left_inv _g := tensor_precomp_injective X f P (tensorExtendLeft_fac X f P _)
  right_inv g := tensorExtendLeft_fac X f P g
theorem sheafify_tensor_isIso (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f ⊗ₘ 𝟙 N)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro P
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let e := ((adj.homEquiv (M' ⊗ N) P).trans
    (tensorHomEquivOfLocallyBijective X f P)).trans (adj.homEquiv (M ⊗ N) P).symm
  convert e.bijective using 1
  funext g
  apply (adj.homEquiv (M ⊗ N) P).injective
  change adj.homEquiv _ P (_ ≫ g) = adj.homEquiv _ P ((adj.homEquiv _ P).symm _)
  rw [Equiv.apply_symm_apply]
  exact adj.homEquiv_naturality_left (f ⊗ₘ 𝟙 N) g
theorem sheafify_tensor_right_isIso (X : Scheme.{u}) {M N N' : X.PresheafOfModules} (f : N ⟶ N')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (𝟙 M ⊗ₘ f)) := by
  let : SymmetricCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.symmetricCategory
  have h : (𝟙 M ⊗ₘ f) = (β_ M N).hom ≫ (f ⊗ₘ 𝟙 M) ≫ (β_ N' M).hom := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intros
    rfl
  have := sheafify_tensor_isIso X (N := M) f
  rw [h, Functor.map_comp, Functor.map_comp]
  infer_instance
def sheafificationTensorIso (X : Scheme.{u}) (M N : X.PresheafOfModules) : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M ⊗ N) ≅
      sheafTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M)
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj N) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit
  let J := Opens.grothendieckTopology X
  letI : PresheafOfModules.IsLocallySurjective J (η.app M) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J M.presheaf))
  letI : PresheafOfModules.IsLocallyInjective J (η.app M) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M.presheaf))
  letI : PresheafOfModules.IsLocallySurjective J (η.app N) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J N.presheaf))
  letI : PresheafOfModules.IsLocallyInjective J (η.app N) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J N.presheaf))
  haveI := sheafify_tensor_isIso X (N := N) (η.app M)
  haveI := sheafify_tensor_right_isIso X (M := (S.obj M).val) (η.app N)
  haveI : IsIso (S.map (η.app M ⊗ₘ η.app N)) := by
    have h : (η.app M ⊗ₘ η.app N) =
        (η.app M ⊗ₘ 𝟙 N) ≫ (𝟙 (S.obj M).val ⊗ₘ η.app N) := by
      ext U : 1
      apply ModuleCat.MonoidalCategory.tensor_ext
      intros
      rfl
    rw [h, S.map_comp]
    infer_instance
  exact asIso (S.map (η.app M ⊗ₘ η.app N))
def freePresheafTensorIso (X : Scheme.{u}) (F G : X.Opensᵒᵖ ⥤ Type u) : (PresheafOfModules.free X.ringCatSheaf.obj).obj F ⊗
      (PresheafOfModules.free X.ringCatSheaf.obj).obj G ≅ (PresheafOfModules.free X.ringCatSheaf.obj).obj (F ⊗ G) := by
  refine (PresheafOfModules.isoMk
    (fun U ↦ (ModuleCat.FreeMonoidal.μIso (X.presheaf.obj U) (F.obj U) (G.obj U)).symm) ?_).symm
  intro U V a
  apply ModuleCat.free_hom_ext
  rintro ⟨m, n⟩
  dsimp
  erw [ModuleCat.freeDesc_apply, ModuleCat.FreeMonoidal.μIso_inv_freeMk,
    ModuleCat.FreeMonoidal.μIso_inv_freeMk, PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
    ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
  rfl
def yonedaInfIso (X : Scheme.{u}) (U V : X.Opens) : yoneda.obj U ⊗ yoneda.obj V ≅ yoneda.obj (U ⊓ V) :=
  NatIso.ofComponents (fun W ↦ Equiv.toIso
    { toFun := fun h ↦ homOfLE (le_inf (leOfHom h.1) (leOfHom h.2))
      invFun := fun h ↦ (homOfLE ((leOfHom h).trans inf_le_left),
        homOfLE ((leOfHom h).trans inf_le_right))
      left_inv := fun _ ↦ Prod.ext (@Subsingleton.elim (W.unop ⟶ U) inferInstance _ _)
        (@Subsingleton.elim (W.unop ⟶ V) inferInstance _ _)
      right_inv := fun _ ↦ @Subsingleton.elim (W.unop ⟶ U ⊓ V) inferInstance _ _ })
    (fun {A B} _ ↦ by ext; exact @Subsingleton.elim (B.unop ⟶ U ⊓ V) inferInstance _ _)
def freeYonedaTensorIso (X : Scheme.{u}) (U V : X.Opens) : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U) ⊗
      (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ≅ (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (U ⊓ V)) :=
  freePresheafTensorIso X _ _ ≪≫
    (PresheafOfModules.free X.ringCatSheaf.obj).mapIso (yonedaInfIso X U V)
def presheafPullback (X Y : Scheme.{u}) (p : X ⟶ Y) : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pullback p.toRingCatSheafHom.hom
def presheafPushforward (X Y : Scheme.{u}) (p : X ⟶ Y) : X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward p.toRingCatSheafHom.hom
def presheafAdjunction (X Y : Scheme.{u}) (p : X ⟶ Y) : presheafPullback X Y p ⊣ presheafPushforward X Y p :=
  PresheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom.hom
def presheafPullbackFreeYonedaIso (X Y : Scheme.{u}) (p : X ⟶ Y) (U : Y.Opens) : (presheafPullback X Y p).obj
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) ≅ (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U)) :=
  ((PresheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom.hom).corepresentableBy _).uniqueUpToIso (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      p.toRingCatSheafHom.hom U)
theorem presheaf_natTrans_isIso (X : Scheme.{u}) {D : Type*} [Category* D] {F G : X.PresheafOfModules ⥤ D}
    [Limits.PreservesColimitsOfSize.{u,u} F] [Limits.PreservesColimitsOfSize.{u,u} G] (α : F ⟶ G) (h : ∀ U : X.Opens,
      IsIso (α.app ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)))) (M : X.PresheafOfModules) : IsIso (α.app M) := by
  have : Limits.PreservesColimitsOfSize.{0,0} F :=
    Limits.preservesSmallestColimits_of_preservesColimits F
  have : Limits.PreservesColimitsOfSize.{0,0} G :=
    Limits.preservesSmallestColimits_of_preservesColimits G
  have hSigma (Q : X.PresheafOfModules) : IsIso (α.app Q.freeYonedaCoproduct) := by
    let K := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := Q))
    have : IsIso (Functor.whiskerLeft K α) := by
      rw [NatTrans.isIso_iff_isIso_app]
      rintro ⟨i⟩
      exact h i.1.unop
    exact Limits.isIso_app_coconePt_of_preservesColimit K α
      (Limits.colimit.cocone K) (Limits.colimit.isColimit K)
  let K := Limits.parallelPair M.toFreeYonedaCoproduct 0
  have : IsIso (Functor.whiskerLeft K α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro (_ | _)
    · exact hSigma (Limits.kernel M.fromFreeYonedaCoproduct)
    · exact hSigma M
  exact Limits.isIso_app_coconePt_of_preservesColimit K α
    M.freeYonedaCoproductsCokernelCofork M.isColimitFreeYonedaCoproductsCokernelCofork
def presheafPushforwardTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : X.PresheafOfModules) : (presheafPushforward X Y p).obj M ⊗
      (presheafPushforward X Y p).obj N ⟶ (presheafPushforward X Y p).obj (M ⊗ N) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ (show M.obj (op (p ⁻¹ᵁ U.unop)) from m) ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)]
      (show N.obj (op (p ⁻¹ᵁ U.unop)) from n))
    (by intros; exact TensorProduct.add_tmul _ _ _)
    (by
      intro r m n
      change M.obj (op (p ⁻¹ᵁ U.unop)) at m
      change N.obj (op (p ⁻¹ᵁ U.unop)) at n
      change ((p.app U.unop r) • m) ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] n =
        (p.app U.unop r) • (m ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] n)
      exact (TensorProduct.smul_tmul' _ _ _).symm)
    (by intros; exact TensorProduct.tmul_add _ _ _)
    (by
      intro r m n
      change M.obj (op (p ⁻¹ᵁ U.unop)) at m
      change N.obj (op (p ⁻¹ᵁ U.unop)) at n
      change m ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] ((p.app U.unop r) • n) =
        (p.app U.unop r) • (m ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] n)
      exact TensorProduct.tmul_smul _ _ _)
  naturality _ := ModuleCat.MonoidalCategory.tensor_ext (by intros; rfl)
def presheafPullbackTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : Y.PresheafOfModules) : (presheafPullback X Y p).obj (M ⊗ N) ⟶
      (presheafPullback X Y p).obj M ⊗ (presheafPullback X Y p).obj N :=
  let adj := presheafAdjunction X Y p
  (adj.homEquiv _ _).symm ((adj.unit.app M ⊗ₘ adj.unit.app N) ≫
    presheafPushforwardTensorMap X Y p _ _)
theorem presheafPullbackTensorMap_homEquiv (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : Y.PresheafOfModules) :
    (presheafAdjunction X Y p).homEquiv _ _ (presheafPullbackTensorMap X Y p M N) =
      ((presheafAdjunction X Y p).unit.app M ⊗ₘ (presheafAdjunction X Y p).unit.app N) ≫ presheafPushforwardTensorMap X Y p _ _ :=
  ((presheafAdjunction X Y p).homEquiv _ _).apply_symm_apply _
theorem presheafPushforwardTensorMap_naturality (X Y : Scheme.{u}) (p : X ⟶ Y) {M M' N N' : X.PresheafOfModules} (f : M ⟶ M') (g : N ⟶ N') :
    ((presheafPushforward X Y p).map f ⊗ₘ (presheafPushforward X Y p).map g) ≫ presheafPushforwardTensorMap X Y p M' N' =
    presheafPushforwardTensorMap X Y p M N ≫ (presheafPushforward X Y p).map (f ⊗ₘ g) := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intros
  rfl
theorem presheafPullbackTensorMap_naturality (X Y : Scheme.{u}) (p : X ⟶ Y) {M M' N N' : Y.PresheafOfModules} (f : M ⟶ M') (g : N ⟶ N') :
    (presheafPullback X Y p).map (f ⊗ₘ g) ≫ presheafPullbackTensorMap X Y p M' N' = presheafPullbackTensorMap X Y p M N ≫
      ((presheafPullback X Y p).map f ⊗ₘ (presheafPullback X Y p).map g) := by
  let adj := presheafAdjunction X Y p
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rw [presheafPullbackTensorMap_homEquiv, presheafPullbackTensorMap_homEquiv]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  erw [adj.unit.naturality f, adj.unit.naturality g]
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  simp only [Functor.comp_map]
  rw [presheafPushforwardTensorMap_naturality, Category.assoc]
theorem presheafPullbackFreeYonedaIso_unit (X Y : Scheme.{u}) (p : X ⟶ Y) (U : Y.Opens) : (presheafAdjunction X Y p).unit.app
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) ≫ (presheafPushforward X Y p).map (presheafPullbackFreeYonedaIso X Y p U).hom =
    (PresheafOfModules.freeYonedaEquiv (M := (presheafPushforward X Y p).obj
        ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U))))).symm
      (ModuleCat.freeMk (𝟙 (p ⁻¹ᵁ U))) := by
  change (presheafAdjunction X Y p).homEquiv _ _
    (presheafPullbackFreeYonedaIso X Y p U).hom = _
  simp only [presheafPullbackFreeYonedaIso, Functor.CorepresentableBy.uniqueUpToIso_hom]
  change (presheafAdjunction X Y p).homEquiv _ _
    (((presheafAdjunction X Y p).homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl
theorem freeYonedaEquiv_symm_apply (X : Scheme.{u}) (M : X.PresheafOfModules) (U V : X.Opens) (i : V ⟶ U) (m : M.obj (op U)) :
    ((PresheafOfModules.freeYonedaEquiv (M := M)).symm m).app (op V)
      (ModuleCat.freeMk i) = M.map i.op m := by
  simp [PresheafOfModules.freeYonedaEquiv, PresheafOfModules.freeHomEquiv, yonedaEquiv]
  erw [ModuleCat.freeDesc_apply]
  rfl
theorem freePresheaf_map_freeMk (X : Scheme.{u}) (F : X.Opensᵒᵖ ⥤ Type u) {U V : X.Opensᵒᵖ} (a : U ⟶ V) (m : F.obj U) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj F).map a (ModuleCat.freeMk m) = ModuleCat.freeMk (F.map a m) := by
  exact ModuleCat.freeDesc_apply _ _
theorem presheafPullbackFreeYonedaIso_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y) (U V : Y.Opens) (i : V ⟶ U) :
    (presheafPullbackFreeYonedaIso X Y p U).hom.app (op (p ⁻¹ᵁ V)) (((presheafAdjunction X Y p).unit.app
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U))).app (op V)
          (ModuleCat.freeMk i)) = ModuleCat.freeMk ((TopologicalSpace.Opens.map p.base).map i) := by
  have h := congrArg (fun k ↦ k.app (op V)) (presheafPullbackFreeYonedaIso_unit X Y p U)
  have h' := ConcreteCategory.congr_hom h (ModuleCat.freeMk i)
  change _ = ((PresheafOfModules.freeYonedaEquiv
    (M := (presheafPushforward X Y p).obj
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U))))).symm
      (ModuleCat.freeMk (𝟙 (p ⁻¹ᵁ U)))).app (op V) (ModuleCat.freeMk i) at h'
  rw [freeYonedaEquiv_symm_apply] at h'
  change _ = ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U))).map
    ((TopologicalSpace.Opens.map p.base).map i).op (ModuleCat.freeMk (𝟙 (p ⁻¹ᵁ U))) at h'
  rw [freePresheaf_map_freeMk] at h'
  exact h'
theorem freeYonedaTensorIso_hom_apply (X : Scheme.{u}) (U V W : X.Opens) (i : W ⟶ U) (j : W ⟶ V) : (freeYonedaTensorIso X U V).hom.app (op W)
      (ModuleCat.freeMk i ⊗ₜ[Γ(X, W)] ModuleCat.freeMk j) = ModuleCat.freeMk (homOfLE (le_inf (leOfHom i) (leOfHom j))) := by
  change (ModuleCat.free (Γ(X, W))).map ((yonedaInfIso X U V).hom.app (op W))
    ((ModuleCat.FreeMonoidal.μIso (Γ(X, W)) _ _).hom
      (ModuleCat.freeMk i ⊗ₜ[Γ(X, W)] ModuleCat.freeMk j)) = _
  rw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk, ModuleCat.free_map_apply]
  rfl
theorem freeYonedaTensorIso_inv_apply (X : Scheme.{u}) (U V W : X.Opens) (i : W ⟶ U ⊓ V) :
    (freeYonedaTensorIso X U V).inv.app (op W) (ModuleCat.freeMk i) = ModuleCat.freeMk (homOfLE ((leOfHom i).trans inf_le_left)) ⊗ₜ[Γ(X, W)]
        ModuleCat.freeMk (homOfLE ((leOfHom i).trans inf_le_right)) := by
  change (ModuleCat.FreeMonoidal.μIso (Γ(X, W)) _ _).inv
    ((ModuleCat.free (Γ(X, W))).map ((yonedaInfIso X U V).inv.app (op W))
      (ModuleCat.freeMk i)) = _
  rw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.μIso_inv_freeMk]
  rfl
theorem presheafPullbackTensorMap_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : Y.PresheafOfModules) (U : Y.Opens) (m : M.obj (op U)) (n : N.obj (op U)) : (presheafPullbackTensorMap X Y p M N).app (op (p ⁻¹ᵁ U))
      (((presheafAdjunction X Y p).unit.app (M ⊗ N)).app (op U) (m ⊗ₜ[Γ(Y, U)] n)) = (show ((presheafPullback X Y p).obj M).obj (op (p ⁻¹ᵁ U)) from
      ((presheafAdjunction X Y p).unit.app M).app (op U) m) ⊗ₜ[Γ(X, p ⁻¹ᵁ U)] (show ((presheafPullback X Y p).obj N).obj (op (p ⁻¹ᵁ U)) from
      ((presheafAdjunction X Y p).unit.app N).app (op U) n) := by
  have h := congrArg (fun k ↦ k.app (op U)) (presheafPullbackTensorMap_homEquiv X Y p M N)
  have h' := ConcreteCategory.congr_hom h (m ⊗ₜ[Γ(Y, U)] n)
  exact h'
theorem presheafPullbackTensorMap_free_isIso (X Y : Scheme.{u}) (p : X ⟶ Y) (U V : Y.Opens) : IsIso (presheafPullbackTensorMap X Y p
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))) := by
  let L := presheafPullback X Y p
  let adj := presheafAdjunction X Y p
  let A := (PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)
  let B := (PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)
  let eY := freeYonedaTensorIso Y U V
  let eX := freeYonedaTensorIso X (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let eU := presheafPullbackFreeYonedaIso X Y p U
  let eV := presheafPullbackFreeYonedaIso X Y p V
  let eI := presheafPullbackFreeYonedaIso X Y p (U ⊓ V)
  let t := presheafPullbackTensorMap X Y p A B
  have he : L.map eY.inv ≫ t ≫ (eU.hom ⊗ₘ eV.hom) ≫ eX.hom = eI.hom := by
    apply (adj.homEquiv _ _).injective
    apply PresheafOfModules.freeYonedaEquiv.injective
    let z := ModuleCat.freeMk (R := Γ(Y, U ⊓ V)) (𝟙 (U ⊓ V))
    have hn := congrArg (fun k ↦ k.app (op (U ⊓ V))) (adj.unit.naturality eY.inv)
    have hn' := (ConcreteCategory.congr_hom hn z).symm
    change (L.map eY.inv).app (op (p ⁻¹ᵁ (U ⊓ V)))
      ((adj.unit.app _).app (op (U ⊓ V)) z) =
      (adj.unit.app (A ⊗ B)).app (op (U ⊓ V)) (eY.inv.app (op (U ⊓ V)) z) at hn'
    change eX.hom.app (op (p ⁻¹ᵁ (U ⊓ V)))
      ((eU.hom ⊗ₘ eV.hom).app (op (p ⁻¹ᵁ (U ⊓ V)))
        (t.app (op (p ⁻¹ᵁ (U ⊓ V)))
          ((L.map eY.inv).app (op (p ⁻¹ᵁ (U ⊓ V))) ((adj.unit.app _).app (op (U ⊓ V)) z)))) =
      eI.hom.app (op (p ⁻¹ᵁ (U ⊓ V))) ((adj.unit.app _).app (op (U ⊓ V)) z)
    rw [hn']
    dsimp only [z, eY]
    rw [freeYonedaTensorIso_inv_apply]
    erw [presheafPullbackTensorMap_unit_apply]
    change eX.hom.app (op (p ⁻¹ᵁ (U ⊓ V)))
      (eU.hom.app (op (p ⁻¹ᵁ (U ⊓ V)))
        ((adj.unit.app A).app (op (U ⊓ V)) (ModuleCat.freeMk (homOfLE inf_le_left))) ⊗ₜ[Γ(X, p ⁻¹ᵁ (U ⊓ V))]
      eV.hom.app (op (p ⁻¹ᵁ (U ⊓ V)))
        ((adj.unit.app B).app (op (U ⊓ V)) (ModuleCat.freeMk (homOfLE inf_le_right)))) = _
    erw [presheafPullbackFreeYonedaIso_unit_apply, presheafPullbackFreeYonedaIso_unit_apply,
      presheafPullbackFreeYonedaIso_unit_apply, freeYonedaTensorIso_hom_apply]
    rfl
  have : IsIso (L.map eY.inv ≫ t ≫ (eU.hom ⊗ₘ eV.hom) ≫ eX.hom) := he ▸ inferInstance
  have : IsIso (t ≫ (eU.hom ⊗ₘ eV.hom) ≫ eX.hom) :=
    IsIso.of_isIso_comp_left (L.map eY.inv) _
  have : IsIso (t ≫ (eU.hom ⊗ₘ eV.hom)) := by
    rw [← Category.assoc] at this
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact IsIso.of_isIso_comp_right t (eU.hom ⊗ₘ eV.hom)
def presheafPullbackTensorRight (X Y : Scheme.{u}) (p : X ⟶ Y) (M : Y.PresheafOfModules) : tensorLeft M ⋙ presheafPullback X Y p ⟶
      presheafPullback X Y p ⋙ tensorLeft ((presheafPullback X Y p).obj M) where
  app N := presheafPullbackTensorMap X Y p M N
  naturality {N N'} f := by
    have h := presheafPullbackTensorMap_naturality X Y p (𝟙 M) f
    rw [(presheafPullback X Y p).map_id] at h
    rw [id_tensorHom, id_tensorHom] at h
    exact h
def presheafPullbackTensorLeft (X Y : Scheme.{u}) (p : X ⟶ Y) (N : Y.PresheafOfModules) : tensorRight N ⋙ presheafPullback X Y p ⟶
      presheafPullback X Y p ⋙ tensorRight ((presheafPullback X Y p).obj N) where
  app M := presheafPullbackTensorMap X Y p M N
  naturality {M M'} f := by
    have h := presheafPullbackTensorMap_naturality X Y p f (𝟙 N)
    rw [(presheafPullback X Y p).map_id] at h
    rw [tensorHom_id, tensorHom_id] at h
    exact h
local instance tensorLeftPreserves (X : Scheme.{u}) (M : X.PresheafOfModules) : Limits.PreservesColimitsOfSize.{u,u} (tensorLeft M) := by
  change Limits.PreservesColimitsOfSize.{u,u}
    (tensorLeft (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M)
  infer_instance
local instance tensorRightPreserves (X : Scheme.{u}) (M : X.PresheafOfModules) : Limits.PreservesColimitsOfSize.{u,u} (tensorRight M) := by
  change Limits.PreservesColimitsOfSize.{u,u}
    (tensorRight (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M)
  infer_instance
theorem presheafPullbackTensorMap_isIso (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : Y.PresheafOfModules) : IsIso (presheafPullbackTensorMap X Y p M N) := by
  have : (presheafPullback X Y p).IsLeftAdjoint := (presheafAdjunction X Y p).isLeftAdjoint
  have hfree (U : Y.Opens) (Q : Y.PresheafOfModules) :
      IsIso (presheafPullbackTensorMap X Y p
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) Q) := by
    exact presheaf_natTrans_isIso Y
      (presheafPullbackTensorRight X Y p
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)))
      (fun V ↦ presheafPullbackTensorMap_free_isIso X Y p U V) Q
  exact presheaf_natTrans_isIso Y (presheafPullbackTensorLeft X Y p N) (fun U ↦ hfree U N) M
def presheafPullbackTensorIso (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : Y.PresheafOfModules) : (presheafPullback X Y p).obj (M ⊗ N) ≅
      (presheafPullback X Y p).obj M ⊗ (presheafPullback X Y p).obj N := by
  haveI := presheafPullbackTensorMap_isIso X Y p M N
  exact asIso (presheafPullbackTensorMap X Y p M N)
def pullback_sheafTensor_iso (X Y : Scheme.{u}) (p : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback p).obj (sheafTensor Y H K) ≅
      sheafTensor X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K) :=
  (SheafOfModules.sheafificationCompPullback p.toRingCatSheafHom).app (tensorPresheaf Y H K) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (presheafPullbackTensorIso X Y p H.val K.val) ≪≫
    sheafificationTensorIso X ((presheafPullback X Y p).obj H.val)
      ((presheafPullback X Y p).obj K.val) ≪≫
    sheafTensorCongr X ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm
def pullback_tensorPower_iso (X Y : Scheme.{u}) (p : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅
      tensorPower X ((Scheme.Modules.pullback p).obj H) n
  | 0 => pullback_unit_iso X Y p
  | n + 1 => pullback_sheafTensor_iso X Y p (tensorPower Y H n) H ≪≫ sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)
end ArithmeticThetaPullback
namespace ArithmeticThetaNormalizedSections run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaTensorPower
def IsLineBundle (X : Scheme.{u}) (H : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (SheafOfModules.unit (X.ringCatSheaf.over U) ≅ SheafOfModules.over H U)
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ)
    (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) :=
  (ArithmeticThetaPullback.pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens))
    (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
end ArithmeticThetaNormalizedSections
namespace ArithmeticThetaRelativeDiscriminantR0171 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun a : X.presheaf.obj (Opposite.op V) => a • res F h s)
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaTateCuspsR0181 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type u) [Field k]
abbrev Disk := Base (PowerSeries k)
abbrev Puncture := Base (LaurentSeries k)
def genericInclusion : Puncture k ⟶ Disk k :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
def diskStructure : Disk k ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))
end ArithmeticThetaTateCuspsR0181
namespace ArithmeticThetaOpenHodgeR0180 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaRelativeDiscriminantR0171
def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv v
end ArithmeticThetaOpenHodgeR0180
namespace ArithmeticThetaCommonHalfHodgeR0185 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
def along {Z Y B : Scheme} (g : Z ⟶ Y) (p : Y ⟶ B) (f : Z ⟶ B) (h : g ≫ p = f) (M : B.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback p).obj M) ≅ (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullbackComp g p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M
end ArithmeticThetaCommonHalfHodgeR0185
namespace ArithmeticThetaSimultaneousUnaryR0187
abbrev Sections (B : Scheme) (J : B.Modules) := J.presheaf.obj (Opposite.op ⊤)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
structure RootCover (k : Type) [Field k] (B : Scheme) (b : B ⟶ Spec (CommRingCat.of k)) (bound : ℕ) where
  space : Scheme
  map : space ⟶ B
  integral : IsIntegral space
  finite : IsFinite map
  flat : Flat map
  surjective : Surjective map
  proper : IsProper (map ≫ b)
  smooth : SmoothOfRelativeDimension 1 (map ≫ b)
  degree : ∀ x : B, 0 < map.finrank x ∧ map.finrank x ≤ bound
end ArithmeticThetaSimultaneousUnaryR0187
namespace ArithmeticThetaFiniteFieldModelsR0221 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaPullback ArithmeticThetaTensorPower
abbrev Base (k : Type) [CommRing k] := Spec (CommRingCat.of k)structure Curve (k : Type) [Field k] where
  space : Scheme
  map : space ⟶ Base k
  proper : IsProper map
  smooth : SmoothOfRelativeDimension 1 map
  geometricallyIntegral : GeometricallyIntegral map
abbrev Sections {X : Scheme} (H : X.Modules) := H.presheaf.obj (Opposite.op ⊤)
def powerIso {X : Scheme} {H J : X.Modules} (e : H ≅ J) : (n : ℕ) → tensorPower X H n ≅ tensorPower X J n
  | 0 => Iso.refl _
  | n+1 => sheafTensorCongr X (powerIso e n) e
def powerComparison {X Y : Scheme} (p : X ⟶ Y) (H : Y.Modules) {J : X.Modules} (e : (Scheme.Modules.pullback p).obj H ≅ J) (n : ℕ) :
    (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X J n :=
  pullback_tensorPower_iso X Y p H n ≪≫ powerIso e n
end ArithmeticThetaFiniteFieldModelsR0221
namespace ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
def triangle {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z) (t : X ⟶ Z) (h : p ≫ q = t) (H : Z.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj H) ≅ (Scheme.Modules.pullback t).obj H :=
  (Scheme.Modules.pullbackComp p q).app H ≪≫ (Scheme.Modules.pullbackCongr h).app H
def squareComparison {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T) (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t) (H : T.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj H) ≅ (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback t).obj H) :=
  triangle p q (r ≫ t) h H ≪≫ ((Scheme.Modules.pullbackComp r t).app H).symm
end ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
namespace ArithmeticThetaProjectiveEffectivityR0135 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace (S : Type u) [CommRing S] (N : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin N) S)
def projectiveStructure (S : Type u) [CommRing S] (N : ℕ) : projectiveSpace S N ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin N) S) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap S ((MvPolynomial.homogeneousSubmodule (Fin N) S) 0)))
end ArithmeticThetaProjectiveEffectivityR0135
namespace ArithmeticThetaPrescribedRootModelsR0224 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
structure ProjectivePresentation (k : Type) [Field k] (X : Scheme.{0}) (b : X ⟶ ArithmeticThetaFiniteFieldModelsR0221.Base k) where
  dimension : ℕ
  embedding : X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)
  closed : IsClosedImmersion embedding
  over_eq : embedding ≫
    ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = b
end ArithmeticThetaPrescribedRootModelsR0224
namespace ArithmeticThetaRamifiedRootModelsR0222 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaTensorPower ArithmeticThetaPullback
def pulledPower {X Y : Scheme} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Sections (tensorPower X H n)) :
    Sections (tensorPower Y ((Scheme.Modules.pullback p).obj H) n) :=
  (pullback_tensorPower_iso Y X p H n).hom.app ⊤
    (pullbackGlobalSection p (tensorPower X H n) F)
def RootEquation {X Y : Scheme} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Sections (tensorPower X H n))
    (r : Sections ((Scheme.Modules.pullback p).obj H)) : Prop :=
  tensorPowerSection Y ((Scheme.Modules.pullback p).obj H) n ⊤ r = pulledPower p H n F
end ArithmeticThetaRamifiedRootModelsR0222
namespace ArithmeticThetaValuativeRootsR0223 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaPullback
abbrev FieldPoint (Ω : Type) [Field Ω] := Spec (CommRingCat.of Ω)
abbrev ValuationPoint (Ω : Type) [Field Ω] (A : ValuationSubring Ω) :=
  Spec (CommRingCat.of A)
def genericInclusion (Ω : Type) [Field Ω] (A : ValuationSubring Ω) : FieldPoint Ω ⟶ ValuationPoint Ω A :=
  Spec.map (CommRingCat.ofHom (algebraMap A Ω))
def extendedDisk (k : Type) [Field k] (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A)
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) : ValuationPoint Ω A ⟶ Z :=
  Spec.map (CommRingCat.ofHom ρ) ≫ f
def extendedFrame (k : Type) [Field k] (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A)
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules) (h : Sections (ArithmeticThetaTateCuspsR0181.Disk k)
      ((Scheme.Modules.pullback f).obj J)) : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback (extendedDisk k Ω A ρ f)).obj J) :=
  ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom ρ)) f).app J).hom.app ⊤
    (pullbackGlobalSection (Spec.map (CommRingCat.ofHom ρ))
      ((Scheme.Modules.pullback f).obj J) h)
end ArithmeticThetaValuativeRootsR0223
namespace ArithmeticThetaConstantExtensionR0225 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections powerIso powerComparison)
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171 (IsFrame)
open ArithmeticThetaValuativeRootsR0223 (ValuationPoint genericInclusion)
open ArithmeticThetaRamifiedRootModelsR0222 (RootEquation)
open ArithmeticThetaPrescribedRootModelsR0224 (ProjectivePresentation)
abbrev Omega (k : Type) [Field k] := AlgebraicClosure k
abbrev FieldStage (k : Type) [Field k] := IntermediateField k (Omega k)
variable {k : Type} [Field k]
def constantMap (K : FieldStage k) : Base (Omega k) ⟶ Base K :=
  Spec.map (CommRingCat.ofHom K.subtype)
structure Model (X : Curve (Omega k)) (K : (FieldStage k)) where
  curve : Curve K
  projection : X.space ⟶ curve.space
  cartesian : IsPullback projection X.map curve.map (constantMap K)
def coverLineComparison {X Y : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) (N : Model Y K) (f : Y.space ⟶ X.space)
    (g : N.curve.space ⟶ M.curve.space) (hc : N.projection ≫ g = f ≫ M.projection) (H0 : M.curve.space.Modules) {H : X.space.Modules}
    (e : (Scheme.Modules.pullback M.projection).obj H0 ≅ H) : (Scheme.Modules.pullback N.projection).obj ((Scheme.Modules.pullback g).obj H0) ≅
      (Scheme.Modules.pullback f).obj H :=
  ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover.squareComparison N.projection g f M.projection hc H0 ≪≫
    (Scheme.Modules.pullback f).mapIso e
structure RootData (k : Type) [Field k] (s n : ℕ) where
  base : Curve (Omega k)
  cover : Curve (Omega k)
  map : cover.space ⟶ base.space
  over_eq : map ≫ base.map = cover.map
  finite : IsFinite map
  surjective : Surjective map
  degree : ∀ x : base.space, 0 < map.finrank x ∧ map.finrank x ≤ n^s
  cusp : Base (Omega k) ⟶ cover.space
  cusp_over : cusp ≫ cover.map = 𝟙 _
  line : base.space.Modules
  isLine : IsLineBundle base.space line
  powers : Fin s → Sections (tensorPower base.space line n)
  powers_nonzero : ∀ i, powers i ≠ 0
  roots : Fin s → Sections ((Scheme.Modules.pullback map).obj line)
  equation : ∀ i, RootEquation map line n (powers i) (roots i)
structure RootModel {s n : ℕ} (D : RootData k s n) (K : (FieldStage k)) where
  base : Model D.base K
  cover : Model D.cover K
  map : cover.curve.space ⟶ base.curve.space
  over_eq : map ≫ base.curve.map = cover.curve.map
  comparison : cover.projection ≫ map = D.map ≫ base.projection
  cartesian : IsPullback cover.projection D.map map base.projection
  finite : IsFinite map
  surjective : Surjective map
  degree_comparison : ∀ x : D.base.space,
    map.finrank (base.projection x) = D.map.finrank x
  degree : ∀ x : base.curve.space, 0 < map.finrank x ∧ map.finrank x ≤ n^s
  cusp : Base K ⟶ cover.curve.space
  cusp_over : cusp ≫ cover.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.projection
  line : base.curve.space.Modules
  isLine : IsLineBundle base.curve.space line
  lineComparison : (Scheme.Modules.pullback base.projection).obj line ≅ D.line
  powers : Fin s → Sections (tensorPower base.curve.space line n)
  powers_nonzero : ∀ i, powers i ≠ 0
  powers_comparison : ∀ i,
    (powerComparison base.projection line lineComparison n).hom.app ⊤
      (pullbackGlobalSection base.projection (tensorPower base.curve.space line n)
        (powers i)) = D.powers i
  roots : Fin s → Sections ((Scheme.Modules.pullback map).obj line)
  roots_comparison : ∀ i,
    (coverLineComparison base cover D.map map comparison line lineComparison).hom.app ⊤
      (pullbackGlobalSection cover.projection ((Scheme.Modules.pullback map).obj line)
        (roots i)) = D.roots i
  equation : ∀ i, RootEquation map line n (powers i) (roots i)
def modelFrameComparison {s n : ℕ} {D : RootData k s n} {K : (FieldStage k)} (M : RootModel D K) {V : Scheme.{0}} (f : V ⟶ D.base.space) :
    (Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line ≅ (Scheme.Modules.pullback f).obj D.line :=
  ((Scheme.Modules.pullbackComp f M.base.projection).app M.line).symm ≪≫
    (Scheme.Modules.pullback f).mapIso M.lineComparison
def modelFrame {s n : ℕ} {D : RootData k s n} {K : (FieldStage k)} (M : RootModel D K) {V : Scheme.{0}} (f : V ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line)) : Sections ((Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line) :=
  (modelFrameComparison M f).inv.app ⊤ h
def ModelBranchValues {s n : ℕ} {D : RootData k s n} {K : (FieldStage k)} (M : RootModel D K) (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ D.base.space) (h : Sections ((Scheme.Modules.pullback f).obj D.line)) (a : Fin s → A)
    (g : ValuationPoint E A ⟶ D.cover.space) : Prop :=
  IsFrame ((Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line) ⊤
      (modelFrame M f h) ∧
    ∃ hg : (g ≫ M.cover.projection) ≫ M.map = f ≫ M.base.projection,
      ∀ j, (ArithmeticThetaCommonHalfHodgeR0185.along (g ≫ M.cover.projection)
        M.map (f ≫ M.base.projection) hg M.line).hom.app ⊤
          (pullbackGlobalSection (g ≫ M.cover.projection)
            ((Scheme.Modules.pullback M.map).obj M.line) (M.roots j)) =
          ArithmeticThetaOpenHodgeR0180.scalar A (a j) • modelFrame M f h
structure RootRealization (X : Curve (Omega k)) (J : X.space.Modules) (n s : ℕ) (F : Fin s → Sections (tensorPower X.space J n))
    (E : Type) [Field E] (A : ValuationSubring E) (f : ValuationPoint E A ⟶ X.space)
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : Fin s → E)
    (c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A) where
  cover : ArithmeticThetaSimultaneousUnaryR0187.RootCover (Omega k) X.space X.map (n^s)
  geometric : GeometricallyIntegral (cover.map ≫ X.map)
  line : IsLineBundle X.space J
  powers_nonzero : ∀ j, F j ≠ 0
  coefficients : Fin s → A
  coefficients_eq : ∀ j, algebraMap A E (coefficients j) = r j
  lift : ValuationPoint E A ⟶ cover.space
  lift_eq : lift ≫ cover.map = f
  dominant : IsDominant (genericInclusion E A ≫ lift)
  roots : Fin s → Sections ((Scheme.Modules.pullback cover.map).obj J)
  roots_nonzero : ∀ j, roots j ≠ 0
  equation : ∀ j, RootEquation cover.map J n (F j) (roots j)
  values : ∀ j,
    (ArithmeticThetaCommonHalfHodgeR0185.along lift cover.map f lift_eq J).hom.app ⊤
      (pullbackGlobalSection lift ((Scheme.Modules.pullback cover.map).obj J) (roots j)) =
        ArithmeticThetaOpenHodgeR0180.scalar A (coefficients j) • h
  centre_over : (c ≫ lift) ≫ (cover.map ≫ X.map) = 𝟙 _
def RootRealization.data {X : Curve (Omega k)} {J : X.space.Modules} {n s : ℕ} {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E} {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E} {c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) : RootData k s n where
  base := X
  cover := ⟨T.cover.space, T.cover.map ≫ X.map, T.cover.proper, T.cover.smooth, T.geometric⟩
  map := T.cover.map
  over_eq := rfl
  finite := T.cover.finite
  surjective := T.cover.surjective
  degree := T.cover.degree
  cusp := c ≫ T.lift
  cusp_over := T.centre_over
  line := J
  isLine := T.line
  powers := F
  powers_nonzero := T.powers_nonzero
  roots := T.roots
  equation := T.equation
def FiniteRealization {X : Curve (Omega k)} {J : X.space.Modules} {n s : ℕ} {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E} {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E} {c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) (K0 : (FieldStage k)) : Prop :=
  ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧
    ∃ M : RootModel T.data K,
      Nonempty (ProjectivePresentation K M.base.curve.space M.base.curve.map) ∧
      Nonempty (ProjectivePresentation K M.cover.curve.space M.cover.curve.map) ∧
      ModelBranchValues M E A f h T.coefficients T.lift
end ArithmeticThetaConstantExtensionR0225
namespace ArithmeticThetaAlgebraicBranchesR0226 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Base Sections)
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaValuativeRootsR0223 (ValuationPoint)
def seriesMap (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E] : PowerSeries k →+* E :=
  (algebraMap (LaurentSeries k) E).comp (algebraMap (PowerSeries k) (LaurentSeries k))
structure ValuationExtension (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E] where
  ring : ValuationSubring E
  inclusion : PowerSeries k →+* ring
  compatible : (algebraMap ring E).comp inclusion = seriesMap k E
  isLocal : IsLocalHom inclusion
structure BranchValuation (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E] extends ValuationExtension k E where
  residue : ring →+* k
  residue_comp : residue.comp inclusion = (PowerSeries.constantCoeff : PowerSeries k →+* k)
  residue_kernel : RingHom.ker residue = IsLocalRing.maximalIdeal ring
variable {k E : Type} [Field k] [Field E] [Algebra (LaurentSeries k) E]
def BranchValuation.centre (B : BranchValuation k E) : Base k ⟶ ValuationPoint E B.ring := Spec.map (CommRingCat.ofHom B.residue)
def fieldDisk {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) : Base E ⟶ Z := Spec.map (CommRingCat.ofHom (seriesMap k E)) ≫ f
def fieldFrame {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules) (h : Sections ((Scheme.Modules.pullback f).obj J)) :
    Sections ((Scheme.Modules.pullback (fieldDisk (E := E) f)).obj J) :=
  ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (seriesMap k E))) f).app J).hom.app ⊤
    (pullbackGlobalSection (Spec.map (CommRingCat.ofHom (seriesMap k E)))
      ((Scheme.Modules.pullback f).obj J) h)
def Equation {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules) (n : ℕ) (F : Sections (tensorPower Z J n))
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : E) : Prop :=
  pullbackPowerSection (fieldDisk (E := E) f) J n F =
    ArithmeticThetaOpenHodgeR0180.scalar E (r ^ n) •
      tensorPowerSection (Base E) ((Scheme.Modules.pullback (fieldDisk (E := E) f)).obj J)
        n ⊤ (fieldFrame (E := E) f J h)
end ArithmeticThetaAlgebraicBranchesR0226
namespace ArithmeticThetaAmbientCompletedRootsR0227 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections)
open ArithmeticThetaConstantExtensionR0225 (Omega FieldStage RootRealization FiniteRealization)
open ArithmeticThetaAlgebraicBranchesR0226 (BranchValuation fieldDisk fieldFrame)
open ArithmeticThetaValuativeRootsR0223 (extendedDisk extendedFrame)
def IsCompletedDisk (k : Type) [Field k] (X : Curve k) (x : X.space) (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ X.space) : Prop :=
  f ≫ X.map = ArithmeticThetaTateCuspsR0181.diskStructure k ∧
  f (IsLocalRing.closedPoint (PowerSeries k)) = x ∧
  IsDominant (ArithmeticThetaTateCuspsR0181.genericInclusion k ≫ f) ∧
  ∃ e : AdicCompletion
      (IsLocalRing.maximalIdeal (X.space.presheaf.stalk (f (IsLocalRing.closedPoint (PowerSeries k)))))
      (X.space.presheaf.stalk (f (IsLocalRing.closedPoint (PowerSeries k)))) ≃+* PowerSeries k,
    ∀ a, e (algebraMap _ _ a) = (Scheme.stalkClosedPointTo f).hom a
def selectedField (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E] (s : ℕ) (r : Fin s → E) : IntermediateField (LaurentSeries k) E :=
  IntermediateField.adjoin (LaurentSeries k) (Set.range r)
structure AlgebraicModel (k : Type) [Field k] (X : Curve (Omega k)) (J : X.space.Modules) (n s : ℕ)
    (F : Fin s → Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)) (f : ArithmeticThetaTateCuspsR0181.Disk (Omega k) ⟶ X.space)
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (E : Type) [Field E] [Algebra (LaurentSeries (Omega k)) E]
    (r : Fin s → E) (K0 : FieldStage k) where
  field : IntermediateField (LaurentSeries (Omega k)) E
  field_eq : field = selectedField (Omega k) E s r
  finite : FiniteDimensional (LaurentSeries (Omega k)) field
  prescribed : Fin s → field
  prescribed_eq : ∀ j, field.subtype (prescribed j) = r j
  branch : BranchValuation (Omega k) field
  centre : branch.centre (IsLocalRing.closedPoint (Omega k)) =
    IsLocalRing.closedPoint branch.ring
  realization : RootRealization X J n s F field branch.ring
    (extendedDisk (Omega k) field branch.ring branch.inclusion f)
    (extendedFrame (Omega k) field branch.ring branch.inclusion f J h)
    prescribed branch.centre
  base_projective : Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation
    (Omega k) X.space X.map)
  cover_projective : Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation
    (Omega k) realization.cover.space (realization.cover.map ≫ X.map))
  finite_model : FiniteRealization realization K0
variable {k : Type} [Field k] {X : Curve (Omega k)} {J : X.space.Modules}
    {n s : ℕ} {F : Fin s → Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)}
    {f : ArithmeticThetaTateCuspsR0181.Disk (Omega k) ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)}
    {E : Type} [Field E] [Algebra (LaurentSeries (Omega k)) E]
    {r : Fin s → E} {K0 : FieldStage k}
def AlgebraicModel.ambientLift (M : AlgebraicModel k X J n s F f h E r K0) : Base E ⟶ M.realization.cover.space :=
  Spec.map (CommRingCat.ofHom M.field.subtype) ≫
    ArithmeticThetaValuativeRootsR0223.genericInclusion M.field M.branch.ring ≫
      M.realization.lift
def AmbientValues (M : AlgebraicModel k X J n s F f h E r K0) : Prop :=
  IsDominant M.ambientLift ∧
  ∃ he : M.ambientLift ≫ M.realization.cover.map = fieldDisk (E := E) f,
    ∀ j, (ArithmeticThetaCommonHalfHodgeR0185.along M.ambientLift
      M.realization.cover.map (fieldDisk (E := E) f) he J).hom.app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection M.ambientLift
        ((Scheme.Modules.pullback M.realization.cover.map).obj J)
        (M.realization.roots j)) =
      ArithmeticThetaOpenHodgeR0180.scalar E (r j) • fieldFrame (E := E) f J h
end ArithmeticThetaAmbientCompletedRootsR0227
namespace ArithmeticThetaPalomarAmbient355 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
theorem ambient_prescribed_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space), CategoryTheory.CategoryStruct.comp f X.map = ArithmeticThetaTateCuspsR0181.diskStructure (ArithmeticThetaConstantExtensionR0225.Omega k) → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion (ArithmeticThetaConstantExtensionR0225.Omega k)) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by sorry
end ArithmeticThetaPalomarAmbient355
namespace ArithmeticThetaPalomarAmbient355 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
theorem smooth_point_simultaneous_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ x : X.space, IsClosed ({x} : Set X.space) → ∃ f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space, ArithmeticThetaAmbientCompletedRootsR0227.IsCompletedDisk (ArithmeticThetaConstantExtensionR0225.Omega k) X x f ∧ (∃ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h) ∧ ∀ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by sorry
end ArithmeticThetaPalomarAmbient355
end
end
end Package00
section Package01
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarSharp360 run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {}
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
noncomputable def thetaMap {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
def pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j
def project {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => pairing A b b * v i - pairing A b v * b i
def step {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun i j => if k < j then project A (fun a => C a k) (fun a => C a j) i
    else C i j)
def runPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).take k).foldl (step A) 1
def basisMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := runPrefix A n
def norms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  pairing A (fun i => basisMatrix A i j) (fun i => basisMatrix A i j)
def naturalNorms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
  (norms A j).toNat
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def distinctNorms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (distinctNorms A).card
def level (N : ℕ) : ℕ := 24 * N^2
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
/-- Full original sharp kernel conclusion plus actual shell finiteness. -/
theorem sharpFiniteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    (∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧
    (n = 0 → cutoff A = 0 ∧ ∀ c : Fin h → ℂ,
      thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  sorry
end ArithmeticThetaPalomarSharp360
end
end Package01
