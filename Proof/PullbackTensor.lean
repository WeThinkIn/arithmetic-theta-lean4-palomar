module

public import PullbackUnit
public import PullbackTensorDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace ArithmeticThetaPullback

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

/-- Functoriality of the genuine sheaf tensor, induced by sheafification. -/
def sheafTensorMap (X : Scheme.{u}) {H H' K K' : X.Modules}
    (f : H ⟶ H') (g : K ⟶ K') : sheafTensor X H K ⟶ sheafTensor X H' K' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)

/-- The genuine sheaf tensor transports isomorphisms in both factors. -/
def sheafTensorCongr (X : Scheme.{u}) {H H' K K' : X.Modules}
    (e : H ≅ H') (d : K ≅ K') : sheafTensor X H K ≅ sheafTensor X H' K' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso d))

/-- The sectionwise tensor pairing for pushforward, before source sheafification. -/
def pushforwardTensorPresheafMap (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : X.Modules) :
    tensorPresheaf Y ((Scheme.Modules.pushforward p).obj M)
      ((Scheme.Modules.pushforward p).obj N) ⟶
    ((Scheme.Modules.pushforward p).obj (sheafTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ tensorSection X M N (p ⁻¹ᵁ U.unop) m n)
    (by intros; simp [tensorSection, TensorProduct.add_tmul])
    (by
      intro r m n
      change Γ(M, p ⁻¹ᵁ U.unop) at m
      change Γ(N, p ⁻¹ᵁ U.unop) at n
      change (tensorUnitMap X M N).app _
        (((p.app U.unop r) • m) ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] n) =
        (p.app U.unop r) • (tensorUnitMap X M N).app _ (m ⊗ₜ n)
      erw [← TensorProduct.smul_tmul', map_smul])
    (by intros; simp [tensorSection, TensorProduct.tmul_add])
    (by
      intro r m n
      change Γ(M, p ⁻¹ᵁ U.unop) at m
      change Γ(N, p ⁻¹ᵁ U.unop) at n
      change (tensorUnitMap X M N).app _
        (m ⊗ₜ[Γ(X, p ⁻¹ᵁ U.unop)] ((p.app U.unop r) • n)) =
        (p.app U.unop r) • (tensorUnitMap X M N).app _ (m ⊗ₜ n)
      erw [TensorProduct.tmul_smul, map_smul])
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (tensorSection_restrict X M N (p ⁻¹ᵁ U.unop) (p ⁻¹ᵁ V.unop)
      (show p ⁻¹ᵁ V.unop ≤ p ⁻¹ᵁ U.unop from
        (TopologicalSpace.Opens.map p.base).monotone (leOfHom f.unop)) m n).symm

/-- The canonical lax tensor morphism of pushforward. -/
def pushforwardTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : X.Modules) :
    sheafTensor Y ((Scheme.Modules.pushforward p).obj M)
      ((Scheme.Modules.pushforward p).obj N) ⟶
    (Scheme.Modules.pushforward p).obj (sheafTensor X M N) :=
  (tensorHomEquiv Y _ _ _).symm (pushforwardTensorPresheafMap X Y p M N)

/-- The adjoint of the canonical pullback tensor comparison. -/
def pullbackTensorAdjoint (X Y : Scheme.{u}) (p : X ⟶ Y) (H K : Y.Modules) :
    sheafTensor Y H K ⟶ (Scheme.Modules.pushforward p).obj
      (sheafTensor X ((Scheme.Modules.pullback p).obj H)
        ((Scheme.Modules.pullback p).obj K)) :=
  sheafTensorMap Y ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app K) ≫
      pushforwardTensorMap X Y p _ _

/-- The canonical pullback tensor comparison obtained from the actual adjunctions. -/
def pullbackTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y) (H K : Y.Modules) :
    (Scheme.Modules.pullback p).obj (sheafTensor Y H K) ⟶
      sheafTensor X ((Scheme.Modules.pullback p).obj H)
        ((Scheme.Modules.pullback p).obj K) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm
    (pullbackTensorAdjoint X Y p H K)

/-- Naturality of the sheafification unit for the tensor morphism. -/
theorem sheafTensorMap_unit (X : Scheme.{u}) {H H' K K' : X.Modules}
    (f : H ⟶ H') (g : K ⟶ K') :
    tensorUnitMap X H K ≫ (sheafTensorMap X f g).val =
      (f.val ⊗ₘ g.val) ≫ tensorUnitMap X H' K' := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality (f.val ⊗ₘ g.val)).symm

/-- Functoriality on pure local tensor sections. -/
theorem sheafTensorMap_section (X : Scheme.{u}) {H H' K K' : X.Modules}
    (f : H ⟶ H') (g : K ⟶ K') (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (sheafTensorMap X f g).app U (tensorSection X H K U s t) =
      tensorSection X H' K' U (f.app U s) (g.app U t) := by
  have h := congrArg (fun h ↦ h.app (op U)) (sheafTensorMap_unit X f g)
  have h' := ConcreteCategory.congr_hom h (s ⊗ₜ[Γ(X, U)] t)
  exact h'

/-- The pushforward comparison is the expected pairing on every open. -/
theorem pushforwardTensorMap_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : X.Modules) (U : Y.Opens)
    (s : Γ((Scheme.Modules.pushforward p).obj M, U))
    (t : Γ((Scheme.Modules.pushforward p).obj N, U)) :
    (pushforwardTensorMap X Y p M N).app U
      (tensorSection Y _ _ U s t) = tensorSection X M N (p ⁻¹ᵁ U) s t := by
  have h := congrArg (fun h ↦ h.app (op U))
    (tensorHomEquiv_symm_unit Y _ _ _ (pushforwardTensorPresheafMap X Y p M N))
  have h' := ConcreteCategory.congr_hom h (s ⊗ₜ[Γ(Y, U)] t)
  exact h'

/-- Characterization of the tensor comparison by the actual adjunction unit. -/
theorem pullbackTensorMap_unit (X Y : Scheme.{u}) (p : X ⟶ Y) (H K : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (sheafTensor Y H K) ≫
      (Scheme.Modules.pushforward p).map (pullbackTensorMap X Y p H K) =
    pullbackTensorAdjoint X Y p H K := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).apply_symm_apply _

/-- The canonical comparison sends a pulled-back pure tensor to the tensor of pullbacks. -/
theorem pullbackTensorMap_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H K : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (pullbackTensorMap X Y p H K).app (p ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
        (sheafTensor Y H K)).app U (tensorSection Y H K U s t)) =
    tensorSection X _ _ (p ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H).app U s)
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app K).app U t) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.app U) (pullbackTensorMap_unit X Y p H K))
    (tensorSection Y H K U s t)
  change _ = (pushforwardTensorMap X Y p _ _).app U
    ((sheafTensorMap Y _ _).app U (tensorSection Y H K U s t)) at h
  rw [sheafTensorMap_section, pushforwardTensorMap_section] at h
  exact h

/-- A tensor morphism with its second argument fixed on an open is a morphism
of module presheaves on the slice site. This permits descent through sheafification. -/
def tensorCurryAt (X : Scheme.{u}) (M N : X.PresheafOfModules) (P : X.Modules)
    (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) :
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

/-- Descent of module morphisms on a slice along a locally bijective map. -/
def localHomEquiv (X : Scheme.{u}) {M M' : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (U : X.Opens) :
    ((presheafOver X U).obj M' ⟶ (SheafOfModules.over P U).val) ≃
      ((presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) := by
  let J := Opens.grothendieckTopology X
  let f₀ := (PresheafOfModules.toPresheaf _).map f
  letI : PresheafOfModules.IsLocallySurjective (J.over U) ((presheafOver X U).map f) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) f₀
  letI : PresheafOfModules.IsLocallyInjective (J.over U) ((presheafOver X U).map f) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) f₀
  exact PresheafOfModules.homEquivOfIsLocallyBijective ((presheafOver X U).map f)
    (SheafOfModules.isSheaf (SheafOfModules.over P U))

/-- Extend the first argument of a bilinear pairing locally by sheaf descent. -/
def tensorCurryExtend (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) :
    (presheafOver X U).obj M' ⟶ (SheafOfModules.over P U).val :=
  (localHomEquiv X f P U).symm (tensorCurryAt X M N P g U n)

theorem tensorCurryExtend_fac (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n : N.obj (op U)) :
    (presheafOver X U).map f ≫ tensorCurryExtend X f P g U n = tensorCurryAt X M N P g U n :=
  (localHomEquiv X f P U).apply_symm_apply _

/-- Restriction of a module morphism between presheaves on an open slice. -/
def localHomRestrict (X : Scheme.{u}) {M : X.PresheafOfModules} {P : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U)
    (k : (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) :
    (presheafOver X V).obj M ⟶ (SheafOfModules.over P V).val where
  app W := k.app (op (Over.mk (W.unop.hom ≫ homOfLE hVU)))
  naturality {W Z} a := by
    exact k.naturality ((Over.map (homOfLE hVU)).map a.unop).op

/-- Scalar multiplication of a local module morphism by a section on the base open. -/
def localHomSMul (X : Scheme.{u}) {M : X.PresheafOfModules} {P : X.Modules}
    {U : X.Opens} (r : Γ(X, U))
    (k : (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val) :
    (presheafOver X U).obj M ⟶ (SheafOfModules.over P U).val where
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
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) {U V : X.Opens} (hVU : V ≤ U)
    (n : N.obj (op U)) :
    localHomRestrict X hVU (tensorCurryExtend X f P g U n) =
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
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens) (n n' : N.obj (op U)) :
    tensorCurryExtend X f P g U (n + n') =
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
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) (U : X.Opens)
    (r : Γ(X, U)) (n : N.obj (op U)) :
    tensorCurryExtend X f P g U (r • n) =
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

/-- Descent of a tensor pairing in its first factor along a locally bijective morphism. -/
def tensorExtendLeft (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
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

/-- Descent recovers the original pairing after precomposition. -/
theorem tensorExtendLeft_fac (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) (g : M ⊗ N ⟶ P.val) :
    (f ⊗ₘ 𝟙 N) ≫ tensorExtendLeft X f P g = g := by
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

/-- A locally surjective first-factor map detects equality of pairings into a sheaf. -/
theorem tensor_precomp_injective (X : Scheme.{u}) {M M' N : X.PresheafOfModules} (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) :
    Function.Injective (fun g : M' ⊗ N ⟶ P.val ↦ (f ⊗ₘ 𝟙 N) ≫ g) := by
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

/-- Sheaf descent gives the universal-property equivalence for a tensor factor. -/
def tensorHomEquivOfLocallyBijective (X : Scheme.{u}) {M M' N : X.PresheafOfModules}
    (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    (P : X.Modules) : (M' ⊗ N ⟶ P.val) ≃ (M ⊗ N ⟶ P.val) where
  toFun g := (f ⊗ₘ 𝟙 N) ≫ g
  invFun g := tensorExtendLeft X f P g
  left_inv _g := tensor_precomp_injective X f P (tensorExtendLeft_fac X f P _)
  right_inv g := tensorExtendLeft_fac X f P g

/-- Sheafification inverts tensoring a locally bijective first-factor map. -/
theorem sheafify_tensor_isIso (X : Scheme.{u}) {M M' N : X.PresheafOfModules}
    (f : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] :
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

/-- The corresponding descent result in the second factor, using tensor symmetry. -/
theorem sheafify_tensor_right_isIso (X : Scheme.{u}) {M N N' : X.PresheafOfModules}
    (f : N ⟶ N')
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] :
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

/-- Sheafification commutes with the genuine sheaf tensor. Both unit maps are
inverted using descent into arbitrary target module sheaves. -/
def sheafificationTensorIso (X : Scheme.{u}) (M N : X.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M ⊗ N) ≅
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

/-- Pointwise tensor products of free presheaves are free on pairs of generators. -/
def freePresheafTensorIso (X : Scheme.{u})
    (F G : X.Opensᵒᵖ ⥤ Type u) :
    (PresheafOfModules.free X.ringCatSheaf.obj).obj F ⊗
      (PresheafOfModules.free X.ringCatSheaf.obj).obj G ≅
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (F ⊗ G) := by
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

/-- Yoneda takes intersections of opens to products of represented presheaves. -/
def yonedaInfIso (X : Scheme.{u}) (U V : X.Opens) :
    yoneda.obj U ⊗ yoneda.obj V ≅ yoneda.obj (U ⊓ V) :=
  NatIso.ofComponents (fun W ↦ Equiv.toIso
    { toFun := fun h ↦ homOfLE (le_inf (leOfHom h.1) (leOfHom h.2))
      invFun := fun h ↦ (homOfLE ((leOfHom h).trans inf_le_left),
        homOfLE ((leOfHom h).trans inf_le_right))
      left_inv := fun _ ↦ Prod.ext (@Subsingleton.elim (W.unop ⟶ U) inferInstance _ _)
        (@Subsingleton.elim (W.unop ⟶ V) inferInstance _ _)
      right_inv := fun _ ↦ @Subsingleton.elim (W.unop ⟶ U ⊓ V) inferInstance _ _ })
    (fun {A B} _ ↦ by ext; exact @Subsingleton.elim (B.unop ⟶ U ⊓ V) inferInstance _ _)

/-- Tensor of free represented module presheaves is represented by the intersection. -/
def freeYonedaTensorIso (X : Scheme.{u}) (U V : X.Opens) :
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U) ⊗
      (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ≅
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (U ⊓ V)) :=
  freePresheafTensorIso X _ _ ≪≫
    (PresheafOfModules.free X.ringCatSheaf.obj).mapIso (yonedaInfIso X U V)

/-- Presheaf pullback with scheme-specific source and target types exposed. -/
def presheafPullback (X Y : Scheme.{u}) (p : X ⟶ Y) :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pullback p.toRingCatSheafHom.hom

/-- Presheaf pushforward with scheme-specific source and target types exposed. -/
def presheafPushforward (X Y : Scheme.{u}) (p : X ⟶ Y) :
    X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward p.toRingCatSheafHom.hom

/-- The actual presheaf pullback/pushforward adjunction, with its scheme types exposed. -/
def presheafAdjunction (X Y : Scheme.{u}) (p : X ⟶ Y) :
    presheafPullback X Y p ⊣ presheafPushforward X Y p :=
  PresheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom.hom

/-- Pullback of a free represented module presheaf, from the two representing
universal properties of the pullback adjunction. -/
def presheafPullbackFreeYonedaIso (X Y : Scheme.{u}) (p : X ⟶ Y) (U : Y.Opens) :
    (presheafPullback X Y p).obj
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) ≅
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U)) :=
  ((PresheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom.hom).corepresentableBy _).uniqueUpToIso (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      p.toRingCatSheafHom.hom U)

/-- Colimit-preserving transformations of module presheaves are isomorphisms
once they are isomorphisms on the free represented generators. -/
theorem presheaf_natTrans_isIso (X : Scheme.{u}) {D : Type*} [Category* D]
    {F G : X.PresheafOfModules ⥤ D}
    [Limits.PreservesColimitsOfSize.{u,u} F] [Limits.PreservesColimitsOfSize.{u,u} G]
    (α : F ⟶ G)
    (h : ∀ U : X.Opens,
      IsIso (α.app ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))))
    (M : X.PresheafOfModules) : IsIso (α.app M) := by
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

/-- The ordinary sectionwise tensor pairing for pushforward of module presheaves. -/
def presheafPushforwardTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : X.PresheafOfModules) :
    (presheafPushforward X Y p).obj M ⊗
      (presheafPushforward X Y p).obj N ⟶
    (presheafPushforward X Y p).obj (M ⊗ N) where
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

/-- The tensor comparison of presheaf pullback, adjoint to the pure-section pairing. -/
def presheafPullbackTensorMap (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : Y.PresheafOfModules) :
    (presheafPullback X Y p).obj (M ⊗ N) ⟶
      (presheafPullback X Y p).obj M ⊗
        (presheafPullback X Y p).obj N :=
  let adj := presheafAdjunction X Y p
  (adj.homEquiv _ _).symm ((adj.unit.app M ⊗ₘ adj.unit.app N) ≫
    presheafPushforwardTensorMap X Y p _ _)

theorem presheafPullbackTensorMap_homEquiv (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : Y.PresheafOfModules) :
    (presheafAdjunction X Y p).homEquiv _ _ (presheafPullbackTensorMap X Y p M N) =
      ((presheafAdjunction X Y p).unit.app M ⊗ₘ (presheafAdjunction X Y p).unit.app N) ≫
        presheafPushforwardTensorMap X Y p _ _ :=
  ((presheafAdjunction X Y p).homEquiv _ _).apply_symm_apply _

/-- Naturality of the sectionwise pushforward tensor pairing. -/
theorem presheafPushforwardTensorMap_naturality (X Y : Scheme.{u}) (p : X ⟶ Y)
    {M M' N N' : X.PresheafOfModules} (f : M ⟶ M') (g : N ⟶ N') :
    ((presheafPushforward X Y p).map f ⊗ₘ
      (presheafPushforward X Y p).map g) ≫
        presheafPushforwardTensorMap X Y p M' N' =
    presheafPushforwardTensorMap X Y p M N ≫
      (presheafPushforward X Y p).map (f ⊗ₘ g) := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intros
  rfl

/-- Naturality of the adjoint presheaf tensor comparison in both factors. -/
theorem presheafPullbackTensorMap_naturality (X Y : Scheme.{u}) (p : X ⟶ Y)
    {M M' N N' : Y.PresheafOfModules} (f : M ⟶ M') (g : N ⟶ N') :
    (presheafPullback X Y p).map (f ⊗ₘ g) ≫
      presheafPullbackTensorMap X Y p M' N' =
    presheafPullbackTensorMap X Y p M N ≫
      ((presheafPullback X Y p).map f ⊗ₘ
        (presheafPullback X Y p).map g) := by
  let adj := presheafAdjunction X Y p
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rw [presheafPullbackTensorMap_homEquiv, presheafPullbackTensorMap_homEquiv]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  erw [adj.unit.naturality f, adj.unit.naturality g]
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  simp only [Functor.comp_map]
  rw [presheafPushforwardTensorMap_naturality, Category.assoc]

/-- The free represented comparison is characterized by the distinguished generator. -/
theorem presheafPullbackFreeYonedaIso_unit (X Y : Scheme.{u}) (p : X ⟶ Y) (U : Y.Opens) :
    (presheafAdjunction X Y p).unit.app
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) ≫
        (presheafPushforward X Y p).map (presheafPullbackFreeYonedaIso X Y p U).hom =
    (PresheafOfModules.freeYonedaEquiv
      (M := (presheafPushforward X Y p).obj
        ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (p ⁻¹ᵁ U))))).symm
      (ModuleCat.freeMk (𝟙 (p ⁻¹ᵁ U))) := by
  change (presheafAdjunction X Y p).homEquiv _ _
    (presheafPullbackFreeYonedaIso X Y p U).hom = _
  simp only [presheafPullbackFreeYonedaIso, Functor.CorepresentableBy.uniqueUpToIso_hom]
  change (presheafAdjunction X Y p).homEquiv _ _
    (((presheafAdjunction X Y p).homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Evaluation of the free represented universal property on any generator. -/
theorem freeYonedaEquiv_symm_apply (X : Scheme.{u}) (M : X.PresheafOfModules)
    (U V : X.Opens) (i : V ⟶ U) (m : M.obj (op U)) :
    ((PresheafOfModules.freeYonedaEquiv (M := M)).symm m).app (op V)
      (ModuleCat.freeMk i) = M.map i.op m := by
  simp [PresheafOfModules.freeYonedaEquiv, PresheafOfModules.freeHomEquiv, yonedaEquiv]
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Restriction of a free presheaf generator. -/
theorem freePresheaf_map_freeMk (X : Scheme.{u}) (F : X.Opensᵒᵖ ⥤ Type u)
    {U V : X.Opensᵒᵖ} (a : U ⟶ V) (m : F.obj U) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj F).map a (ModuleCat.freeMk m) =
      ModuleCat.freeMk (F.map a m) := by
  exact ModuleCat.freeDesc_apply _ _

/-- The generator formula for pullback of a free represented presheaf. -/
theorem presheafPullbackFreeYonedaIso_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (U V : Y.Opens) (i : V ⟶ U) :
    (presheafPullbackFreeYonedaIso X Y p U).hom.app (op (p ⁻¹ᵁ V))
      (((presheafAdjunction X Y p).unit.app
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

/-- Tensor of two represented generators is the generator on the intersection. -/
theorem freeYonedaTensorIso_hom_apply (X : Scheme.{u}) (U V W : X.Opens)
    (i : W ⟶ U) (j : W ⟶ V) :
    (freeYonedaTensorIso X U V).hom.app (op W)
      (ModuleCat.freeMk i ⊗ₜ[Γ(X, W)] ModuleCat.freeMk j) =
    ModuleCat.freeMk (homOfLE (le_inf (leOfHom i) (leOfHom j))) := by
  change (ModuleCat.free (Γ(X, W))).map ((yonedaInfIso X U V).hom.app (op W))
    ((ModuleCat.FreeMonoidal.μIso (Γ(X, W)) _ _).hom
      (ModuleCat.freeMk i ⊗ₜ[Γ(X, W)] ModuleCat.freeMk j)) = _
  rw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk, ModuleCat.free_map_apply]
  rfl

/-- Inverse generator formula for the represented tensor isomorphism. -/
theorem freeYonedaTensorIso_inv_apply (X : Scheme.{u}) (U V W : X.Opens)
    (i : W ⟶ U ⊓ V) :
    (freeYonedaTensorIso X U V).inv.app (op W) (ModuleCat.freeMk i) =
      ModuleCat.freeMk (homOfLE ((leOfHom i).trans inf_le_left)) ⊗ₜ[Γ(X, W)]
        ModuleCat.freeMk (homOfLE ((leOfHom i).trans inf_le_right)) := by
  change (ModuleCat.FreeMonoidal.μIso (Γ(X, W)) _ _).inv
    ((ModuleCat.free (Γ(X, W))).map ((yonedaInfIso X U V).inv.app (op W))
      (ModuleCat.freeMk i)) = _
  rw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.μIso_inv_freeMk]
  rfl

/-- The actual presheaf comparison has the expected pure-section equation. -/
theorem presheafPullbackTensorMap_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : Y.PresheafOfModules) (U : Y.Opens) (m : M.obj (op U)) (n : N.obj (op U)) :
    (presheafPullbackTensorMap X Y p M N).app (op (p ⁻¹ᵁ U))
      (((presheafAdjunction X Y p).unit.app (M ⊗ N)).app (op U) (m ⊗ₜ[Γ(Y, U)] n)) =
    (show ((presheafPullback X Y p).obj M).obj (op (p ⁻¹ᵁ U)) from
      ((presheafAdjunction X Y p).unit.app M).app (op U) m) ⊗ₜ[Γ(X, p ⁻¹ᵁ U)]
    (show ((presheafPullback X Y p).obj N).obj (op (p ⁻¹ᵁ U)) from
      ((presheafAdjunction X Y p).unit.app N).app (op U) n) := by
  have h := congrArg (fun k ↦ k.app (op U)) (presheafPullbackTensorMap_homEquiv X Y p M N)
  have h' := ConcreteCategory.congr_hom h (m ⊗ₜ[Γ(Y, U)] n)
  exact h'

/-- On free represented generators the canonical comparison is an isomorphism,
since preimages commute with intersections of opens. -/
theorem presheafPullbackTensorMap_free_isIso (X Y : Scheme.{u}) (p : X ⟶ Y)
    (U V : Y.Opens) :
    IsIso (presheafPullbackTensorMap X Y p
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U))
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V))) := by
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

/-- Tensor comparison as a natural transformation in the second factor. -/
def presheafPullbackTensorRight (X Y : Scheme.{u}) (p : X ⟶ Y) (M : Y.PresheafOfModules) :
    tensorLeft M ⋙ presheafPullback X Y p ⟶
      presheafPullback X Y p ⋙ tensorLeft ((presheafPullback X Y p).obj M) where
  app N := presheafPullbackTensorMap X Y p M N
  naturality {N N'} f := by
    have h := presheafPullbackTensorMap_naturality X Y p (𝟙 M) f
    rw [(presheafPullback X Y p).map_id] at h
    rw [id_tensorHom, id_tensorHom] at h
    exact h

/-- Tensor comparison as a natural transformation in the first factor. -/
def presheafPullbackTensorLeft (X Y : Scheme.{u}) (p : X ⟶ Y) (N : Y.PresheafOfModules) :
    tensorRight N ⋙ presheafPullback X Y p ⟶
      presheafPullback X Y p ⋙ tensorRight ((presheafPullback X Y p).obj N) where
  app M := presheafPullbackTensorMap X Y p M N
  naturality {M M'} f := by
    have h := presheafPullbackTensorMap_naturality X Y p f (𝟙 N)
    rw [(presheafPullback X Y p).map_id] at h
    rw [tensorHom_id, tensorHom_id] at h
    exact h

local instance tensorLeftPreserves (X : Scheme.{u}) (M : X.PresheafOfModules) :
    Limits.PreservesColimitsOfSize.{u,u} (tensorLeft M) := by
  change Limits.PreservesColimitsOfSize.{u,u}
    (tensorLeft (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M)
  infer_instance

local instance tensorRightPreserves (X : Scheme.{u}) (M : X.PresheafOfModules) :
    Limits.PreservesColimitsOfSize.{u,u} (tensorRight M) := by
  change Limits.PreservesColimitsOfSize.{u,u}
    (tensorRight (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M)
  infer_instance

/-- Arbitrary presheaf pullback commutes with tensor, by free presentations and
preservation of colimits in each variable. -/
theorem presheafPullbackTensorMap_isIso (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M N : Y.PresheafOfModules) : IsIso (presheafPullbackTensorMap X Y p M N) := by
  have : (presheafPullback X Y p).IsLeftAdjoint := (presheafAdjunction X Y p).isLeftAdjoint
  have hfree (U : Y.Opens) (Q : Y.PresheafOfModules) :
      IsIso (presheafPullbackTensorMap X Y p
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)) Q) := by
    exact presheaf_natTrans_isIso Y
      (presheafPullbackTensorRight X Y p
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj U)))
      (fun V ↦ presheafPullbackTensorMap_free_isIso X Y p U V) Q
  exact presheaf_natTrans_isIso Y (presheafPullbackTensorLeft X Y p N) (fun U ↦ hfree U N) M

/-- The canonical tensor comparison for actual module presheaves. -/
def presheafPullbackTensorIso (X Y : Scheme.{u}) (p : X ⟶ Y) (M N : Y.PresheafOfModules) :
    (presheafPullback X Y p).obj (M ⊗ N) ≅
      (presheafPullback X Y p).obj M ⊗ (presheafPullback X Y p).obj N := by
  haveI := presheafPullbackTensorMap_isIso X Y p M N
  exact asIso (presheafPullbackTensorMap X Y p M N)

/-- Canonical pullback comparison for genuine sheaf tensors. The construction uses
commutation of pullback with sheafification, the colimit-preserving presheaf comparison,
and descent of tensor pairings through sheafification. -/
def pullback_sheafTensor_iso (X Y : Scheme.{u}) (p : X ⟶ Y) (H K : Y.Modules) :
    (Scheme.Modules.pullback p).obj (sheafTensor Y H K) ≅
      sheafTensor X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K) :=
  (SheafOfModules.sheafificationCompPullback p.toRingCatSheafHom).app (tensorPresheaf Y H K) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (presheafPullbackTensorIso X Y p H.val K.val) ≪≫
    sheafificationTensorIso X ((presheafPullback X Y p).obj H.val)
      ((presheafPullback X Y p).obj K.val) ≪≫
    sheafTensorCongr X ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm

/-- Recursive comparison for every genuine tensor power, including the structure
sheaf at exponent zero. -/
def pullback_tensorPower_iso (X Y : Scheme.{u}) (p : X ⟶ Y) (H : Y.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅
      tensorPower X ((Scheme.Modules.pullback p).obj H) n
  | 0 => pullback_unit_iso X Y p
  | n + 1 => pullback_sheafTensor_iso X Y p (tensorPower Y H n) H ≪≫
      sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)

end ArithmeticThetaPullback
