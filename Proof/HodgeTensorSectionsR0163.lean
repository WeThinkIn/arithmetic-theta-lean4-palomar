module

public import HodgeInitialDefinitionsR0163
public import Mathlib.LinearAlgebra.TensorPower.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open scoped TensorProduct
namespace ArithmeticThetaHodgeInitialR0163
namespace HodgeTensorSections
attribute [local instance] sectionModule

private theorem cover_top (K : Type u) [Field K]
    (S : Sieve (⊤ : (Spec (CommRingCat.of K)).Opens))
    (hS : S ∈ Opens.grothendieckTopology (Spec (CommRingCat.of K)) ⊤) :
    S (𝟙 _) := by
  obtain ⟨V, f, hf, hx⟩ := hS (IsLocalRing.closedPoint K) (by trivial)
  have hV : V = ⊤ := by
    apply top_unique
    intro y _
    exact Subsingleton.elim (IsLocalRing.closedPoint K) y ▸ hx
  subst V
  rwa [show f = 𝟙 _ from Subsingleton.elim _ _] at hf

private theorem binary_bijective (K : Type u) [Field K]
    (F G : (Spec (CommRingCat.of K)).Modules) :
    Function.Bijective ((tensorUnitMap (Spec (CommRingCat.of K)) F G).app (op ⊤)) := by
  let X := Spec (CommRingCat.of K)
  let P := (tensorPresheaf X F G).presheaf
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P
  constructor
  · intro x y h
    have hc := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) η x y h
    have ht := cover_top K _ hc
    simpa [Presheaf.equalizerSieve] using ht
  · intro y
    have hc := Presheaf.imageSieve_mem (Opens.grothendieckTopology X) η y
    have ht := cover_top K _ hc
    obtain ⟨t, ht⟩ := ht
    refine ⟨t, ?_⟩
    change η.app (op ⊤) t = y
    simpa using ht

private abbrev scalarIso (K : Type u) [Field K] :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm

private instance scalarInvPair (K : Type u) [Field K] :
    RingHomInvPair (scalarIso K).toRingHom (scalarIso K).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (scalarIso K)

private instance scalarInvPairSymm (K : Type u) [Field K] :
    RingHomInvPair (scalarIso K).symm.toRingHom (scalarIso K).toRingHom :=
  RingHomInvPair.of_ringEquiv (scalarIso K).symm

private def scalarIdentity (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) :
    Γ(F, ⊤) ≃ₛₗ[(scalarIso K).toRingHom] Γ(F, ⊤) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def binaryEquiv (K : Type u) [Field K]
    (F G : (Spec (CommRingCat.of K)).Modules) :
    Γ(F, ⊤) ⊗[K] Γ(G, ⊤) ≃ₗ[K] Γ(sheafTensor (Spec (CommRingCat.of K)) F G, ⊤) := by
  let e := TensorProduct.congr (scalarIdentity K F) (scalarIdentity K G)
  let f := LinearEquiv.ofBijective
    ((tensorUnitMap (Spec (CommRingCat.of K)) F G).app (op ⊤)).hom
    (binary_bijective K F G)
  exact
    { toFun := fun x => f (e x)
      invFun := fun y => e.symm (f.symm y)
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change f (e (c • x)) = (scalarIso K c) • f (e x)
        rw [e.map_smulₛₗ, f.map_smul]
        rfl }

private theorem binaryEquiv_tmul (K : Type u) [Field K]
    (F G : (Spec (CommRingCat.of K)).Modules) (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    binaryEquiv K F G (x ⊗ₜ[K] y) =
      tensorSection (Spec (CommRingCat.of K)) F G ⊤ x y := rfl

private def zeroEquiv (K : Type u) [Field K] :
    K ≃ₗ[K] Γ(SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf, ⊤) where
  toFun := scalarIso K
  invFun := (scalarIso K).symm
  left_inv := (scalarIso K).left_inv
  right_inv := (scalarIso K).right_inv
  map_add' := (scalarIso K).map_add
  map_smul' c x := (scalarIso K).map_mul c x

private def splitLast (K : Type u) [Field K] (M : Type u) [AddCommGroup M]
    [Module K M] (n : ℕ) :
    PiTensorProduct K (fun _ : Fin (n+1) => M) ≃ₗ[K]
      (PiTensorProduct K (fun _ : Fin n => M)) ⊗[K] M :=
  TensorPower.mulEquiv.symm.trans
    (TensorProduct.congr (LinearEquiv.refl K _) (PiTensorProduct.subsingletonEquiv (0 : Fin 1)))

private theorem splitLast_tprod (K : Type u) [Field K] (M : Type u) [AddCommGroup M]
    [Module K M] (n : ℕ) (x : Fin (n+1) → M) :
    splitLast K M n (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K (fun i => x i.castSucc) ⊗ₜ[K] x (Fin.last n) := by
  have hm : (TensorPower.mulEquiv :
      (PiTensorProduct K (fun _ : Fin n => M)) ⊗[K]
        (PiTensorProduct K (fun _ : Fin 1 => M)) ≃ₗ[K] _)
      ((PiTensorProduct.tprod K (fun i => x i.castSucc)) ⊗ₜ[K]
        PiTensorProduct.tprod K (fun _ => x (Fin.last n))) = PiTensorProduct.tprod K x := by
    rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod,
      Fin.append_right_eq_snoc]
    congr 1
    exact Fin.snoc_init_self x
  simp only [splitLast, LinearEquiv.trans_apply, ← hm, LinearEquiv.symm_apply_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

private def comparison (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) :
    (n : ℕ) → SectionTensor K F n ≃ₗ[K]
      Γ(tensorPower (Spec (CommRingCat.of K)) F n, ⊤)
  | 0 => (PiTensorProduct.isEmptyEquiv (Fin 0)).trans (zeroEquiv K)
  | n+1 => (splitLast K Γ(F, ⊤) n).trans
      ((TensorProduct.congr (comparison K F n) (LinearEquiv.refl K _)).trans
        (binaryEquiv K (tensorPower (Spec (CommRingCat.of K)) F n) F))

private theorem comparison_tprod (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) (n : ℕ) :
    IsTensorSections K F n (comparison K F n) := by
  intro x
  induction n with
  | zero =>
    change zeroEquiv K (PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.tprod K x)) =
      (1 : Γ(Spec (CommRingCat.of K), ⊤))
    rw [PiTensorProduct.isEmptyEquiv_apply_tprod]
    exact (scalarIso K).map_one
  | succ n ih =>
    simp only [comparison, LinearEquiv.trans_apply, splitLast_tprod,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    change tensorSection _ _ _ _ (comparison K F n
      (PiTensorProduct.tprod K (fun i => x i.castSucc))) (x (Fin.last n)) = _
    rw [ih]
    rfl

end HodgeTensorSections

attribute [local instance] sectionModule

/-- The unique comparison between the tensor of global sections and global
sections of the genuine sheaf tensor power, with the ordered representative formula. -/
theorem hodge_tensor_sections (K : Type u) [Field K]
    (F : (AlgebraicGeometry.Spec (CommRingCat.of K)).Modules) (n : ℕ) :
    ArithmeticThetaHodgeInitialR0163.TensorSections K F n := by
  refine ⟨HodgeTensorSections.comparison K F n,
    HodgeTensorSections.comparison_tprod K F n, ?_⟩
  intro e he
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  ext x
  exact (he x).trans (HodgeTensorSections.comparison_tprod K F n x).symm

end ArithmeticThetaHodgeInitialR0163
