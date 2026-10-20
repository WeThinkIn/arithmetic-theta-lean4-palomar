module

public import RelativeDoubledTorsionThetaLiftPreludeR0255
import all RelativeDoubledTorsionThetaLiftPreludeR0255

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true
noncomputable section
universe u v
attribute [local instance] AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.OModulePresheaf.module
open _root_.AlgebraicGeometry
set_option maxErrors 15

/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover


private theorem AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) (i' : Xk' ⟶ X')
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U)
    (U' : X'.Opens) (hU' : U' ≤ h ⁻¹ᵁ U) (W' : Xk'.Opens) (hW' : W' ≤ i' ⁻¹ᵁ U') (hWk : W' ≤ hk ⁻¹ᵁ W)
    (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').obj W')
    (hw' : ∀ ξ : Module.Dual k V, w' ξ = (hk.appLE W W' hWk).hom (w ξ))
    (hw : IsFibreReading V ι f fk i U W hW δ w) :
    IsFibreReading V ι f' fk' i' U' W' hW' ((h.appLE U U' hU').hom δ) w' := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"


namespace T3D4

variable {k : Type u} [Field k] {Xk Xk' : Scheme.{u}}
  {fk : Xk ⟶ Spec (CommRingCat.of k)} {fk' : Xk' ⟶ Spec (CommRingCat.of k)}

theorem unitPullback_add (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z z' : (OModulePresheaf.unit fk).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n (z + z') =
      OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z +
        OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z' := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · simp only [OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.add_apply]
    change ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom ((show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z _) + (show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z' _)) =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) • (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z _) +
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) • (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z' _)
    rw [map_add, smul_add]
  · simp only [OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.add_apply, add_zero]

theorem unitPullback_smul (hk : Xk' ⟶ Xk) (hfk : hk ≫ fk = fk') (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : k)
    (z : (OModulePresheaf.unit fk).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n (c • z) =
      c • OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · simp only [OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.smul_apply]
    letI := algebraOfHom fk (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))
    letI := algebraOfHom fk' (𝒲.inter s)
    have hcomp : (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (algebraMap k _ c) = algebraMap k _ c := by
      show (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
          ((fk.appLE ⊤ _ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
        (fk'.appLE ⊤ _ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
        (Scheme.Hom.appLE_comp_appLE hk fk ⊤ (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) le_top
          (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this]; subst hfk; rfl
    change ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (algebraMap k _ c * (show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z _)) =
      algebraMap k _ c * (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z _))
    rw [map_mul, hcomp, mul_smul_comm]
  · simp only [OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.smul_apply, smul_zero]

noncomputable def unitPullbackLin (hk : Xk' ⟶ Xk) (hfk : hk ≫ fk = fk') (𝒲 : Xk'.OrderedAffineCover)
    (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    (OModulePresheaf.unit fk).cochain 𝒦 n →ₗ[k] (OModulePresheaf.unit fk').cochain 𝒲 n where
  toFun := OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n
  map_add' := unitPullback_add hk 𝒲 𝒦 lam hlam n
  map_smul' := unitPullback_smul hk hfk 𝒲 𝒦 lam hlam n

theorem sort_pair_eq_swap {ι : Type u} [LinearOrder ι] (f : Fin 2 → ι) (h : f 1 < f 0) : Tuple.sort f = Equiv.swap 0 1 := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · exact le_rfl
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]; exact h.le
    · exact absurd hxy (by decide)
    · exact le_rfl
  · intro x y hxy hfe
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hfe; exact absurd hfe h.ne
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)

theorem injective_pair {ι : Type u} (f : Fin 2 → ι) (h : f 0 ≠ f 1) : Function.Injective f := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd hxy h
  · exact absurd hxy.symm h
  · rfl

theorem monotone_pair {ι : Type u} [Preorder ι] (f : Fin 2 → ι) (h : f 0 ≤ f 1) : Monotone f := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · exact le_rfl
  · exact h
  · exact absurd hxy (by decide)
  · exact le_rfl

theorem unitPullback_one_of_lt (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit fk).cochain 𝒦 1) (s : 𝒲.Idx 1)
    (hinj : Function.Injective (lam ∘ s.1)) (hlt : lam (s.1 0) < lam (s.1 1)) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam 1 z s =
      (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj)) := by
  have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (monotone_pair _ hlt.le)
  rw [OModulePresheaf.unitPullback_apply_of_injective hk 𝒲 𝒦 lam hlam 1 z s hinj, hsort, Equiv.Perm.sign_refl, Units.val_one,
    one_smul]
  rfl

theorem unitPullback_one_of_gt (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit fk).cochain 𝒦 1) (s : 𝒲.Idx 1)
    (hinj : Function.Injective (lam ∘ s.1)) (hgt : lam (s.1 1) < lam (s.1 0)) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam 1 z s =
      -(hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj)) := by
  have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_pair_eq_swap _ hgt
  rw [OModulePresheaf.unitPullback_apply_of_injective hk 𝒲 𝒦 lam hlam 1 z s hinj, hsort,
    Equiv.Perm.sign_swap (by decide), Units.val_neg, Units.val_one, neg_smul, one_smul]
  rfl

theorem mul_self_eq_zero_of_isFibreReading {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁) (hJ : ∀ v w : V, ι v * ι w = 0)
    {X Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W) (hw : IsFibreReading V ι f fk i U W hW δ w) :
    δ * δ = 0 := by
  letI := algebraOfHom f U
  obtain ⟨n, v, s, hδ, -⟩ := hw
  rw [← hδ, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  rw [mul_mul_mul_comm, ← map_mul, hJ, map_zero, zero_mul]

end T3D4

open T3D4 in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    {X X' X₀ X₀' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) [IsAffineHom i] (i' : Xk' ⟶ X') [IsAffineHom i']
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (hlamk : ∀ w, (𝒲.comap i').U w ≤ hk ⁻¹ᵁ (𝒰.comap i).U (lam w))
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    ∃ w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1,
      (∀ ξ : Module.Dual k V,
        w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ)) ∧
      IsPicDeformationCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀)
        w' := by
  classical
  obtain ⟨τ, e, e', hee', hdisc, hread⟩ := hw
  obtain ⟨τ', hτ'chart, hT0, hTplus, hTminus⟩ := AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq h 𝒰 𝒲 lam hlam M τ

  let w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1 :=
    (unitPullbackLin hk hfk (𝒲.comap i') (𝒰.comap i) lam hlamk 1).comp w
  have hw'eq : ∀ ξ, w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) :=
    fun ξ => rfl
  refine ⟨w', hw'eq, ?_⟩

  let E : ∀ a : 𝒲.ι, Γ(X', 𝒲.U a) := fun a => (h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)).hom (e (lam a))
  let E' : ∀ a : 𝒲.ι, Γ(X', 𝒲.U a) := fun a => (h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)).hom (e' (lam a))
  refine ⟨τ', E, E', fun a => by simp only [E, E', ← map_mul, hee', map_one], ?_, ?_⟩
  ·
    intro a
    rw [AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE g g' h h₀ hh₀ 𝒰 𝒲 lam hlam M τ τ' a (hτ'chart a) φ₀, ← hdisc (lam a)]
    show ((h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)) ≫ g'.app (𝒲.U a)).hom (e (lam a)) =
      (g.app (𝒰.U (lam a)) ≫ h₀.appLE _ _ _).hom (e (lam a))
    rw [Scheme.Hom.app_eq_appLE g', Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE g, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (p q : X₀' ⟶ X) (hpq : p = q) (e₁ : g' ⁻¹ᵁ 𝒲.U a ≤ p ⁻¹ᵁ 𝒰.U (lam a))
        (e₂ : g' ⁻¹ᵁ 𝒲.U a ≤ q ⁻¹ᵁ 𝒰.U (lam a)),
        (p.appLE (𝒰.U (lam a)) _ e₁).hom (e (lam a)) = (q.appLE (𝒰.U (lam a)) _ e₂).hom (e (lam a)) := by
      intro p q hpq e₁ e₂; subst hpq; rfl
    exact key _ _ hh₀.symm _ _
  ·
    intro s

    have resE : ∀ (c : 𝒰.ι) (x : Γ(X, 𝒰.U c)) (j : Fin 2) (p : 𝒲.U (s.1 j) ≤ h ⁻¹ᵁ 𝒰.U c),
        (X'.presheaf.map (homOfLE (𝒲.inter_le s j)).op).hom ((h.appLE (𝒰.U c) (𝒲.U (s.1 j)) p).hom x) =
          (h.appLE (𝒰.U c) (𝒲.inter s) ((𝒲.inter_le s j).trans p)).hom x := by
      intro c x j p
      exact congrArg (fun q => q.hom x) (Scheme.Hom.appLE_map h p (homOfLE (𝒲.inter_le s j)).op)

    have keyE : ∀ (c d : 𝒰.ι) (hcd : c = d) (x : ∀ a, Γ(X, 𝒰.U a)) (p : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U c) (q : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U d),
        (h.appLE (𝒰.U c) (𝒲.inter s) p).hom (x c) = (h.appLE (𝒰.U d) (𝒲.inter s) q).hom (x d) := by
      intro c d hcd x p q; subst hcd; rfl
    have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
    rw [resE (lam (s.1 0)) (e' (lam (s.1 0))) 0 (hlam _), resE (lam (s.1 1)) (e (lam (s.1 1))) 1 (hlam _)]
    rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hlt.ne
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (monotone_pair _ hlt.le)
      set σ := 𝒲.sortIdx 𝒰 lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have P : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.inter σ := 𝒲.inter_le_preimage_inter_sortIdx h 𝒰 lam hlam s hinj
      have hread' := AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq V ι f f' fk fk' i i' h hh hk hhk hfk
        (𝒰.inter σ) ((𝒰.comap i).inter σ) (𝒰.comap_inter_le i σ) (𝒲.inter s) P ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s) ((𝒲.comap i').inter_le_preimage_inter_sortIdx hk (𝒰.comap i) lam hlamk s hinj)
        _ ((LinearMap.proj σ).comp w) ((LinearMap.proj s).comp w')
        (fun ξ => unitPullback_one_of_lt hk (𝒲.comap i') (𝒰.comap i) lam hlamk (w ξ) s hinj hlt) (hread σ)
      convert hread' using 2
      rw [hTplus s hinj hlt, map_sub, map_one, map_mul, map_mul]
      change _ = (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) *
        (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le σ 0)).op).hom (e' (σ.1 0))) *
        (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le σ 1)).op).hom (e (σ.1 1))) - 1
      have r0 := congrArg (fun q => q.hom (e' (σ.1 0))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 0)).op)
      have r1 := congrArg (fun q => q.hom (e (σ.1 1))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 1)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at r0 r1
      rw [r0, r1, keyE _ _ hσ0 e' _ ((𝒲.inter_le s 0).trans (hlam _)), keyE _ _ hσ1 e _ ((𝒲.inter_le s 1).trans (hlam _))]
      rfl
    ·
      have hninj : ¬ Function.Injective (lam ∘ s.1) := fun hinj => absurd (hinj heq) (by decide)
      have hzero : (LinearMap.proj s).comp w' = 0 := by
        ext ξ
        show OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s = 0
        exact OModulePresheaf.unitPullback_apply_of_not_injective hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s hninj
      rw [hzero, hT0 s heq, one_mul]
      have hone : (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
          (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) = 1 := by
        rw [keyE _ _ heq.symm e ((𝒲.inter_le s 1).trans (hlam _)) ((𝒲.inter_le s 0).trans (hlam _)), ← map_mul,
          mul_comm, hee', map_one]
      rw [hone, sub_self]
      exact (AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading V ι f' fk' i' (𝒲.inter s) ((𝒲.comap i').inter s) (𝒲.comap_inter_le i' s)).1
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hgt.ne'
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_pair_eq_swap _ hgt
      set σ := 𝒲.sortIdx 𝒰 lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have P : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.inter σ := 𝒲.inter_le_preimage_inter_sortIdx h 𝒰 lam hlam s hinj

      have hread' := AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq V ι f f' fk fk' i i' h hh hk hhk hfk
        (𝒰.inter σ) ((𝒰.comap i).inter σ) (𝒰.comap_inter_le i σ) (𝒲.inter s) P ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s) ((𝒲.comap i').inter_le_preimage_inter_sortIdx hk (𝒰.comap i) lam hlamk s hinj)
        _ ((LinearMap.proj σ).comp w) (-((LinearMap.proj s).comp w'))
        (fun ξ => by
          show -(OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s) = _
          rw [unitPullback_one_of_gt hk (𝒲.comap i') (𝒰.comap i) lam hlamk (w ξ) s hinj hgt]
          exact neg_neg _) (hread σ)
      have hneg := ((AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading V ι f' fk' i' (𝒲.inter s) ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s)).2.2.2.1 _ _ hread')
      rw [neg_neg] at hneg

      have hD2 := mul_self_eq_zero_of_isFibreReading V ι hJ f' fk' i' _ _ _ _ _ hread'
      set D : Γ(X', 𝒲.inter s) := ((h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom
        (τ.transition σ * (X.presheaf.map (homOfLE (𝒰.inter_le σ 0)).op).hom (e' (σ.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le σ 1)).op).hom (e (σ.1 1)) - 1)) with hD
      have r0 := congrArg (fun q => q.hom (e' (σ.1 0))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 0)).op)
      have r1 := congrArg (fun q => q.hom (e (σ.1 1))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 1)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at r0 r1
      have hD' : 1 + D = (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) *
          (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) *
          (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0))) := by
        rw [hD, map_sub, map_one, map_mul, map_mul, r0, r1,
          keyE _ _ hσ0 e' _ ((𝒲.inter_le s 1).trans (hlam _)), keyE _ _ hσ1 e _ ((𝒲.inter_le s 0).trans (hlam _))]
        abel
      have hprod : (1 + (τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1)) *
          (1 + D) = 1 := by
        rw [hD']
        have hT := hTminus s hinj hgt
        have h0 : (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0))) = 1 := by
          rw [← map_mul, mul_comm, hee', map_one]
        have h1 : (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) = 1 := by
          rw [← map_mul, hee', map_one]
        have hT' : τ'.transition s * (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) = 1 := hT
        linear_combination ((h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) * (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) * (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) * (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0)))) * hT' +
          ((h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) * (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0)))) * h1 + h0
      have hinv : (1 + D) * (1 - D) = 1 := by linear_combination (-1 : _) * hD2
      have hδ' : τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1 = -D := by
        linear_combination (1 - D) * hprod + (1 + (τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1)) * hD2
      rw [hδ']
      exact hneg
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback
/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover


private theorem AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    {X X' X₀ X₀' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) [IsAffineHom i] (i' : Xk' ⟶ X') [IsAffineHom i']
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (hlamk : ∀ w, (𝒲.comap i').U w ≤ hk ⁻¹ᵁ (𝒰.comap i).U (lam w))
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    ∃ w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1,
      (∀ ξ : Module.Dual k V,
        w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ)) ∧
      IsPicDeformationCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀)
        w' := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover Opposite TopologicalSpace"


namespace PicDefWD

theorem uAS_conj_homOfLE {Y : Scheme.{u}} {W U : Y.Opens} (h : W ≤ U)
    (lam : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).symm ≪≫
          (Scheme.Modules.pullback (Y.homOfLE h)).mapIso lam ≪≫
          Scheme.Modules.pullbackUnitIso (Y.homOfLE h)) =
      (Y.presheaf.map (homOfLE h).op).hom (Scheme.Modules.unitAutSection U lam) := by
  unfold Scheme.Modules.unitAutSection
  erw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso_hom]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem presheaf_map_map_eq {Z : Scheme.{u}} {A B C : (Z.Opens)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (y : Z.presheaf.obj A) :
    (Z.presheaf.map g).hom ((Z.presheaf.map f).hom y) = (Z.presheaf.map h).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

theorem uAS_conj_morphismRestrict {X X₀ : Scheme.{u}} (g : X₀ ⟶ X) (U : X.Opens)
    (lam : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection (g ⁻¹ᵁ U)
        ((Scheme.Modules.pullbackUnitIso (g ∣_ U)).symm ≪≫
          (Scheme.Modules.pullback (g ∣_ U)).mapIso lam ≪≫
          Scheme.Modules.pullbackUnitIso (g ∣_ U)) =
      (g.app U).hom (Scheme.Modules.unitAutSection U lam) := by
  unfold Scheme.Modules.unitAutSection
  erw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  rw [morphismRestrict_appTop]
  simp only [Scheme.Opens.topIso_hom]
  have nat := congrArg (fun φ => φ.hom ((lam.hom.val.app (op ⊤)).hom (1 : (U : Scheme.{u}).presheaf.obj (op ⊤))))
    (g.naturality (eqToHom U.ι_image_top.symm).op)
  simp only [CommRingCat.comp_apply] at nat ⊢
  erw [nat]
  erw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact presheaf_map_map_eq _ _ _ _

variable {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}

noncomputable def transportR
    (lam : ∀ a : 𝒱.ι, SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) : Scheme.Modules.CechTrivialisation 𝒱 𝓜 :=
  fun a => τ a ≪≫ lam a

theorem transportR_restrict
    (lam : ∀ a : 𝒱.ι, SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (transportR lam τ).restrict h =
      τ.restrict h ≪≫ ((Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (lam a) ≪≫ Scheme.Modules.pullbackUnitIso (Y.homOfLE h)) := by
  apply Iso.ext
  change ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜).inv ≫
      ((Scheme.Modules.pullbackComp (Y.homOfLE h) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (Y.homOfLE h)).map ((τ a).hom ≫ (lam a).hom) ≫
      (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).hom =
    (((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜).inv ≫
      ((Scheme.Modules.pullbackComp (Y.homOfLE h) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (Y.homOfLE h)).map (τ a).hom ≫
      (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).hom) ≫
    (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).inv ≫
      (Scheme.Modules.pullback (Y.homOfLE h)).map (lam a).hom ≫
      (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).hom
  simp

theorem transportR_comap
    (lam : ∀ a : 𝒱.ι, SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsAffineHom g] (a : 𝒱.ι) :
    (transportR lam τ).comap g a =
      τ.comap g a ≪≫ ((Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)).symm ≪≫
        (Scheme.Modules.pullback (g ∣_ 𝒱.U a)).mapIso (lam a) ≪≫ Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)) := by
  apply Iso.ext
  change ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ 𝒱.U a).ι g).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι g (𝒱.U a)).symm).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackComp (g ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (g ∣_ 𝒱.U a)).map ((τ a).hom ≫ (lam a).hom) ≫
      (Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)).hom =
    (((Scheme.Modules.pullbackComp (g ⁻¹ᵁ 𝒱.U a).ι g).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι g (𝒱.U a)).symm).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackComp (g ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (g ∣_ 𝒱.U a)).map (τ a).hom ≫
      (Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)).hom) ≫
    (Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)).inv ≫
      (Scheme.Modules.pullback (g ∣_ 𝒱.U a)).map (lam a).hom ≫
      (Scheme.Modules.pullbackUnitIso (g ∣_ 𝒱.U a)).hom
  simp

theorem conj_symm {Z Z' : Scheme.{u}} (p : Z' ⟶ Z)
    (lam : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ((Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso lam ≪≫
        Scheme.Modules.pullbackUnitIso p).symm =
      (Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso lam.symm ≪≫
        Scheme.Modules.pullbackUnitIso p := by
  apply Iso.ext
  change ((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map lam.inv) ≫
      (Scheme.Modules.pullbackUnitIso p).hom =
    (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map lam.inv ≫
      (Scheme.Modules.pullbackUnitIso p).hom
  simp

theorem uAS_trans' {Z : Scheme.{u}} (W : Z.Opens)
    (e₁ e₂ : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W (e₁ ≪≫ e₂) =
      Scheme.Modules.unitAutSection W e₁ * Scheme.Modules.unitAutSection W e₂ :=
  (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).1 e₁ e₂

theorem uAS_mul_uAS_symm {Z : Scheme.{u}} (W : Z.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W e * Scheme.Modules.unitAutSection W e.symm = 1 := by
  rw [← uAS_trans', Iso.self_symm_id]
  exact (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).2

theorem transportR_transition
    (lam : ∀ a : 𝒱.ι, SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (transportR lam τ).transition s =
      (Y.presheaf.map (homOfLE (𝒱.inter_le s 0)).op).hom
          (Scheme.Modules.unitAutSection (𝒱.U (s.1 0)) (lam (s.1 0)).symm) *
        τ.transition s *
      (Y.presheaf.map (homOfLE (𝒱.inter_le s 1)).op).hom
          (Scheme.Modules.unitAutSection (𝒱.U (s.1 1)) (lam (s.1 1))) := by
  unfold Scheme.Modules.CechTrivialisation.transition
  rw [transportR_restrict, transportR_restrict, ← uAS_conj_homOfLE, ← uAS_conj_homOfLE,
    ← uAS_trans', ← uAS_trans']
  congr 1

theorem transportR_discrepancy
    (lam : ∀ a : 𝒱.ι, SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsAffineHom g] (a : 𝒱.ι)
    (φ₀ : (Scheme.Modules.pullback g).obj 𝓜 ≅ SheafOfModules.unit Y'.ringCatSheaf) :
    Scheme.Modules.unitAutSection (g ⁻¹ᵁ 𝒱.U a)
        (((transportR lam τ).comap g a).symm ≪≫
          (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒱.U a).ι).mapIso φ₀ ≪≫
            Scheme.Modules.pullbackUnitIso (g ⁻¹ᵁ 𝒱.U a).ι) =
      (g.app (𝒱.U a)).hom (Scheme.Modules.unitAutSection (𝒱.U a) (lam a).symm) *
        Scheme.Modules.unitAutSection (g ⁻¹ᵁ 𝒱.U a)
          ((τ.comap g a).symm ≪≫
            (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒱.U a).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso (g ⁻¹ᵁ 𝒱.U a).ι) := by
  rw [transportR_comap, ← uAS_conj_morphismRestrict, ← uAS_trans']
  congr 1

theorem inter_one_eq_inf {Z : Scheme.{u}} (𝒦 : Z.OrderedAffineCover) (s : 𝒦.Idx 1) :
    𝒦.inter s = 𝒦.U (s.1 0) ⊓ 𝒦.U (s.1 1) := by
  apply le_antisymm
  · exact le_inf (𝒦.inter_le s 0) (𝒦.inter_le s 1)
  · refine le_iInf fun j => ?_
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

theorem mul_eq_zero_of_mem_map {T' A : Type u} [CommRing T'] [CommRing A] [Algebra T' A]
    (J : Ideal T') (hJ : J * J = ⊥) {x y : A}
    (hx : x ∈ J.map (algebraMap T' A)) (hy : y ∈ J.map (algebraMap T' A)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, hJ, Ideal.map_bot] at h
  exact h

theorem map_res_mem {T' : Type u} [CommRing T'] {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of T'))
    (J : Ideal T') {U U' : Z.Opens} (h : U' ≤ U) {x : Γ(Z, U)}
    (hx : letI := algebraOfHom p U; x ∈ J.map (algebraMap T' Γ(Z, U))) :
    letI := algebraOfHom p U'
    (Z.presheaf.map (homOfLE h).op).hom x ∈ J.map (algebraMap T' Γ(Z, U')) := by
  letI := algebraOfHom p U
  letI := algebraOfHom p U'
  have hc : (algebraMap T' Γ(Z, U')) = (restrictAlgHom p h).toRingHom.comp (algebraMap T' Γ(Z, U)) :=
    RingHom.ext fun r => ((restrictAlgHom p h).commutes r).symm
  rw [hc, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx

theorem mem_map_of_isFibreReading {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (h : IsFibreReading V ι f fk i U W hW δ w) :
    letI := algebraOfHom f U
    δ ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι) := by
  letI := algebraOfHom f U
  obtain ⟨n, v, s, hs, -⟩ := h
  rw [← hs]
  refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ⟨v j, rfl⟩)

theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type u} [CommRing A] {x y z : A} (hy : x * y = 1) (hz : x * z = 1) :
    y = z := by
  calc y = y * (x * z) := by rw [hz, mul_one]
    _ = (x * y) * z := by ring
    _ = z := by rw [hy, one_mul]

theorem key_identity {A : Type u} [CommRing A] (t ea eb la la' lb lb' ca cb : A)
    (hA : la * la' = 1) (hB : lb * lb' = 1) (hcc : ca * cb = 0)
    (hda : (t * ea * eb - 1) * ca = 0) (hdb : (t * ea * eb - 1) * cb = 0) :
    la' * t * lb * (la * ea * (1 - ca)) * (lb' * eb * (1 + cb)) - 1 =
      (t * ea * eb - 1) + cb + -ca := by
  linear_combination (lb * lb' * (t * ea * eb) * (1 - ca) * (1 + cb)) * hA +
    ((t * ea * eb) * (1 - ca) * (1 + cb)) * hB + hdb - hda - (t * ea * eb) * hcc

section dzero
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {p : Z ⟶ Spec (.of R)}
  (F : OModulePresheaf p) (K : Z.OrderedAffineCover)

theorem res_face_aux (η : ∀ a : K.ι, F.obj (K.U a)) {t : K.Idx 0} {a : K.ι} (h : t.1 0 = a)
    {W : Z.Opens} (hW : W ≤ K.inter t) (hW' : W ≤ K.U a) :
    F.res hW (F.res (K.inter_le t 0) (η (t.1 0))) = F.res hW' (η a) := by
  subst h; rw [F.res_res]

theorem d_zero_apply (η : ∀ a : K.ι, F.obj (K.U a)) (s : K.Idx 1) :
    F.d K 0 (fun t => F.res (K.inter_le t 0) (η (t.1 0))) s =
      F.res (K.inter_le s 1) (η (s.1 1)) + -F.res (K.inter_le s 0) (η (s.1 0)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  have h0 : (K.face s 0).1 0 = s.1 1 := congrArg s.1 (by decide)
  have h1 : (K.face s 1).1 0 = s.1 0 := congrArg s.1 (by decide)
  rw [res_face_aux F K η h0 _ (K.inter_le s 1), res_face_aux F K η h1 _ (K.inter_le s 0)]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]

end dzero

end PicDefWD

open PicDefWD in
theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w w' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) (hw' : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w') :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      w ξ - w' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 0) := by
  classical
  obtain ⟨τ, e, e', h1, h2, h3⟩ := hw
  obtain ⟨τ', f1, f1', h1', h2', h3'⟩ := hw'

  have hJJ : RingHom.ker π * RingHom.ker π = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [pow_two]; exact hJJ⟩
  have hJι : (LinearMap.range ι : Ideal B₁) = RingHom.ker π := by
    rw [hιI, Submodule.restrictScalars_self]

  set lam : ∀ a : 𝒰.ι, SheafOfModules.unit ((𝒰.U a : Scheme.{u})).ringCatSheaf ≅
      SheafOfModules.unit ((𝒰.U a : Scheme.{u})).ringCatSheaf := fun a => (τ a).symm ≪≫ τ' a with hlam
  have hτ' : τ' = transportR lam τ := by
    rw [hlam]; funext a; exact (Iso.self_symm_id_assoc (τ a) (τ' a)).symm
  set l : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => Scheme.Modules.unitAutSection (𝒰.U a) (lam a) with hl
  set l' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => Scheme.Modules.unitAutSection (𝒰.U a) (lam a).symm with hl'
  have hll' : ∀ a, l a * l' a = 1 := fun a => uAS_mul_uAS_symm (𝒰.U a) (lam a)

  have tr' : ∀ s : 𝒰.Idx 1, τ'.transition s =
      (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (l' (s.1 0)) * τ.transition s *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (l (s.1 1)) := fun s =>
    (congrArg (fun t => Scheme.Modules.CechTrivialisation.transition t s) hτ').trans (transportR_transition lam τ s)
  have dc' : ∀ a : 𝒰.ι, (g.app (𝒰.U a)).hom (f1 a) = (g.app (𝒰.U a)).hom (l' a * e a) := by
    intro a
    have hd := (congrArg (fun t => Scheme.Modules.unitAutSection (g ⁻¹ᵁ 𝒰.U a)
      ((Scheme.Modules.CechTrivialisation.comap t g a).symm ≪≫
        (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒰.U a).ι).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso (g ⁻¹ᵁ 𝒰.U a).ι)) hτ').trans (transportR_discrepancy lam τ g a φ₀)
    rw [map_mul, h2 a, h2' a]
    exact hd

  have hker : ∀ a : 𝒰.ι, letI := algebraOfHom f (𝒰.U a)
      RingHom.ker (g.app (𝒰.U a)).hom = (RingHom.ker π).map (algebraMap B₁ Γ(X, 𝒰.U a)) := fun a =>
    (IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen π hπ hnil f f₀ g hg (𝒰.U a)
      (𝒰.isAffineOpen a)).2

  set c : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => l a * e' a * (f1 a - l' a * e a) with hc
  have hcJ : ∀ a : 𝒰.ι, letI := algebraOfHom f (𝒰.U a)
      c a ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, 𝒰.U a)) := by
    intro a
    rw [← hker a, RingHom.mem_ker, hc, map_mul, map_sub, dc' a, sub_self, mul_zero]
  have hcJ' : ∀ a : 𝒰.ι, letI := algebraOfHom f (𝒰.U a)
      c a ∈ Ideal.map (algebraMap B₁ Γ(X, 𝒰.U a)) (LinearMap.range ι) := by
    intro a
    letI := algebraOfHom f (𝒰.U a)
    rw [hJι]; exact hcJ a
  have hJJ' : (LinearMap.range ι : Ideal B₁) * LinearMap.range ι = ⊥ := by rw [hJι]; exact hJJ
  have hcc : ∀ a : 𝒰.ι, c a * c a = 0 := fun a => by
    letI := algebraOfHom f (𝒰.U a)
    exact mul_eq_zero_of_mem_map (LinearMap.range ι) hJJ' (hcJ' a) (hcJ' a)
  have hf1 : ∀ a : 𝒰.ι, f1 a = l' a * e a * (1 + c a) := fun a => by
    rw [hc]
    linear_combination (-(e a * e' a) * (f1 a - l' a * e a)) * hll' a + (-(f1 a - l' a * e a)) * h1 a
  have hf1' : ∀ a : 𝒰.ι, f1' a = l a * e' a * (1 - c a) := fun a =>
    eq_of_mul_eq_one_of_mul_eq_one (h1' a) (by
      rw [hf1]
      linear_combination (e a * e' a * (1 - c a * c a)) * hll' a + (1 - c a * c a) * h1 a - hcc a)

  have key : ∀ s : 𝒰.Idx 1,
      τ'.transition s * (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (f1' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (f1 (s.1 1)) - 1 =
        (τ.transition s * (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (e' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (e (s.1 1)) - 1) +
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (c (s.1 1)) +
          -(X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (c (s.1 0)) := by
    intro s
    letI := algebraOfHom f (𝒰.inter s)
    have hA : (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (l (s.1 0)) *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (l' (s.1 0)) = 1 := by
      rw [← map_mul, hll', map_one]
    have hB : (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (l (s.1 1)) *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (l' (s.1 1)) = 1 := by
      rw [← map_mul, hll', map_one]
    have hca := map_res_mem f (LinearMap.range ι) (𝒰.inter_le s 0) (hcJ' (s.1 0))
    have hcb := map_res_mem f (LinearMap.range ι) (𝒰.inter_le s 1) (hcJ' (s.1 1))
    have hδ := mem_map_of_isFibreReading V ι f fk i _ _ _ _ _ (h3 s)
    rw [tr', hf1, hf1']
    simp only [map_mul, map_sub, map_add, map_one]
    exact key_identity _ _ _ _ _ _ _ _ _ hA hB (mul_eq_zero_of_mem_map _ hJJ' hca hcb)
      (mul_eq_zero_of_mem_map _ hJJ' hδ hca) (mul_eq_zero_of_mem_map _ hJJ' hδ hcb)

  have Hcal := fun (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) =>
    isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading V ι f fk i U W hW
  choose γ hγ using fun a : 𝒰.ι =>
    (Hcal (𝒰.U a) ((𝒰.comap i).U a) le_rfl).2.2.2.2.2 (c a) (hcJ' a)
  have hra : ∀ s : 𝒰.Idx 1, IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
      ((X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (c (s.1 0)))
      (((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 0)).comp (γ (s.1 0))) := fun s =>
    (Hcal _ _ le_rfl).2.2.2.2.1 (c (s.1 0)) (γ (s.1 0)) (𝒰.inter s) ((𝒰.comap i).inter s)
      (𝒰.inter_le s 0) ((𝒰.comap i).inter_le s 0) (𝒰.comap_inter_le i s) (hγ (s.1 0))
  have hrb : ∀ s : 𝒰.Idx 1, IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
      ((X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (c (s.1 1)))
      (((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 1)).comp (γ (s.1 1))) := fun s =>
    (Hcal _ _ le_rfl).2.2.2.2.1 (c (s.1 1)) (γ (s.1 1)) (𝒰.inter s) ((𝒰.comap i).inter s)
      (𝒰.inter_le s 1) ((𝒰.comap i).inter_le s 1) (𝒰.comap_inter_le i s) (hγ (s.1 1))
  have hread' : ∀ s : 𝒰.Idx 1, IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
      ((τ.transition s * (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (e' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (e (s.1 1)) - 1) +
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (c (s.1 1)) +
          -(X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (c (s.1 0)))
      ((LinearMap.proj s).comp w') := fun s => by
    rw [← key s]; exact h3' s
  have haff : ∀ s : 𝒰.Idx 1, IsAffineOpen (𝒰.inter s) := fun s => by
    rw [inter_one_eq_inf]
    exact (IsSeparated.isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen f _ _
      (𝒰.isAffineOpen _) (𝒰.isAffineOpen _)).1
  have heq : ∀ s : 𝒰.Idx 1, (LinearMap.proj s).comp w' =
      (LinearMap.proj s).comp w +
        ((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 1)).comp (γ (s.1 1)) +
        -(((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 0)).comp (γ (s.1 0))) := fun s =>
    IsFibreReading.eq_of_isFibreReading_of_flat V ι hι f fk i hi (𝒰.inter s) (haff s) ((𝒰.comap i).inter s)
      (𝒰.comap_inter_le i s) _ _ _ (hread' s)
      ((Hcal _ _ _).2.1 _ _ _ _ ((Hcal _ _ _).2.1 _ _ _ _ (h3 s) (hrb s)) ((Hcal _ _ _).2.2.2.1 _ _ (hra s)))

  intro ξ
  set γ0 : (OModulePresheaf.unit fk).cochain (𝒰.comap i) 0 := fun t =>
    (OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le t 0) (γ (t.1 0) ξ) with hγ0
  have hd : (OModulePresheaf.unit fk).d (𝒰.comap i) 0 γ0 = w' ξ - w ξ := by
    funext s
    have hs : w' ξ s = w ξ s + (OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 1) (γ (s.1 1) ξ) +
        -((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le s 0) (γ (s.1 0) ξ)) := by
      have h := LinearMap.congr_fun (heq s) ξ
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.proj_apply] at h
      exact h
    rw [hγ0, d_zero_apply (OModulePresheaf.unit fk) (𝒰.comap i) (fun a => γ a ξ) s]
    show _ = w' ξ s - w ξ s
    rw [hs]; abel
  refine ⟨-γ0, ?_⟩
  rw [map_neg, hd, neg_sub]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover


private theorem AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w w' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) (hw' : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w') :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      w ξ - w' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 0) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace PicDefIso

variable {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 𝓜' : Y.Modules}

noncomputable def transport (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    Scheme.Modules.CechTrivialisation 𝒱 𝓜' :=
  fun a => (Scheme.Modules.pullback (𝒱.U a).ι).mapIso e ≪≫ τ a

theorem transport_restrict (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (transport e τ).restrict h = (Scheme.Modules.pullback W.ι).mapIso e ≪≫ τ.restrict h := by
  apply Iso.ext
  simp only [transport, Scheme.Modules.CechTrivialisation.restrict, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map]
  simp

theorem transport_transition (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (transport e τ).transition s = τ.transition s := by
  simp only [Scheme.Modules.CechTrivialisation.transition, transport_restrict]
  congr 1
  apply Iso.ext
  change ((τ.restrict (𝒱.inter_le s 0)).inv ≫ ((Scheme.Modules.pullback (𝒱.inter s).ι).mapIso e).inv) ≫
      ((Scheme.Modules.pullback (𝒱.inter s).ι).mapIso e).hom ≫ (τ.restrict (𝒱.inter_le s 1)).hom =
    (τ.restrict (𝒱.inter_le s 0)).inv ≫ (τ.restrict (𝒱.inter_le s 1)).hom
  simp

theorem transport_comap_hom (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    ((transport e τ).comap h a).hom =
      (Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι).map e.hom ≫ (τ.comap h a).hom := by
  change ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜').hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜').hom ≫
      ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜').inv ≫
      (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map
        (((Scheme.Modules.pullback (𝒱.U a).ι).mapIso e).hom ≫ (τ a).hom) ≫
      (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom =
    (Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι).map e.hom ≫
      ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map (τ a).hom ≫
      (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom
  simp only [Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, NatTrans.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp]
  erw [Category.assoc ((Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map ((Scheme.Modules.pullback (𝒱.U a).ι).map e.hom))
    ((Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map (τ a).hom) (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom]

theorem transport_comap (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    (transport e τ).comap h a =
      (Scheme.Modules.pullback ((𝒱.comap h).U a).ι).mapIso ((Scheme.Modules.pullback h).mapIso e) ≪≫ τ.comap h a :=
  Iso.ext (transport_comap_hom e τ h a)

end PicDefIso

open PicDefIso in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    {M M' : X.Modules} (e : M ≅ M')
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M'
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ φ₀) w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw
  refine ⟨transport e.symm τ, ea, ea', h1, fun a => ?_, fun s => ?_⟩
  · rw [h2 a, transport_comap]
    congr 1
    generalize (Scheme.Modules.pullback g).mapIso e.symm = E
    apply Iso.ext
    change (τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀.hom ≫
        (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom =
      ((τ.comap g a).inv ≫ ((Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso E).inv) ≫
        (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map (E.hom ≫ φ₀.hom) ≫
        (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom
    simp
  · rw [transport_transition]
    exact h3 s
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso
/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    {M M' : X.Modules} (e : M ≅ M')
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M'
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ φ₀) w := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : X.OrderedAffineCover) (h₁ h₂ : X ⟶ X) [IsAffineHom h₁] [IsAffineHom h₂] :
    ∃ (𝒲 : X.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ h₁ ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧ (∀ w, 𝒲.U w ≤ h₂ ⁻¹ᵁ 𝒦.U (lam₂ w)) := by
  classical

  have hsep : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from _ from terminal.hom_ext _ _]; infer_instance
  haveI : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance

  let e := Equiv.refl (𝒦.ι × 𝒦.ι)
  letI : LinearOrder (𝒦.ι × 𝒦.ι) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let 𝒲 : X.OrderedAffineCover :=
    { ι := 𝒦.ι × 𝒦.ι
      U := fun j => h₁ ⁻¹ᵁ 𝒦.U (e j).1 ⊓ h₂ ⁻¹ᵁ 𝒦.U (e j).2
      isAffineOpen := fun j => ((𝒦.isAffineOpen _).preimage h₁).inf ((𝒦.isAffineOpen _).preimage h₂)
      iSup_eq_top := by
        have h1 : (⨆ a, h₁ ⁻¹ᵁ 𝒦.U a) = ⊤ := by rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; rfl
        have h2 : (⨆ b, h₂ ⁻¹ᵁ 𝒦.U b) = ⊤ := by rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; rfl
        have key : (⨆ p : 𝒦.ι × 𝒦.ι, h₁ ⁻¹ᵁ 𝒦.U p.1 ⊓ h₂ ⁻¹ᵁ 𝒦.U p.2) = ⊤ := by
          rw [iSup_prod]
          dsimp only
          rw [show (⨆ i, ⨆ j, h₁ ⁻¹ᵁ 𝒦.U i ⊓ h₂ ⁻¹ᵁ 𝒦.U j) = ⨆ i, (h₁ ⁻¹ᵁ 𝒦.U i ⊓ ⨆ j, h₂ ⁻¹ᵁ 𝒦.U j) from
              iSup_congr fun i => (inf_iSup_eq _ _).symm,
            ← iSup_inf_eq, h1, h2, top_inf_eq]
        rw [← key]
        exact e.iSup_comp (g := fun p : 𝒦.ι × 𝒦.ι => h₁ ⁻¹ᵁ 𝒦.U p.1 ⊓ h₂ ⁻¹ᵁ 𝒦.U p.2) }
  exact ⟨𝒲, fun j => (e j).1, fun j => (e j).2, fun j => inf_le_left, fun j => inf_le_right⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_preimage_preimage_of_isSeparated
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : X.OrderedAffineCover) (h₁ h₂ : X ⟶ X) [IsAffineHom h₁] [IsAffineHom h₂] :
    ∃ (𝒲 : X.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ h₁ ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧ (∀ w, 𝒲.U w ≤ h₂ ⁻¹ᵁ 𝒦.U (lam₂ w)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"


namespace TrivCoverPen

open TopologicalSpace Opposite

noncomputable def restrictTriv {Y : Scheme.{u}} {M : Y.Modules} {V W : Y.Opens} (h : W ≤ V)
    (τ : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit ((V : Scheme.{u})).ringCatSheaf) :
    (Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso τ ≪≫
    Scheme.Modules.pullbackUnitIso (Y.homOfLE h)

theorem isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M : SheafOfModules.{u} Y.ringCatSheaf) :
    Limits.IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf Y.ringCatSheaf).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  have hU : U.unop = ⊥ := by
    ext y; exact (IsEmpty.false y).elim
  have hT := TopCat.Sheaf.isTerminalOfEqEmpty (X := Y.carrier)
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) hU
  exact hT.hom_ext _ _

theorem nonempty_iso_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M N : Y.Modules) : Nonempty (M ≅ N) := by
  let e : @Iso (SheafOfModules.{u} Y.ringCatSheaf) _ M N := (isZero_of_isEmpty M).iso (isZero_of_isEmpty N)
  exact ⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

end TrivCoverPen

theorem solution
    {X X₀ : Scheme.{u}} [CompactSpace X] (g : X₀ ⟶ X) [IsClosedImmersion g]
    (𝓛₀ : X₀.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∃ 𝒰 : X.OrderedAffineCover, Nonempty (Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) := by
  classical
  have htriv := h𝓛₀.exists_trivialization

  have key : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj 𝓛₀ ≅
        SheafOfModules.unit ((g ⁻¹ᵁ U : Scheme.{u})).ringCatSheaf) := by
    intro x
    by_cases hx : x ∈ Set.range g.base
    · obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨V₀, hxV₀, ⟨τ⟩⟩ := htriv x₀
      obtain ⟨V', hV'open, hV'⟩ := g.isClosedEmbedding.isInducing.isOpen_iff.mp V₀.isOpen
      have hxV' : g.base x₀ ∈ V' := by
        rw [← Set.mem_preimage, hV']; exact hxV₀
      obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUV'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV' hV'open
      refine ⟨U, hUaff, hxU, ⟨TrivCoverPen.restrictTriv ?_ τ⟩⟩
      intro y hy
      have hy' : g.base y ∈ V' := hUV' hy
      rw [← Set.mem_preimage, hV'] at hy'
      exact hy'
    · obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUc⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (Set.range g.base)ᶜ from hx) g.isClosedEmbedding.isClosed_range.isOpen_compl
      refine ⟨U, hUaff, hxU, ?_⟩
      have hbot : g ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun y hy => (hUc hy ⟨y, rfl⟩).elim
      by_cases hne : Nonempty X₀
      · obtain ⟨x₁⟩ := hne
        obtain ⟨V₁, -, ⟨τ₁⟩⟩ := htriv x₁
        exact ⟨TrivCoverPen.restrictTriv (show g ⁻¹ᵁ U ≤ V₁ from hbot ▸ bot_le) τ₁⟩
      · haveI : IsEmpty ((g ⁻¹ᵁ U : X₀.Opens) : Scheme.{u}) := ⟨fun y => hne ⟨(g ⁻¹ᵁ U).ι.base y⟩⟩
        exact TrivCoverPen.nonempty_iso_of_isEmpty _ _
  choose U hUaff hxU hτ using key

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  letI : LinearOrder (↥t) := LinearOrder.lift' (Fintype.equivFin (↥t)) (Fintype.equivFin (↥t)).injective
  refine ⟨{ ι := ↥t
            U := fun w => U w.1
            isAffineOpen := fun w => hUaff w.1
            iSup_eq_top := ?_ }, ⟨fun w => (hτ w.1).some⟩⟩
  refine top_le_iff.mp fun y _ => ?_
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hyw⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover


private theorem AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
    {X X₀ : Scheme.{u}} [CompactSpace X] (g : X₀ ⟶ X) [IsClosedImmersion g]
    (𝓛₀ : X₀.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∃ 𝒰 : X.OrderedAffineCover, Nonempty (Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct


theorem solution
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X X' Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πX' : X' ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (g : X' ⟶ X) [IsAffineHom g]
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (hlam' : ∀ w : (𝒲.comap g).ι, (𝒲.comap g).U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒲.comap g).Idx n) :
    (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom
        ((g.app (𝒲.inter s)).hom (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s))
      = OModulePresheaf.unitPullback (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s := by
  classical
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n z s hinj,
      OModulePresheaf.unitPullback_apply_of_injective (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s hinj,
      map_zsmul, map_zsmul]
    congr 1
    have key : h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫
        X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op ≫
          g.app (𝒲.inter s) ≫ X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op =
        h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫ g.app (h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫
          X'.presheaf.map (homOfLE ((𝒲.comap g).inter_le_preimage_inter_sortIdx (g ≫ h) 𝒦 lam hlam' s hinj)).op := by
      congr 1
      rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
      rfl
    have e := congrArg (fun φ => φ.hom (z (𝒲.sortIdx 𝒦 lam s hinj))) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    exact e
  · rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n z s hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s hinj]
    change (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom ((g.app (𝒲.inter s)).hom (0 : Γ(X, 𝒲.inter s))) =
      (0 : Γ(X', (𝒲.comap g).inter s))
    rw [map_zero, map_zero]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct


private theorem AlgebraicGeometry.OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X X' Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πX' : X' ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (g : X' ⟶ X) [IsAffineHom g]
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (hlam' : ∀ w : (𝒲.comap g).ι, (𝒲.comap g).U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒲.comap g).Idx n) :
    (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom
        ((g.app (𝒲.inter s)).hom (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s))
      = OModulePresheaf.unitPullback (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero

set_option autoImplicit false


namespace LamIndepAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

section Sheaf

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) {m : ℕ} (z : (OModulePresheaf.unit πY).cochain 𝒦 m)

noncomputable def pb (T : 𝒦.Idx m) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) : Γ(X, W) :=
  (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter T)).hom (z T))

theorem map_pb (T : 𝒦.Idx m) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ 𝒦.inter T) :
    (X.presheaf.map (homOfLE hW').op).hom (pb h 𝒦 z T W hW) = pb h 𝒦 z T W' hW'' := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem pb_congr {T T' : 𝒦.Idx m} (e : T = T') (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W ≤ h ⁻¹ᵁ 𝒦.inter T') :
    pb h 𝒦 z T W hW = pb h 𝒦 z T' W hW' := by
  subst e; rfl

theorem map_app_map_eq_pb (S : 𝒦.Idx (m + 1)) (i : Fin (m + 2)) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter S) :
    (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter S)).hom
      ((Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face S i)).op).hom (z (𝒦.face S i)))) =
      pb h 𝒦 z (𝒦.face S i) W (hW.trans (h.preimage_mono (𝒦.inter_le_inter_face S i))) := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality_assoc, ← X.presheaf.map_comp,
    ← CommRingCat.comp_apply]
  rfl

end Sheaf

section Pairs

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)

def pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exact hij)⟩

theorem pair_val {i j : 𝒦.ι} (hij : i < j) : (pair 𝒦 hij).1 = ![i, j] := rfl

theorem inf_le_inter_pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.U i ⊓ 𝒦.U j ≤ 𝒦.inter (pair 𝒦 hij) :=
  le_iInf fun k => by fin_cases k; exacts [inf_le_left, inf_le_right]

def triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.Idx 2 :=
  ⟨![a, b, c], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exacts [hab, hbc])⟩

theorem inf_le_inter_triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c ≤ 𝒦.inter (triple 𝒦 hab hbc) :=
  le_iInf fun k => by
    fin_cases k
    exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]

theorem face_triple_zero {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 0 = pair 𝒦 hbc := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_one {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 1 = pair 𝒦 (hab.trans hbc) := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_two {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 2 = pair 𝒦 hab := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

noncomputable def P {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) :=
  pb h 𝒦 z (pair 𝒦 hij) W (hW.trans (h.preimage_mono (inf_le_inter_pair 𝒦 hij)))

theorem map_P {i j : 𝒦.ι} (hij : i < j) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W)
    (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (P h 𝒦 z hij W hW) = P h 𝒦 z hij W' hW'' :=
  map_pb h 𝒦 z _ _ hW' _

theorem P_add_P (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c)
    (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c)) :
    P h 𝒦 z hab W (hW.trans (h.preimage_mono inf_le_left)) + P h 𝒦 z hbc W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      P h 𝒦 z (hab.trans hbc) W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by
  have hle : W ≤ h ⁻¹ᵁ 𝒦.inter (triple 𝒦 hab hbc) := hW.trans (h.preimage_mono (inf_le_inter_triple 𝒦 hab hbc))
  have hd := congrFun hz (triple 𝒦 hab hbc)
  rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_three] at hd
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_zsmul, neg_one_zsmul] at hd
  change (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 0)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 0)) +
        -(Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 1)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 1)) +
        (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 2)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 2))
      = (0 : Γ(Y, 𝒦.inter (triple 𝒦 hab hbc))) at hd
  have hd' := congrArg (fun y => (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter (triple 𝒦 hab hbc))).hom y)) hd
  simp only [map_add, map_neg, map_zero] at hd'
  rw [map_app_map_eq_pb, map_app_map_eq_pb, map_app_map_eq_pb,
    pb_congr h 𝒦 z (face_triple_zero 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hbc))),
    pb_congr h 𝒦 z (face_triple_one 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 (hab.trans hbc)))),
    pb_congr h 𝒦 z (face_triple_two 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono inf_le_left)).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hab)))] at hd'
  unfold P
  linear_combination hd'

noncomputable def Z (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) := by
  classical
  exact if hij : i < j then P h 𝒦 z hij W hW
    else if hji : j < i then -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _))))
    else 0

theorem Z_of_lt {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = P h 𝒦 z hij W hW := by
  classical
  simp only [Z, dif_pos hij]

theorem Z_of_gt {i j : 𝒦.ι} (hji : j < i) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _)))) := by
  classical
  simp only [Z, dif_neg (not_lt_of_gt hji), dif_pos hji]

theorem Z_self (i : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U i)) : Z h 𝒦 z i i W hW = 0 := by
  classical
  simp only [Z, dif_neg (lt_irrefl i)]

theorem Z_of_eq {i j : 𝒦.ι} (e : i = j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Z h 𝒦 z i j W hW = 0 := by
  subst e; exact Z_self h 𝒦 z i W hW

theorem map_Z (i j : 𝒦.ι) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (Z h 𝒦 z i j W hW) = Z h 𝒦 z i j W' hW'' := by
  classical
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_lt h 𝒦 z hij, map_P]
  · simp only [Z_self, map_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_gt h 𝒦 z hji, map_neg, map_P]

theorem Z_swap (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i)) :
    Z h 𝒦 z j i W hW' = -Z h 𝒦 z i j W hW := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_gt h 𝒦 z hij]
  · simp only [Z_self, neg_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_lt h 𝒦 z hji, neg_neg]

theorem Z_add_Z (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) (i j l : 𝒦.ι) (W : X.Opens)
    (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l)) :
    Z h 𝒦 z i j W (hW.trans (h.preimage_mono inf_le_left)) +
        Z h 𝒦 z j l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      Z h 𝒦 z i l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by

  have key : ∀ (a b c : 𝒦.ι) (hab : a < b) (hbc : b < c) (V : X.Opens) (hV : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c))
      (h₁ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b)) (h₂ : V ≤ h ⁻¹ᵁ (𝒦.U b ⊓ 𝒦.U c)) (h₃ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U c)),
      Z h 𝒦 z a b V h₁ + Z h 𝒦 z b c V h₂ = Z h 𝒦 z a c V h₃ := by
    intro a b c hab hbc V hV h₁ h₂ h₃
    rw [Z_of_lt h 𝒦 z hab, Z_of_lt h 𝒦 z hbc, Z_of_lt h 𝒦 z (hab.trans hbc)]
    exact P_add_P h 𝒦 z hz hab hbc V hV
  have hWij : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j) := hW.trans (h.preimage_mono inf_le_left)
  have hWjl : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))
  have hWil : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))
  have hWji : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i) := hWij.trans (le_of_eq (by rw [inf_comm]))
  have hWlj : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U j) := hWjl.trans (le_of_eq (by rw [inf_comm]))
  have hWli : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U i) := hWil.trans (le_of_eq (by rw [inf_comm]))
  have perm : ∀ (a b c : 𝒦.ι), W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l) →
      ({a, b, c} : Set 𝒦.ι) ⊆ {i, j, l} → W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c) := by
    intro a b c hW habc
    refine hW.trans (h.preimage_mono ?_)
    have mem : ∀ x ∈ ({i, j, l} : Set 𝒦.ι), 𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l ≤ 𝒦.U x := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]
    exact le_inf (le_inf (mem a (habc (by simp))) (mem b (habc (by simp)))) (mem c (habc (by simp)))
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · exact key i j l hij hjl W hW hWij hWjl hWil
    · rw [Z_self, add_zero]
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key i l j hil hlj W (perm i l j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWil hWlj hWij
        rw [Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key l i j hli hij W (perm l i j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWli hWij hWlj
        rw [Z_swap h 𝒦 z i l W hWil hWli, Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination e
  · rw [Z_self, zero_add]
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key j i l hji hil W (perm j i l hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWji hWil hWjl
        rw [Z_swap h 𝒦 z i j W hWij hWji] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key j l i hjl hli W (perm j l i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWjl hWli hWji
        rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z i l W hWil hWli] at e
        linear_combination e
    · rw [Z_self, add_zero]
    ·
      have e := key l j i hlj hji W (perm l j i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWlj hWji hWli
      rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z j l W hWjl hWlj, Z_swap h 𝒦 z i l W hWil hWli] at e
      linear_combination -e

end Pairs

section Branches

variable {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R')) {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

theorem inter_le_two (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (s : 𝒲.Idx 1) : 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U (lam (s.1 0)) ⊓ 𝒦.U (lam (s.1 1))) := by
  rw [Scheme.Hom.preimage_inf]
  exact le_inf ((𝒲.inter_le s 0).trans (hlam _)) ((𝒲.inter_le s 1).trans (hlam _))

theorem unitPullback_one_eq_Z (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)
    (s : 𝒲.Idx 1) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z s =
      Z h 𝒦 z (lam (s.1 0)) (lam (s.1 1)) (𝒲.inter s) (inter_le_two h 𝒲 𝒦 lam hlam s) := by
  classical
  have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
  rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_lt hlt)
      · exact absurd hab (ne_of_gt hlt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := by
      rw [Tuple.sort_eq_refl_iff_monotone]
      intro a b hab
      fin_cases a <;> fin_cases b
      · exact le_rfl
      · exact le_of_lt hlt
      · exact absurd hab (by decide)
      · exact le_rfl
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hlt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort, Equiv.Perm.sign_refl,
      Units.val_one, one_smul, Z_of_lt h 𝒦 z hlt]
    exact pb_congr h 𝒦 z hidx _ _ _
  ·
    have hninj : ¬ Function.Injective (lam ∘ s.1) := fun hinj => absurd (hinj (a₁ := 0) (a₂ := 1) heq) (by decide)
    rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hninj]
    exact (Z_of_eq h 𝒦 z heq _ _).symm
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_gt hgt)
      · exact absurd hab (ne_of_lt hgt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := by
      symm
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · intro a b hab
        fin_cases a <;> fin_cases b
        · exact le_rfl
        · exact le_of_lt (by simpa using hgt)
        · exact absurd hab (by decide)
        · exact le_rfl
      · intro a b hab hfab
        exact absurd ((Equiv.swap (0 : Fin 2) 1).injective (hinj hfab)) (ne_of_lt hab)
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hgt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort,
      Equiv.Perm.sign_swap (by decide), Units.val_neg, Units.val_one, neg_one_smul, Z_of_gt h 𝒦 z hgt]
    congr 1
    exact pb_congr h 𝒦 z hidx _ _ _

end Branches

end LamIndepAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LamIndepAux
open scoped TensorProduct

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit πX).cochain 𝒲 0,
      (OModulePresheaf.unit πX).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z - OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' 1 z := by
  classical

  have hle0 : ∀ t : 𝒲.Idx 0, 𝒲.inter t ≤ h ⁻¹ᵁ (𝒦.U (lam (t.1 0)) ⊓ 𝒦.U (lam' (t.1 0))) := fun t => by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf ((𝒲.inter_le t 0).trans (hlam _)) ((𝒲.inter_le t 0).trans (hlam' _))
  refine ⟨fun t => -Z h 𝒦 z (lam (t.1 0)) (lam' (t.1 0)) (𝒲.inter t) (hle0 t), ?_⟩
  funext s

  have hW : 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U (lam (s.1 0)) ⊓ 𝒦.U (lam' (s.1 0)) ⊓ 𝒦.U (lam (s.1 1)) ⊓ 𝒦.U (lam' (s.1 1))) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact le_inf (le_inf (le_inf ((𝒲.inter_le s 0).trans (hlam _)) ((𝒲.inter_le s 0).trans (hlam' _)))
      ((𝒲.inter_le s 1).trans (hlam _))) ((𝒲.inter_le s 1).trans (hlam' _))
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.sub_apply, unitPullback_one_eq_Z πX h 𝒲 𝒦 lam hlam z s,
    unitPullback_one_eq_Z πX h 𝒲 𝒦 lam' hlam' z s]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]

  have hb : ∀ (j : Fin 2), (OModulePresheaf.unit πX).res (𝒲.inter_le_inter_face s j)
      (-Z h 𝒦 z (lam ((𝒲.face s j).1 0)) (lam' ((𝒲.face s j).1 0)) (𝒲.inter (𝒲.face s j)) (hle0 (𝒲.face s j))) =
      -Z h 𝒦 z (lam ((𝒲.face s j).1 0)) (lam' ((𝒲.face s j).1 0)) (𝒲.inter s)
        ((𝒲.inter_le_inter_face s j).trans (hle0 (𝒲.face s j))) := by
    intro j
    show (X.presheaf.map (homOfLE (𝒲.inter_le_inter_face s j)).op).hom (-_) = _
    rw [map_neg, map_Z]
  rw [hb 0, hb 1]

  change -Z h 𝒦 z (lam (s.1 1)) (lam' (s.1 1)) (𝒲.inter s) _ + - -Z h 𝒦 z (lam (s.1 0)) (lam' (s.1 0)) (𝒲.inter s) _ =
    Z h 𝒦 z (lam (s.1 0)) (lam (s.1 1)) (𝒲.inter s) _ - Z h 𝒦 z (lam' (s.1 0)) (lam' (s.1 1)) (𝒲.inter s) _

  have ha : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam (s.1 0)) := (𝒲.inter_le s 0).trans (hlam _)
  have hb : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam (s.1 1)) := (𝒲.inter_le s 1).trans (hlam _)
  have ha' : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam' (s.1 0)) := (𝒲.inter_le s 0).trans (hlam' _)
  have hb' : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam' (s.1 1)) := (𝒲.inter_le s 1).trans (hlam' _)
  have h3 : ∀ (x y w : 𝒦.ι), 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U x → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U y → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U w →
      𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U x ⊓ 𝒦.U y ⊓ 𝒦.U w) := by
    intro x y w hx hy hw
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact le_inf (le_inf hx hy) hw
  have h2 : ∀ (x y : 𝒦.ι), 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U x → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U y → 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U x ⊓ 𝒦.U y) := by
    intro x y hx hy
    rw [Scheme.Hom.preimage_inf]
    exact le_inf hx hy
  have e1 := Z_add_Z h 𝒦 z hz (lam (s.1 0)) (lam' (s.1 0)) (lam (s.1 1)) (𝒲.inter s) (h3 _ _ _ ha ha' hb)
  have e2 := Z_add_Z h 𝒦 z hz (lam' (s.1 0)) (lam' (s.1 1)) (lam (s.1 1)) (𝒲.inter s) (h3 _ _ _ ha' hb' hb)
  have e3 := Z_swap h 𝒦 z (lam (s.1 1)) (lam' (s.1 1)) (𝒲.inter s) (h2 _ _ hb hb') (h2 _ _ hb' hb)
  linear_combination e1 + e2 - e3
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct


private theorem AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit πX).cochain 𝒲 0,
      (OModulePresheaf.unit πX).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z - OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' 1 z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite


namespace C1Body

section Res
variable {P : Scheme.{u}}

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_self {U : P.Opens} (h : U ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), P.presheaf.map_id]; rfl

theorem res_res_self {U V : P.Opens} (h₁ : U ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x) = x := by
  rw [res_res, res_self]

theorem res_app {X : Scheme.{u}} (s : X ⟶ P) {U V : P.Opens} (h : V ≤ U) (x : Γ(P, U)) :
    (s.app V).hom ((P.presheaf.map (homOfLE h).op).hom x)
      = (X.presheaf.map (homOfLE (s.preimage_mono h)).op).hom ((s.app U).hom x) := by
  exact congrArg (fun φ => φ.hom x) (s.naturality (homOfLE h).op)

theorem res_appLE {X : Scheme.{u}} (p : P ⟶ X) {U : X.Opens} {V W : P.Opens} (e : V ≤ p ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(X, U)) :
    (P.presheaf.map (homOfLE h).op).hom ((p.appLE U V e).hom y) = (p.appLE U W (h.trans e)).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X : Scheme.{u}} (p : P ⟶ X) {U U' : X.Opens} {V : P.Opens} (e : V ≤ p ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(X, U')) :
    (p.appLE U V e).hom ((X.presheaf.map (homOfLE h).op).hom y)
      = (p.appLE U' V (e.trans (p.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end Res

end C1Body

namespace C1Body

section ResAny
variable {P : Scheme.{u}}
theorem res_any {U W : P.Opens} (i : op U ⟶ op W) (h : W ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map i).hom x = (P.presheaf.map (homOfLE h).op).hom x := by
  rw [Subsingleton.elim i (homOfLE h).op]

theorem appLE_of_eq_id {X : Scheme.{u}} (f : X ⟶ X) (hf : f = 𝟙 X) {U V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V ≤ U) (y : Γ(X, U)) :
    (f.appLE U V e).hom y = (X.presheaf.map (homOfLE h).op).hom y := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  change (X.presheaf.map (homOfLE e).op).hom ((𝟙 Γ(X, U) : Γ(X, U) ⟶ Γ(X, U)).hom y) = _
  rw [CommRingCat.id_apply]
  exact res_any _ h y
end ResAny

open AlgebraicGeometry.OModulePresheaf.Leray

section Main

variable {R : Type u} [CommRing R] {X P : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R)) (p : P ⟶ X) (s : X ⟶ P) [IsAffineHom s]
  (𝒲 : P.OrderedAffineCover)

theorem pre_pre (hs : s ≫ p = 𝟙 X) (V : X.Opens) : s ⁻¹ᵁ (p ⁻¹ᵁ V) = V := by
  rw [← Scheme.Hom.comp_preimage, hs]; rfl

abbrev XO {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) : X.Opens :=
  (𝒲.comap s).inter τ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒲.comap s).inter σ))

theorem XO_le {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) :
    XO p s 𝒲 σ τ ≤ s ⁻¹ᵁ (biOpen p (𝒲.comap s) 𝒲 a b σ τ) :=
  inf_le_inf_right _ (𝒲.comap_inter_le s τ)

noncomputable def pull {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (x : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) : Γ(X, XO p s 𝒲 σ τ) :=
  (s.appLE (biOpen p (𝒲.comap s) 𝒲 a b σ τ) (XO p s 𝒲 σ τ) (XO_le p s 𝒲 σ τ)).hom x

theorem pull_res {a b a' b' : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (σ' : (𝒲.comap s).Idx a') (τ' : (𝒲.comap s).Idx b')
    (h : biOpen p (𝒲.comap s) 𝒲 a' b' σ' τ' ≤ biOpen p (𝒲.comap s) 𝒲 a b σ τ)
    (h' : XO p s 𝒲 σ' τ' ≤ XO p s 𝒲 σ τ)
    (x : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) :
    pull p s 𝒲 σ' τ' ((P.presheaf.map (homOfLE h).op).hom x)
      = (X.presheaf.map (homOfLE h').op).hom (pull p s 𝒲 σ τ x) := by
  unfold pull
  rw [appLE_res, res_appLE]

theorem pull_sum {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) {ι : Type*} (t : Finset ι)
    (f : ι → Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) (n : ι → ℤ) :
    pull p s 𝒲 σ τ (∑ j ∈ t, n j • f j) = ∑ j ∈ t, n j • pull p s 𝒲 σ τ (f j) := by
  unfold pull; simp only [map_sum, map_zsmul]

theorem pull_sub {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (x y : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) :
    pull p s 𝒲 σ τ (x - y) = pull p s 𝒲 σ τ x - pull p s 𝒲 σ τ y := by
  unfold pull; simp only [map_sub]

theorem pull_appLE (hs : s ≫ p = 𝟙 X) {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (y : Γ(X, (𝒲.comap s).inter σ)) (h : XO p s 𝒲 σ τ ≤ (𝒲.comap s).inter σ) :
    pull p s 𝒲 σ τ ((p.appLE ((𝒲.comap s).inter σ) (biOpen p (𝒲.comap s) 𝒲 a b σ τ) inf_le_right).hom y)
      = (X.presheaf.map (homOfLE h).op).hom y := by
  unfold pull
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_of_eq_id _ hs _ h y

end Main

end C1Body

namespace C1Body
open AlgebraicGeometry.OModulePresheaf.Leray

section MainC

variable {R : Type u} [CommRing R] {X P : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R)) (p : P ⟶ X) (s : X ⟶ P) [IsAffineHom s]
  (𝒲 : P.OrderedAffineCover)

local notation "𝒦" => (Scheme.OrderedAffineCover.comap 𝒲 s)

omit πX p s 𝒲 in
theorem alt_two {M : Type*} [AddCommGroup M] (x : M) :
    ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • x = 0 := by
  show ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • x = 0
  rw [Fin.sum_univ_two]; simp

noncomputable def ΘP {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) : biC p πX 𝒦 𝒲 a b :=
  fun στ => (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a b στ.1 στ.2) inf_le_right).hom (y στ.1)

theorem ΘP_apply {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (στ : BiIdx 𝒦 𝒲 a b) :
    ΘP πX p s 𝒲 y στ = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a b στ.1 στ.2) inf_le_right).hom (y στ.1) :=
  rfl

theorem dV_ΘP {a : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) :
    dV p πX 𝒦 𝒲 a 0 (ΘP πX p s 𝒲 y) = 0 := by
  funext στ
  rw [dV_apply', Pi.zero_apply]
  have : ∀ j : Fin (0 + 2),
      (P.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj ((𝒦).inter στ.1))
        (𝒲.inter_le_inter_face στ.2 j))).op).hom (ΘP πX p s 𝒲 y (στ.1, 𝒲.face στ.2 j))
        = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a 1 στ.1 στ.2) inf_le_right).hom (y στ.1) := by
    intro j
    rw [ΘP_apply, res_appLE]
  simp only [this]
  exact alt_two _

noncomputable def dK {a : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (σ : (𝒦).Idx (a + 1)) :
    Γ(X, (𝒦).inter σ) :=
  ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (X.presheaf.map (homOfLE ((𝒦).inter_le_inter_face σ j)).op).hom (y ((𝒦).face σ j))

theorem dH_ΘP {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (στ : BiIdx 𝒦 𝒲 (a + 1) b) :
    dH p πX 𝒦 𝒲 a b (ΘP πX p s 𝒲 y) στ
      = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 (a + 1) b στ.1 στ.2) inf_le_right).hom
          (dK s 𝒲 y στ.1) := by
  rw [dH_apply', dK, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ΘP_apply, res_appLE, appLE_res]

noncomputable def β0 (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))) :
    biC p πX 𝒦 𝒲 0 0 :=
  fun στ => (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter στ.2)
      (p.preimage_mono ((𝒦).inter_le στ.1 0)))).op).hom (βi (στ.1.1 0) στ.2)

theorem β0_apply (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)))
    (στ : BiIdx 𝒦 𝒲 0 0) :
    β0 πX p s 𝒲 βi στ = (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter στ.2)
      (p.preimage_mono ((𝒦).inter_le στ.1 0)))).op).hom (βi (στ.1.1 0) στ.2) :=
  rfl

theorem dV_β0 (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)))
    (hβi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (βi i (𝒲.face t j))) :
    dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) = biAug p πX 𝒦 𝒲 1 c := by
  funext στ
  obtain ⟨σ, τ⟩ := στ
  rw [dV_apply', biAug_apply]
  have hle : biOpen p 𝒦 𝒲 0 1 σ τ ≤ 𝒲.inter τ ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (σ.1 0)) :=
    inf_le_inf_left _ (p.preimage_mono ((𝒦).inter_le σ 0))
  rw [show (P.presheaf.map (homOfLE (inf_le_left : biOpen p 𝒦 𝒲 0 1 σ τ ≤ 𝒲.inter τ)).op).hom (c τ)
      = (P.presheaf.map (homOfLE hle).op).hom ((P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter τ ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (σ.1 0)) ≤ 𝒲.inter τ)).op).hom (c τ)) from (res_res _ _ _).symm,
    hβi (σ.1 0) τ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, β0_apply, res_res, res_res]
  rfl

theorem appLE_apply' {U : X.Opens} {V : P.Opens} (e : V ≤ p ⁻¹ᵁ U) (y : Γ(X, U)) :
    (p.appLE U V e).hom y = (P.presheaf.map (homOfLE e).op).hom ((p.app U).hom y) := rfl

omit πX p s 𝒲 in

theorem relAug_eq_zero {V' Z : Scheme.{u}} (q : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (K' : V'.OrderedAffineCover)
    (φ : OModulePresheaf.Hom (relHPresheaf q πZ K' 0) (pullOpen q πZ (⊤ : V'.Opens)))
    (hbij : ∀ U : Z.Opens, Function.Bijective (φ.app U))
    (haug : ∀ (U : Z.Opens) (x : LinearMap.ker (relAltd q πZ K' U 0)),
        relAug q πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1)
    (U : Z.Opens) (w : (pullOpen q πZ (⊤ : V'.Opens)).obj U) (h : relAug q πZ K' U w = 0) :
    w = 0 := by
  obtain ⟨y, rfl⟩ := (hbij U).2 w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hx : x.1 = 0 := by rw [← haug U x]; exact h
  have : x = 0 := Subtype.ext hx
  rw [this, Submodule.Quotient.mk_zero]; exact map_zero _

noncomputable def BX (bs : (OModulePresheaf.unit πX).cochain 𝒦 0) (σ : (𝒦).Idx 0) :
    relAltC s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 :=
  fun τ => (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)

theorem BX_apply (bs : (OModulePresheaf.unit πX).cochain 𝒦 0) (σ : (𝒦).Idx 0) (τ : (𝒦).Idx 0) :
    BX πX p s 𝒲 bs σ τ
      = (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ) := rfl

noncomputable def ζX (β : biC p πX 𝒦 𝒲 0 0) (σ : (𝒦).Idx 0) :
    relAltC s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 :=
  fun τ => pull p s 𝒲 σ τ (β (σ, τ))

theorem ζX_apply (β : biC p πX 𝒦 𝒲 0 0) (σ : (𝒦).Idx 0) (τ : (𝒦).Idx 0) :
    ζX πX p s 𝒲 β σ τ = pull p s 𝒲 σ τ (β (σ, τ)) := rfl

theorem pull_dV_eq (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1) (β : biC p πX 𝒦 𝒲 0 0)
    (hβ : dV p πX 𝒦 𝒲 0 0 β = biAug p πX 𝒦 𝒲 1 c) (σ : (𝒦).Idx 0) (τ' : (𝒦).Idx (0 + 1)) :
    (∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (ζX πX p s 𝒲 β σ ((𝒦).face τ' j)))
      = (s.appLE (𝒲.inter τ') (XO p s 𝒲 σ τ')
          ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans (𝒲.comap_inter_le s τ'))).hom (c τ') := by
  have h1 : pull p s 𝒲 σ τ' (dV p πX 𝒦 𝒲 0 0 β (σ, τ'))
      = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (ζX πX p s 𝒲 β σ ((𝒦).face τ' j)) := by
    rw [dV_apply', pull_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ζX_apply]
    exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (pull_res p s 𝒲 σ ((𝒦).face τ' j) σ τ' _
      (inf_le_inf_right _ ((𝒦).inter_le_inter_face τ' j)) _)
  rw [← h1, hβ, biAug_apply]
  unfold pull
  rw [appLE_res]

theorem relAltd_ζX_sub_BX (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (bs : (OModulePresheaf.unit πX).cochain 𝒦 0)
    (hbs : (OModulePresheaf.unit πX).d 𝒦 0 bs = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t)))
    (β : biC p πX 𝒦 𝒲 0 0) (hβ : dV p πX 𝒦 𝒲 0 0 β = biAug p πX 𝒦 𝒲 1 c) (σ : (𝒦).Idx 0) :
    relAltd s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 (ζX πX p s 𝒲 β σ - BX πX p s 𝒲 bs σ) = 0 := by
  rw [map_sub, sub_eq_zero]
  funext τ'
  rw [relAltd_apply', relAltd_apply', pull_dV_eq πX p s 𝒲 c β hβ σ τ']

  have h2 : ∀ j : Fin (0 + 2),
      (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (BX πX p s 𝒲 bs σ ((𝒦).face τ' j))
        = (X.presheaf.map (homOfLE ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans
            ((𝒦).inter_le_inter_face τ' j))).op).hom (bs ((𝒦).face τ' j)) := by
    intro j; rw [BX_apply, res_res]
  simp only [h2]
  have h3 : (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ')).op).hom
      ((OModulePresheaf.unit πX).d 𝒦 0 bs τ')
      = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (X.presheaf.map (homOfLE ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans
            ((𝒦).inter_le_inter_face τ' j))).op).hom (bs ((𝒦).face τ' j)) := by
    erw [OModulePresheaf.d_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [map_zsmul]
    exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (res_res _ _ _)
  rw [← h3, hbs, res_res]
  rfl

noncomputable def gK (hs : s ≫ p = 𝟙 X)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (σ : (𝒦).Idx 0) : Γ(X, (𝒦).inter σ) :=
  (X.presheaf.map (homOfLE (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le :
      (𝒦).inter σ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)))).op).hom (gX σ)

theorem gK_apply (hs : s ≫ p = 𝟙 X)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (σ : (𝒦).Idx 0) :
    gK πX p s 𝒲 hs gX σ = (X.presheaf.map (homOfLE (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le :
      (𝒦).inter σ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)))).op).hom (gX σ) := rfl

theorem XO_le_inter (hs : s ≫ p = 𝟙 X) {a b : ℕ} (σ : (𝒦).Idx a) (τ : (𝒦).Idx b) :
    XO p s 𝒲 σ τ ≤ (𝒦).inter σ :=
  inf_le_right.trans (pre_pre p s hs _).le

theorem e_eq_dK (hs : s ≫ p = 𝟙 X)
    (β : biC p πX 𝒦 𝒲 0 0) (e : ∀ σ : (𝒦).Idx 1, Γ(X, (𝒦).inter σ))
    (he : ∀ (σ : (𝒦).Idx 1) (τ : (𝒦).Idx 0), dH p πX 𝒦 𝒲 0 0 β (σ, τ)
        = (p.appLE ((𝒦).inter σ) (biOpen p 𝒦 𝒲 1 0 σ τ) inf_le_right).hom (e σ))
    (bs : (OModulePresheaf.unit πX).cochain 𝒦 0)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (hg : ∀ σ : (𝒦).Idx 0, relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) (gX σ)
        = ζX πX p s 𝒲 β σ - BX πX p s 𝒲 bs σ)
    (φX : OModulePresheaf.Hom (relHPresheaf s (p ≫ πX) 𝒦 0) (pullOpen s (p ≫ πX) (⊤ : X.Opens)))
    (hφXbij : ∀ U : P.Opens, Function.Bijective (φX.app U))
    (hφXaug : ∀ (U : P.Opens) (x : LinearMap.ker (relAltd s (p ≫ πX) 𝒦 U 0)),
        relAug s (p ≫ πX) 𝒦 U (φX.app U (Submodule.Quotient.mk x)) = x.1)
    (σ : (𝒦).Idx 1) :
    e σ = dK s 𝒲 (gK πX p s 𝒲 hs gX) σ := by

  have hζ' : ∀ (σ0 : (𝒦).Idx 0) (τ : (𝒦).Idx 0),
      ζX πX p s 𝒲 β σ0 τ = BX πX p s 𝒲 bs σ0 τ + relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ0)) (gX σ0) τ := by
    intro σ0 τ
    have h := congrFun (hg σ0) τ
    rw [Pi.sub_apply] at h
    rw [h]; abel
  have hpt : ∀ τ : (𝒦).Idx 0,
      (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (e σ)
        = (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (dK s 𝒲 (gK πX p s 𝒲 hs gX) σ) := by
    intro τ
    have hB : ∀ j : Fin (0 + 2),
        XO p s 𝒲 σ τ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter ((𝒦).face σ j))) := fun j =>
      (inf_le_inf_left _ (s.preimage_mono (p.preimage_mono ((𝒦).inter_le_inter_face σ j)))).trans
        (inf_le_inf_right _ le_top)
    have step : ∀ (j : Fin (0 + 2))
        (hh : biOpen p 𝒦 𝒲 (0 + 1) 0 σ τ ≤ biOpen p 𝒦 𝒲 0 0 ((𝒦).face σ j) τ),
        pull p s 𝒲 σ τ ((P.presheaf.map (homOfLE hh).op).hom (β ((𝒦).face σ j, τ)))
          = (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)
            + (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      intro j hh
      rw [pull_res p s 𝒲 ((𝒦).face σ j) τ σ τ hh
        (inf_le_inf_left _ (s.preimage_mono (p.preimage_mono ((𝒦).inter_le_inter_face σ j)))),
        ← ζX_apply, hζ']
      erw [map_add]
      rw [BX_apply, res_res, relAug_apply, res_res]
    have L : (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      rw [← pull_appLE p s 𝒲 hs σ τ (e σ) (XO_le_inter p s 𝒲 hs σ τ), ← he σ τ, dH_apply', pull_sum]
      calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull p s 𝒲 σ τ
              ((P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter τ) ((Opens.map p.base).monotone
                ((𝒦).inter_le_inter_face σ j)))).op).hom (β ((𝒦).face σ j, τ)))
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              ((X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)
                + (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j))) :=
            Finset.sum_congr rfl (fun j _ => by rw [step j])
        _ = (∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ))
            + ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
                (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun j _ => smul_add _ _ _)
        _ = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
            rw [alt_two, zero_add]
    have Rr : (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (dK s 𝒲 (gK πX p s 𝒲 hs gX) σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      rw [dK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, gK_apply, res_res, res_res]
    rw [L, Rr]

  have hw : (⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)) : X.Opens) ≤ (𝒦).inter σ :=
    inf_le_right.trans (pre_pre p s hs _).le
  have h0 : relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ))
      ((X.presheaf.map (homOfLE hw).op).hom (e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ)) = 0 := by
    funext τ
    rw [relAug_apply, Pi.zero_apply, res_res, map_sub]
    exact sub_eq_zero.mpr (hpt τ)
  have h1 := relAug_eq_zero s (p ≫ πX) 𝒦 φX hφXbij hφXaug _ _ h0
  have h2 : e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ = 0 := by
    rw [← res_res_self (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le) hw
      (e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ), h1]
    exact map_zero _
  exact sub_eq_zero.mp h2

theorem main [IsSeparated πX] [IsSeparated (p ≫ πX)] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by
  classical
  obtain ⟨hexact, hker0, hinj⟩ := rows_exact p πX 𝒦 𝒲
  choose βi hβi using hcU
  have hdVβ : dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) = biAug p πX 𝒦 𝒲 1 c :=
    dV_β0 πX p s 𝒲 c βi hβi

  have hdVδ : dV p πX 𝒦 𝒲 1 0 (dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi)) = 0 := by
    have h1 := LinearMap.congr_fun (dHV_comm p πX 𝒦 𝒲 0 0) (β0 πX p s 𝒲 βi)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, hdVβ]
    have hm : biAug p πX 𝒦 𝒲 1 c ∈ LinearMap.ker ((LerayDblCpx p πX 𝒦 𝒲).dH 0 1) := by
      rw [hker0 1]; exact ⟨c, rfl⟩
    exact hm

  obtain ⟨φ, hφbij, hφaug⟩ := exists_hom_relHPresheaf_zero p πX 𝒲
  have he' : ∀ σ : (𝒦).Idx 1, ∃ eσ : Γ(X, (𝒦).inter σ), ∀ τ : (𝒦).Idx 0,
      dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) (σ, τ)
        = (p.appLE ((𝒦).inter σ) (biOpen p 𝒦 𝒲 1 0 σ τ) inf_le_right).hom eσ := by
    intro σ
    have hδσ : relAltd p πX 𝒲 ((𝒦).inter σ) 0
        (fun τ => dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) (σ, τ)) = 0 := by
      funext τ'
      have h2 := congrFun hdVδ (σ, τ')
      rw [dV_apply'] at h2
      rw [relAltd_apply']
      exact h2
    obtain ⟨eσ, heσ⟩ := hp ((𝒦).inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter πX 𝒦 σ)
      ((P.presheaf.map (homOfLE (le_inf le_top le_rfl :
          p ⁻¹ᵁ ((𝒦).inter σ) ≤ ⊤ ⊓ p ⁻¹ᵁ ((𝒦).inter σ))).op).hom
        (φ.app ((𝒦).inter σ) (Submodule.Quotient.mk ⟨_, LinearMap.mem_ker.mpr hδσ⟩)))
    refine ⟨eσ, fun τ => ?_⟩
    have h3 := congrFun (hφaug ((𝒦).inter σ) ⟨_, LinearMap.mem_ker.mpr hδσ⟩) τ
    rw [relAug_apply] at h3
    rw [appLE_apply', heσ, res_res]
    exact h3.symm
  choose e he using he'

  obtain ⟨bs, hbs⟩ := hcs
  obtain ⟨φX, hφXbij, hφXaug⟩ := exists_hom_relHPresheaf_zero s (p ≫ πX) 𝒦
  have hζ := relAltd_ζX_sub_BX πX p s 𝒲 c bs hbs (β0 πX p s 𝒲 βi) hdVβ
  have hg' : ∀ σ0 : (𝒦).Idx 0,
      ∃ g0 : (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ0)),
        relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ0)) g0
          = ζX πX p s 𝒲 (β0 πX p s 𝒲 βi) σ0 - BX πX p s 𝒲 bs σ0 :=
    fun σ0 => ⟨φX.app _ (Submodule.Quotient.mk ⟨_, LinearMap.mem_ker.mpr (hζ σ0)⟩), hφXaug _ _⟩
  choose gX hgX using hg'
  have heq : ∀ σ : (𝒦).Idx 1, e σ = dK s 𝒲 (gK πX p s 𝒲 hs gX) σ :=
    e_eq_dK πX p s 𝒲 hs (β0 πX p s 𝒲 βi) e he bs gX hgX φX hφXbij hφXaug

  have hH : dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX)) = 0 := by
    rw [map_sub]
    funext στ
    obtain ⟨σ, τ⟩ := στ
    rw [Pi.sub_apply, Pi.zero_apply, he σ τ, dH_ΘP, ← heq σ]
    exact sub_self _
  have hV : dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX))
      = biAug p πX 𝒦 𝒲 1 c := by
    rw [map_sub, hdVβ, dV_ΘP, sub_zero]
  have hmem : (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX))
      ∈ LinearMap.range (biAug p πX 𝒦 𝒲 0) := by
    rw [← hker0 0]; exact hH
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, hinj 1 ?_⟩
  have h4 : (LerayDblCpx p πX 𝒦 𝒲).dV 0 0 (biAug p πX 𝒦 𝒲 0 b)
      = biAug p πX 𝒦 𝒲 (0 + 1) ((OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b) :=
    LinearMap.congr_fun (dV_comp_biAug p πX 𝒦 𝒲 0) b
  have h5 : (LerayDblCpx p πX 𝒦 𝒲).dV 0 0 (biAug p πX 𝒦 𝒲 0 b) = biAug p πX 𝒦 𝒲 1 c := by
    rw [hb]; exact hV
  exact h4.symm.trans h5

end MainC
end C1Body

theorem solution
    {R : Type u} [CommRing R] {X P : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX]
    (p : P ⟶ X) [IsSeparated (p ≫ πX)]
    (s : X ⟶ P) [IsAffineHom s] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by
  exact C1Body.main πX p s 𝒲 hs hp c hc hcU hcs
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
    {R : Type u} [CommRing R] {X P : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX]
    (p : P ⟶ X) [IsSeparated (p ≫ πX)]
    (s : X ⟶ P) [IsAffineHom s] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace C2KunnethH0Aux

theorem flat_of_field {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Flat f := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := (inferInstance : Subsingleton (PrimeSpectrum k))
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  infer_instance

theorem bijective_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    Function.Bijective (f.appLE ⊤ ⊤ e).hom ↔ Function.Bijective f.appTop.hom := by
  rw [Scheme.Hom.appLE_congr f e rfl (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)
    (fun φ => Function.Bijective φ.hom), Scheme.Hom.appLE_eq_app]
  exact Iff.rfl

end C2KunnethH0Aux

open C2KunnethH0Aux in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by
  haveI : Flat fX := flat_of_field fX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated fY

  haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hY
  haveI hfY : IsIso fY.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  have hUSX : U ≤ fX ⁻¹ᵁ ⊤ := le_top
  have hUST : (⊤ : Y.Opens) ≤ fY ⁻¹ᵁ ⊤ := by simp
  have hUY : p₁ ⁻¹ᵁ U = p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ ⊤ := by simp
  haveI : IsIso (fY.appLE ⊤ ⊤ hUST) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((bijective_appLE_top_iff fY hUST).mpr (ConcreteCategory.bijective_of_isIso fY.appTop))
  haveI hps := isIso_pushoutSection_of_isQuasiSeparated_of_flat_left hP hUST hUSX hUY
    (isAffineOpen_top _) hU
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ)
  have hcomp : pushout.inl (fX.appLE ⊤ U hUSX) (fY.appLE ⊤ ⊤ hUST) ≫
      pushoutSection hP hUST hUSX hUY = p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp) :=
    pushout.inl_desc _ _ _
  have hiso : IsIso (p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp)) := by
    rw [← hcomp]
    infer_instance
  have := ConcreteCategory.bijective_of_isIso (p₁.appLE U (p₁ ⁻¹ᵁ U) le_rfl)
  rwa [Scheme.Hom.appLE_eq_app] at this
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace


namespace G1SlabZigzagAux

variable {P : Scheme.{u}}

noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (U : X.Opens)

theorem isSeparated_fst (hP : IsPullback p₁ p₂ fX fY) : IsSeparated p₁ :=
  MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)

theorem isAffineOpen_strip (hP : IsPullback p₁ p₂ fX fY) (hU : IsAffineOpen U) {a : ℕ} (σ : 𝒱.Idx a) :
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) := by
  have hV : IsAffineOpen (𝒱.inter σ) := Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of k))
  have hsq := Scheme.Hom.isPullback_resLE hP (US := ⊤) (UT := 𝒱.inter σ) (UX := U)
    (by simp) (by simp) (UY := p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) rfl
  exact .of_isIso hsq.isoPullback.hom

theorem restrict_inter {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R)) [IsSeparated π]
    {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  show (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end Main

end G1SlabZigzagAux

open G1SlabZigzagAux in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
      (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)),
      (∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
        (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
                (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j))) ∧
      (∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
        (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
                ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t)) ∧
      (∀ ρ : 𝒱.Idx (1 + 1),
        ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e (𝒱.face ρ j)) = 0) := by
  classical

  haveI : IsSeparated p₁ := isSeparated_fst fX fY p₁ p₂ hP
  haveI hπ : IsSeparated (p₁ ≫ fX) := inferInstance
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)

  have hF : ∀ {a : ℕ} (σ : 𝒱.Idx a), IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => isAffineOpen_strip fX fY p₁ p₂ 𝒱 U hP hU σ
  let K : ∀ {a : ℕ} (σ : 𝒱.Idx a), P.OrderedAffineCoverOf (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => 𝒲.restrict (p₁ ≫ fX) (hF σ)
  have hKi : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t = 𝒲.inter t ⊓ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => restrict_inter 𝒲 (p₁ ≫ fX) (hF σ) t
  have hBK : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ (K σ).inter t :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKB : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKW : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b), (K σ).inter t ≤ 𝒲.inter t :=
    fun σ t => (hKB σ t).trans (inf_le_left.trans inf_le_left)

  have step1 : ∀ σ : 𝒱.Idx 0, ∃ g : (K σ).cochain 0,
      (K σ).d (p₁ ≫ fX) 0 g = fun t => rr (hKW σ t) (c t) := by
    intro σ
    have hmem : (fun t => rr (hKW σ t) (c t) : (K σ).cochain 1) ∈
        LinearMap.ker ((K σ).d (p₁ ≫ fX) 1) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have h0' : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (OModulePresheaf.unit (p₁ ≫ fX)).res (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 := by
        have := congrFun hc s
        rwa [OModulePresheaf.d_apply] at this
      have h0 : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 := h0'
      have h1 := congrArg (rr (hKW σ s)) h0
      rw [map_sum, map_zero] at h1
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
      rw [map_zsmul]
      congr 1
      change rr _ (rr _ (c _)) = rr _ (rr _ (c _))
      simp only [rr_rr]
      try rfl
    obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen
      (p₁ ≫ fX) (K σ) (hF σ) 0 hmem
    exact ⟨g, hg⟩
  choose g hg using step1

  let γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => rr (hBK σ t) (g σ t)

  have hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      rr (inf_le_left.trans inf_le_left) (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))
              (γ σ (𝒲.face t j)) := by
    intro σ t
    have h1 := congrFun (hg σ) t
    rw [Scheme.OrderedAffineCoverOf.d_apply] at h1
    have h2 := congrArg (rr (hBK σ t)) h1
    rw [map_sum, rr_rr] at h2
    refine Eq.trans h2.symm (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (g σ _)) = rr _ (rr _ (g σ _))
    simp only [rr_rr]
    try rfl

  have step2 : ∀ σ : 𝒱.Idx 1, ∃ eσ : Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ),
      (K σ).aug (p₁ ≫ fX) eσ = fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) := by
    intro σ
    set η : (K σ).cochain 0 := fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) with hη
    have hmem : η ∈ LinearMap.ker ((K σ).d (p₁ ≫ fX) 0) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have key : ∀ j : Fin (0 + 2),
          ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) •
            rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
              (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))))
              (γ (𝒱.face σ j) (𝒲.face s l))
          = rr (hKW σ s) (c s) := by
        intro j
        have hle : (K σ).inter s ≤ 𝒲.inter s ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter (𝒱.face σ j) :=
          (hKB σ s).trans (inf_le_inf_left _ ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))
        have h3 := congrArg (rr hle) (hV (𝒱.face σ j) s)
        rw [rr_rr, map_sum] at h3
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h3.symm
        rw [map_zsmul]
        congr 1
        change rr _ (rr _ (g _ _)) = rr _ (rr _ (rr _ (g _ _)))
        simp only [rr_rr]
        try rfl
      calc ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) • rr ((K σ).inter_le_inter_face s l) (η ((K σ).face s l))
          = ∑ l : Fin (0 + 2), ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (l : ℕ)) •
              rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
                (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                  ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))))
                (γ (𝒱.face σ j) (𝒲.face s l))) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hη, map_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_zsmul, smul_comm]
            congr 2
            change rr _ (rr _ (rr _ (g _ _))) = rr _ (rr _ (g _ _))
            simp only [rr_rr]
            try rfl
        _ = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • rr (hKW σ s) (c s) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.smul_sum, key j]
        _ = 0 := by
            rw [Fin.sum_univ_two]
            simp
    have hrange : η ∈ LinearMap.range ((K σ).aug (p₁ ≫ fX)) := by
      rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact hmem
    obtain ⟨eσ, heσ⟩ := hrange
    exact ⟨eσ, heσ.trans hη⟩
  choose e he using step2

  have hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))) (γ (𝒱.face σ j) t) := by
    intro σ t
    have h1 := congrFun (he σ) t
    rw [Scheme.OrderedAffineCoverOf.aug_apply] at h1
    have h2 := congrArg (rr (hBK σ t)) h1
    change rr _ (rr _ (e σ)) = _ at h2
    rw [rr_rr, map_sum] at h2
    refine Eq.trans h2 (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (rr _ (g _ _))) = rr _ (rr _ (g _ _))
    simp only [rr_rr]
    try rfl
  refine ⟨γ, e, hV, hH, ?_⟩

  intro ρ
  have hbox : ∀ t : 𝒲.Idx 0,
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)
        (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (inf_le_inf_left (p₁ ⁻¹ᵁ U)
            ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j))) (e (𝒱.face ρ j)))
        = 0 := by
    intro t
    let G := OModulePresheaf.Leray.pullOpen p₂ fY (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
    have hdd := congrFun (LinearMap.congr_fun (OModulePresheaf.Leray.d_d G 𝒱 0)
      (fun σ => γ σ t : G.cochain 𝒱 0)) ρ
    rw [LinearMap.comp_apply, LinearMap.zero_apply, OModulePresheaf.d_apply] at hdd
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hdd
    rw [map_zsmul, OModulePresheaf.d_apply, rr_rr]
    congr 1
    have hle : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter (𝒱.face ρ j) :=
      inf_le_inf_left _ ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j))
    have h5 := congrArg (rr hle) (hH (𝒱.face ρ j) t)
    rw [rr_rr, map_sum] at h5
    rw [map_sum]
    refine h5.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_zsmul, map_zsmul]
    congr 1
  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (K ρ)
  rw [map_zero]
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Pi.zero_apply]
  change rr ((K ρ).inter_le_base t) _ = 0
  have hfac : rr ((K ρ).inter_le_base t)
      = (rr (hKB ρ t)).comp (rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)) := by
    ext x
    exact (rr_rr _ _ x).symm
  rw [hfac, RingHom.comp_apply, hbox t, map_zero]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
      (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)),
      (∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
        (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
                (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j))) ∧
      (∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
        (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
                ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t)) ∧
      (∀ ρ : 𝒱.Idx (1 + 1),
        ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e (𝒱.face ρ j)) = 0) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite


namespace G2aBody

section Res
variable {P : Scheme.{u}}

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end Res

section Cover

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
  (U : X.Opens) (hU : IsAffineOpen U)

noncomputable def boxCover {n : ℕ} (t : 𝒲.Idx n) : P.OrderedAffineCoverOf (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) where
  ι := 𝒱.ι
  U i := (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) ⊓ p₂ ⁻¹ᵁ 𝒱.U i
  isAffineOpen i := by
    haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
    haveI : IsSeparated (p₁ ≫ fX) := inferInstance
    have h1 : IsAffineOpen (𝒲.inter t) := Scheme.OrderedAffineCover.isAffineOpen_inter (p₁ ≫ fX) 𝒲 t
    have h2 : IsAffineOpen (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) :=
      Scheme.OrderedAffineCover.fiberAffineOpen p₁ fX h1 hU
    exact Scheme.OrderedAffineCover.fiberAffineOpen p₂ fY h2 (𝒱.isAffineOpen i)
  le _ := inf_le_left
  iSup_eq := by
    rw [← inf_iSup_eq, ← Scheme.Hom.preimage_iSup, 𝒱.iSup_eq_top]
    exact le_antisymm inf_le_left (le_inf le_rfl le_top)

variable {fX fY p₁ p₂ 𝒲 𝒱 U}

theorem boxCover_face {n m : ℕ} (t : 𝒲.Idx n) (σ : 𝒱.Idx (m + 1)) (j : Fin (m + 2)) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).face σ j = 𝒱.face σ j := rfl

theorem inter_le_box {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s := by
  refine le_inf (((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s 0).trans inf_le_left) ?_
  calc (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ ⨅ j, p₂ ⁻¹ᵁ 𝒱.U (s.1 j) :=
        le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans inf_le_right
    _ = p₂ ⁻¹ᵁ 𝒱.inter s := (Scheme.OrderedAffineCover.preimage_iInf_fin p₂ _).symm

theorem box_le_inter {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s :=
  le_iInf fun j => le_inf inf_le_left (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le s j)))

theorem inter_le_inter {n n' m : ℕ} (t : 𝒲.Idx n) (t' : 𝒲.Idx n') (h : 𝒲.inter t ≤ 𝒲.inter t')
    (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t').inter s :=
  le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans
    (inf_le_inf_right _ (inf_le_inf_right _ h))

end Cover

end G2aBody

open G2aBody in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (he : ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j))) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by
  classical
  obtain ⟨g, hg⟩ := he
  haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
  haveI : IsSeparated (p₁ ≫ fX) := inferInstance
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)

  let f : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).cochain 0 := fun t s =>
    (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom
      (γ s t - (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)).op).hom (g s))

  have hf : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).d (p₁ ≫ fX) 0 (f t) = 0 := by
    intro t
    funext σ
    rw [Scheme.OrderedAffineCoverOf.d_apply]
    have h1 := congrArg (fun x => (P.presheaf.map (homOfLE
      (inter_le_box hP hU t σ)).op).hom x) (hH σ t)
    have h2 := congrArg (fun x => (P.presheaf.map (homOfLE
      ((inter_le_box hP hU t σ).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right))).op).hom x) (hg σ)
    simp only [map_sum, map_zsmul, map_sub, G2aBody.res_res, f] at h1 h2 ⊢
    rw [Fin.sum_univ_two] at h1 h2 ⊢
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h1 h2 ⊢
    dsimp only [boxCover_face] at h1 h2 ⊢
    show _ = (0 : Γ(P, _))
    linear_combination h2 - h1

  have hglue : ∀ t : 𝒲.Idx 0, ∃ w : Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX) w = f t := by
    intro t
    have hmem : f t ∈ LinearMap.range ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX)) := by
      rw [← Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact LinearMap.mem_ker.mpr (hf t)
    exact LinearMap.mem_range.mp hmem
  choose β hβ using hglue
  have hβ' : ∀ (t : 𝒲.Idx 0) (s : 𝒱.Idx 0) {O : P.Opens}
      (h : O ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s)
      (h₁ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) (h₂ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)
      (h₃ : O ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s),
      (P.presheaf.map (homOfLE h₁).op).hom (β t)
        = (P.presheaf.map (homOfLE h₂).op).hom (γ s t) - (P.presheaf.map (homOfLE h₃).op).hom (g s) := by
    intro t s O h h₁ h₂ h₃
    have := congrArg (fun x => (P.presheaf.map (homOfLE h).op).hom x) (congrFun (hβ t) s)
    simp only [Scheme.OrderedAffineCoverOf.aug_apply, map_sub, G2aBody.res_res, f] at this
    exact this
  refine ⟨β, fun t => ?_⟩
  apply Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t)
  funext s
  simp only [Scheme.OrderedAffineCoverOf.aug_apply, map_sum, map_zsmul, G2aBody.res_res]
  have h3 := congrArg (fun x => (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom x) (hV s t)
  simp only [map_sum, map_zsmul, G2aBody.res_res] at h3
  rw [Fin.sum_univ_two] at h3 ⊢
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h3 ⊢
  have l0 := inter_le_inter hP hU t (𝒲.face t 0) (𝒲.inter_le_inter_face t 0) s
  have l1 := inter_le_inter hP hU t (𝒲.face t 1) (𝒲.inter_le_inter_face t 1) s
  rw [hβ' (𝒲.face t 0) s l0 _ (l0.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right)),
    hβ' (𝒲.face t 1) s l1 _ (l1.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right))]
  linear_combination h3
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (he : ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j))) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace


namespace G2bStripUniqueAux

variable {P : Scheme.{u}}

noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (U : X.Opens)

theorem isSeparated_fst (hP : IsPullback p₁ p₂ fX fY) : IsSeparated p₁ :=
  MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)

theorem isAffineOpen_strip (hP : IsPullback p₁ p₂ fX fY) (hU : IsAffineOpen U) {a : ℕ} (σ : 𝒱.Idx a) :
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) := by
  have hV : IsAffineOpen (𝒱.inter σ) := Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of k))
  have hsq := Scheme.Hom.isPullback_resLE hP (US := ⊤) (UT := 𝒱.inter σ) (UX := U)
    (by simp) (by simp) (UY := p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) rfl
  exact .of_isIso hsq.isoPullback.hom

theorem restrict_inter {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R)) [IsSeparated π]
    {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  show (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end Main

end G2bStripUniqueAux

open G2bStripUniqueAux in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (U' : X.Opens) (hU' : IsAffineOpen U') (hle : U' ≤ U)
    (γ' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e' : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U') (𝒲.inter_le_inter_face t j)))).op).hom (γ' σ (𝒲.face t j)))
    (hH' : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e' σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ' (𝒱.face σ j) t)) :
    ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ) - e' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by
  classical
  haveI : IsSeparated p₁ := isSeparated_fst fX fY p₁ p₂ hP
  haveI hπ : IsSeparated (p₁ ≫ fX) := inferInstance
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)

  have hF : ∀ {a : ℕ} (σ : 𝒱.Idx a), IsAffineOpen (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => isAffineOpen_strip fX fY p₁ p₂ 𝒱 U' hP hU' σ
  let K : ∀ {a : ℕ} (σ : 𝒱.Idx a), P.OrderedAffineCoverOf (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => 𝒲.restrict (p₁ ≫ fX) (hF σ)
  have hKi : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t = 𝒲.inter t ⊓ (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => restrict_inter 𝒲 (p₁ ≫ fX) (hF σ) t
  have hKB' : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => by rw [hKi, inf_assoc]
  have hB'K : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ (K σ).inter t :=
    fun σ t => by rw [hKi, inf_assoc]
  have hB'B : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => inf_le_inf_right _ (inf_le_inf_left _ ((Opens.map p₁.base).monotone hle))
  have hKB : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => (hKB' σ t).trans (hB'B σ t)
  have hKW : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b), (K σ).inter t ≤ 𝒲.inter t :=
    fun σ t => (hKB' σ t).trans (inf_le_left.trans inf_le_left)

  have step1 : ∀ i : 𝒱.Idx 0, ∃ gi : Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      (K i).aug (p₁ ≫ fX) gi = fun t => rr (hKB i t) (γ i t) - rr (hKB' i t) (γ' i t) := by
    intro i
    set δ : (K i).cochain 0 := fun t => rr (hKB i t) (γ i t) - rr (hKB' i t) (γ' i t) with hδ
    have hmem : δ ∈ LinearMap.ker ((K i).d (p₁ ≫ fX) 0) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have h1 := congrArg (rr (hKB i s)) (hV i s)
      have h1' := congrArg (rr (hKB' i s)) (hV' i s)
      rw [rr_rr, map_sum] at h1 h1'
      have h2 : rr ((hKB i s).trans (inf_le_left.trans inf_le_left)) (c s)
          = rr ((hKB' i s).trans (inf_le_left.trans inf_le_left)) (c s) := rfl
      calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • rr ((K i).inter_le_inter_face s j) (δ ((K i).face s j))
          = ∑ j : Fin (0 + 2), rr (hKB i s) (((-1 : ℤ) ^ (j : ℕ)) •
              rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter i) (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face s j)))
                (γ i (𝒲.face s j)))
            - ∑ j : Fin (0 + 2), rr (hKB' i s) (((-1 : ℤ) ^ (j : ℕ)) •
              rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter i) (inf_le_inf_right (p₁ ⁻¹ᵁ U') (𝒲.inter_le_inter_face s j)))
                (γ' i (𝒲.face s j))) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hδ, map_sub, smul_sub, map_zsmul, map_zsmul]
            congr 2
            · change rr _ (rr _ (γ _ _)) = rr _ (rr _ (γ _ _))
              simp only [rr_rr]
              try rfl
            · change rr _ (rr _ (γ' _ _)) = rr _ (rr _ (γ' _ _))
              simp only [rr_rr]
              try rfl
        _ = 0 := by rw [← h1, ← h1', h2, sub_self]
    have hrange : δ ∈ LinearMap.range ((K i).aug (p₁ ≫ fX)) := by
      rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact hmem
    obtain ⟨gi, hgi⟩ := hrange
    exact ⟨gi, hgi.trans hδ⟩
  choose g hg using step1
  refine ⟨g, fun σ => ?_⟩

  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (K σ)
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Scheme.OrderedAffineCoverOf.aug_apply, map_sub, map_sum]
  change rr _ (rr _ (e σ)) - rr _ (e' σ) = ∑ j : Fin (0 + 2), rr _ (((-1 : ℤ) ^ (j : ℕ)) • rr _ (g (𝒱.face σ j)))
  have hHt := congrArg (rr (hKB σ t)) (hH σ t)
  have hHt' := congrArg (rr (hKB' σ t)) (hH' σ t)
  rw [rr_rr, map_sum] at hHt hHt'
  rw [rr_rr, hHt, hHt', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, ← smul_sub]
  congr 1
  have hKK : (K σ).inter t ≤ (K (𝒱.face σ j)).inter t := by
    rw [hKi, hKi]
    exact inf_le_inf_left _ (inf_le_inf_left _ ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))
  have h3 := congrArg (rr hKK) (congrFun (hg (𝒱.face σ j)) t)
  rw [Scheme.OrderedAffineCoverOf.aug_apply] at h3
  change rr hKK (rr _ (g _)) = rr hKK (rr _ (γ _ _) - rr _ (γ' _ _)) at h3
  rw [rr_rr, map_sub, rr_rr, rr_rr] at h3
  change rr _ (rr _ (γ _ _)) - rr _ (rr _ (γ' _ _)) = rr _ (rr _ (g _))
  rw [rr_rr, rr_rr, rr_rr]
  exact h3.symm
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (U' : X.Opens) (hU' : IsAffineOpen U') (hle : U' ≤ U)
    (γ' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e' : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U') (𝒲.inter_le_inter_face t j)))).op).hom (γ' σ (𝒲.face t j)))
    (hH' : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e' σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ' (𝒱.face σ j) t)) :
    ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ) - e' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite


namespace G3Body

variable {Y P : Scheme.{u}}

theorem res_res {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x)
      = (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_appLE (f : Y ⟶ P) {U : P.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(P, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom y) = (f.appLE U W (h.trans e)).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res (f : Y ⟶ P) {U U' : P.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(P, U')) :
    (f.appLE U V e).hom ((P.presheaf.map (homOfLE h).op).hom y)
      = (f.appLE U' V (e.trans (f.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem app_eq_appLE' (f : Y ⟶ P) (U : P.Opens) (y : Γ(P, U)) :
    (f.app U).hom y = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom y := by
  rw [Scheme.Hom.app_eq_appLE]

theorem res_app_eq_appLE (f : Y ⟶ P) (U : P.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (y : Γ(P, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app U).hom y) = (f.appLE U W h).hom y := by
  rw [app_eq_appLE', res_appLE]

end G3Body

open G3Body in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x₀ : Spec (CommRingCat.of k) ⟶ X)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU₀ : x₀ ⁻¹ᵁ U = ⊤)
    (γ : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (e : ∀ σ : (𝒲.comap iY).Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (hV : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : (𝒲.comap iY).Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j)))).op).hom (γ ((𝒲.comap iY).face σ j) t)) :
    ∃ g : ∀ i : (𝒲.comap iY).Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter i)),
      ∀ σ : (𝒲.comap iY).Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j))))).op).hom (g ((𝒲.comap iY).face σ j)) := by
  classical
  obtain ⟨b, hb⟩ := hcY
  have hpre2 : ∀ W : Y.Opens, iY ⁻¹ᵁ (p₂ ⁻¹ᵁ W) = W := fun W => by
    rw [← Scheme.Hom.comp_preimage, hiY₂]; rfl
  have hpre1 : iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hiY₁, Scheme.Hom.comp_preimage, hU₀]; rfl

  have L1 : ∀ {n : ℕ} (s : 𝒲.Idx n),
      iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s) ≤ (𝒲.comap iY).inter s := fun s =>
    (iY.preimage_mono inf_le_right).trans (hpre2 _).le
  have LV : ∀ {n : ℕ} (s : 𝒲.Idx n), (𝒲.comap iY).inter s ≤ iY ⁻¹ᵁ 𝒲.inter s := fun s =>
    𝒲.comap_inter_le iY s

  have L2 : ∀ {n n' m : ℕ} (s : 𝒲.Idx n) (s' : 𝒲.Idx n') (t : 𝒲.Idx m),
      (𝒲.comap iY).inter s ≤ (𝒲.comap iY).inter s' →
      (𝒲.comap iY).inter s ≤ (𝒲.comap iY).inter t →
      iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s)
        ≤ iY ⁻¹ᵁ (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s') :=
    fun s s' t h1 h2 => by
      change iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) ⊓ iY ⁻¹ᵁ (p₂ ⁻¹ᵁ (𝒲.comap iY).inter s)
          ≤ iY ⁻¹ᵁ 𝒲.inter t ⊓ iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) ⊓ iY ⁻¹ᵁ (p₂ ⁻¹ᵁ (𝒲.comap iY).inter s')
      exact le_inf (le_inf ((L1 s).trans (h2.trans (LV t))) inf_le_left)
        (inf_le_right.trans (iY.preimage_mono (p₂.preimage_mono h1)))
  refine ⟨fun i => (iY.appLE _ _ (L2 i i i le_rfl le_rfl)).hom (γ i i)
      - (Y.presheaf.map (homOfLE (L1 i)).op).hom (b i), fun σ => ?_⟩
  have hσ₀ : (𝒲.comap iY).inter σ ≤ (𝒲.comap iY).inter (𝒲.face σ 0) :=
    (𝒲.comap iY).inter_le_inter_face σ 0
  have hσ₁ : (𝒲.comap iY).inter σ ≤ (𝒲.comap iY).inter (𝒲.face σ 1) :=
    (𝒲.comap iY).inter_le_inter_face σ 1

  have hE := congrArg
    (fun x => (iY.appLE _ (iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
      (L2 σ σ (𝒲.face σ 1) le_rfl hσ₁)).hom x) (hH σ (𝒲.face σ 1))
  simp only [map_sum, map_zsmul, appLE_res] at hE
  rw [Fin.sum_univ_two] at hE
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hE

  have hC := congrArg
    (fun x => (iY.appLE _ (iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
      (L2 σ (𝒲.face σ 0) σ hσ₀ le_rfl)).hom x) (hV (𝒲.face σ 0) σ)
  simp only [map_sum, map_zsmul, appLE_res] at hC
  rw [Fin.sum_univ_two] at hC
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hC

  have hD0 : ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (Y.presheaf.map (homOfLE ((𝒲.comap iY).inter_le_inter_face σ j)).op).hom
        (b ((𝒲.comap iY).face σ j))
      = (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY σ)).op).hom ((iY.app (𝒲.inter σ)).hom (c σ)) := by
    have := congrFun hb σ
    rw [OModulePresheaf.d_apply] at this
    exact this
  have hD := congrArg (fun x => (Y.presheaf.map (homOfLE (L1 σ)).op).hom x) hD0
  simp only [map_sum, map_zsmul, G3Body.res_res, res_app_eq_appLE, res_appLE] at hD
  rw [Fin.sum_univ_two] at hD
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hD

  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_sub,
    res_appLE, G3Body.res_res, app_eq_appLE']
  dsimp only [Scheme.OrderedAffineCover.comap_face] at hE hC hD ⊢
  linear_combination hE + hC + hD
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x₀ : Spec (CommRingCat.of k) ⟶ X)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU₀ : x₀ ⁻¹ᵁ U = ⊤)
    (γ : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (e : ∀ σ : (𝒲.comap iY).Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (hV : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : (𝒲.comap iY).Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j)))).op).hom (γ ((𝒲.comap iY).face σ j) t)) :
    ∃ g : ∀ i : (𝒲.comap iY).Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter i)),
      ∀ σ : (𝒲.comap iY).Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j))))).op).hom (g ((𝒲.comap iY).face σ j)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct


namespace E163G5A

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst hfg; rfl

theorem appLE_self_of_eq_id {X : Scheme.{u}} {k : X ⟶ X} (hk : k = 𝟙 X) (W : X.Opens)
    (h : W ≤ k ⁻¹ᵁ W) : k.appLE W W h = 𝟙 _ := by
  subst hk
  have hh : (homOfLE h).op = 𝟙 (op W) := Subsingleton.elim _ _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  rw [hh]
  exact X.presheaf.map_id _

theorem appLE_comp_appLE_eq_id {P Q : Scheme.{u}} (f : P ⟶ Q) (g : Q ⟶ P) (hfg : f ≫ g = 𝟙 P)
    (W : P.Opens) (W' : Q.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W) (h₂ : W ≤ f ⁻¹ᵁ W') :
    g.appLE W W' h₁ ≫ f.appLE W' W h₂ = 𝟙 _ := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact appLE_self_of_eq_id hfg W _

theorem appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (e₃ : W ≤ k ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (k.appLE U W e₃).hom x := by
  subst hk
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

noncomputable def sectionsIso {P Q : Scheme.{u}} (e : P ≅ Q) (W : P.Opens) (W' : Q.Opens)
    (hW : W = e.hom ⁻¹ᵁ W') : Γ(Q, W') ≅ Γ(P, W) where
  hom := e.hom.appLE W' W hW.le
  inv := e.inv.appLE W W' (by
    rw [hW, ← Scheme.Hom.comp_preimage, e.inv_hom_id]; exact le_rfl)
  hom_inv_id := appLE_comp_appLE_eq_id e.inv e.hom e.inv_hom_id W' W _ _
  inv_hom_id := appLE_comp_appLE_eq_id e.hom e.inv e.hom_inv_id W W' _ _

theorem transport {R : Type u} [CommRing R] {P Q : Scheme.{u}} (e : P ≅ Q)
    (W : P.Opens) (W' : Q.Opens) (hW : W = e.hom ⁻¹ᵁ W')
    [iQ : Algebra R Γ(Q, W')] [iP : Algebra R Γ(P, W)]
    (halg : ∀ r : R, (e.hom.appLE W' W hW.le).hom (algebraMap R Γ(Q, W') r) = algebraMap R Γ(P, W) r) :
    ∃ σ : Γ(Q, W') ≃ₐ[R] Γ(P, W), ∀ x, σ x = (e.hom.appLE W' W hW.le).hom x :=
  ⟨AlgEquiv.ofRingEquiv (f := (sectionsIso e W W' hW).commRingCatIsoToRingEquiv) halg, fun _ => rfl⟩

end E163G5A

theorem solution
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fX U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) ∧
    ∃ Φ : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), Φ (a ⊗ₜ[R] b) =
        (p₁.appLE U (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left).hom a *
          (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom b := by
  letI iU := Scheme.TwoAffineOpenCover.algebraOfHom fX U
  letI iV := Scheme.TwoAffineOpenCover.algebraOfHom fY V
  letI iW := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
  letI iW' := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst fX fY ≫ fX) (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V)
  have h60 := AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
    fX fY U hU V hV
  obtain ⟨hW'aff, e₀, he₀⟩ := h60
  have he₁ : hP.isoPullback.hom ≫ pullback.fst fX fY = p₁ := hP.isoPullback_hom_fst
  have he₂ : hP.isoPullback.hom ≫ pullback.snd fX fY = p₂ := hP.isoPullback_hom_snd
  have hW : (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) = hP.isoPullback.hom ⁻¹ᵁ (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, he₁, he₂]
  refine ⟨?_, ?_⟩
  · rw [hW]; exact hW'aff.preimage_of_isIso _
  have he₁' : hP.isoPullback.hom ≫ (pullback.fst fX fY ≫ fX) = p₁ ≫ fX := by
    rw [← Category.assoc, he₁]
  have hσ := E163G5A.transport (R := R) hP.isoPullback (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V) hW
    (iQ := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst fX fY ≫ fX) (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V))
    (iP := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V))
    (fun r => E163G5A.appLE_appLE_apply hP.isoPullback.hom (pullback.fst fX fY ≫ fX) (p₁ ≫ fX) he₁'
      ⊤ (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) le_top hW.le le_top ((Scheme.ΓSpecIso (.of R)).inv.hom r))
  obtain ⟨σ, hσ⟩ := hσ
  refine ⟨(e₀.trans σ).toLinearEquiv, fun a b => ?_⟩
  have h1 := E163G5A.appLE_appLE_apply hP.isoPullback.hom (pullback.fst fX fY) p₁ he₁
      U (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left hW.le inf_le_left a
  have h2 := E163G5A.appLE_appLE_apply hP.isoPullback.hom (pullback.snd fX fY) p₂ he₂
      V (pullback.fst fX fY ⁻¹ᵁ U ⊓ pullback.snd fX fY ⁻¹ᵁ V) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right hW.le inf_le_right b
  rw [AlgEquiv.toLinearEquiv_apply, AlgEquiv.trans_apply, hσ, he₀ a b, map_mul, h1, h2]

#print axioms solution
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct


private theorem AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fX U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) ∧
    ∃ Φ : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), Φ (a ⊗ₜ[R] b) =
        (p₁.appLE U (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left).hom a *
          (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom b := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace


namespace G5cAffineFamilyConstAux

variable {P : Scheme.{u}}

noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem restrict_inter (𝒲 : P.OrderedAffineCover) {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R))
    [IsSeparated π] {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  show (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end G5cAffineFamilyConstAux

open G5cAffineFamilyConstAux in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact fX] [IsSeparated fX]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ fX.appTop).hom)
    (a : ∀ U : X.affineOpens, Γ(X, U.1))
    (ha : ∀ (U U' : X.affineOpens) (h : U'.1 ≤ U.1),
      (X.presheaf.map (homOfLE h).op).hom (a U) = a U') :
    ∃ c : R, ∀ U : X.affineOpens,
      a U = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  obtain ⟨𝒳⟩ := Scheme.OrderedAffineCover.nonempty_of_compactSpace X
  letI := Scheme.OrderedAffineCoverOf.moduleSections fX

  have hKaff : ∀ {b : ℕ} (t : 𝒳.Idx b), IsAffineOpen (𝒳.toCoverOf.inter t) :=
    fun t => Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t
  let A : ∀ {b : ℕ}, 𝒳.Idx b → X.affineOpens := fun t => ⟨𝒳.toCoverOf.inter t, hKaff t⟩
  have hRaff : ∀ (U : X.affineOpens) {b : ℕ} (t : (𝒳.restrict fX U.2).Idx b),
      IsAffineOpen ((𝒳.restrict fX U.2).inter t) := by
    intro U b t
    rw [restrict_inter]
    exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated fX
      (Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t) U.2
  let A' : ∀ (U : X.affineOpens) {b : ℕ}, (𝒳.restrict fX U.2).Idx b → X.affineOpens :=
    fun U {b} t => ⟨(𝒳.restrict fX U.2).inter t, hRaff U t⟩

  have hmem : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.ker (𝒳.toCoverOf.d fX 0) := by
    rw [LinearMap.mem_ker]
    funext s
    rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
    have hj : ∀ j : Fin (0 + 2),
        rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j))) = a (A s) :=
      fun j => ha (A (𝒳.toCoverOf.face s j)) (A s) (𝒳.toCoverOf.inter_le_inter_face s j)
    calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j)))
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • a (A s) := Finset.sum_congr rfl fun j _ => by rw [hj]
      _ = 0 := by rw [Fin.sum_univ_two]; simp
  have hrange : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.range (𝒳.toCoverOf.aug fX) := by
    rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
    exact hmem
  obtain ⟨sec, hsec⟩ := hrange

  obtain ⟨c, hc⟩ := hX.2 sec
  refine ⟨c, fun U => ?_⟩
  have hsU : (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
      = rr (le_top : U.1 ≤ ⊤) sec := by
    rw [← hc]
    rfl
  rw [hsU]

  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective fX (𝒳.restrict fX U.2)
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Scheme.OrderedAffineCoverOf.aug_apply]
  change rr _ (a U) = rr _ (rr _ sec)
  have hle1 : (𝒳.restrict fX U.2).inter t ≤ 𝒳.toCoverOf.inter t := by
    rw [restrict_inter]; exact inf_le_left
  have h1 : rr ((𝒳.restrict fX U.2).inter_le_base t) (a U) = a (A' U t) := ha U (A' U t) _
  have h2 : rr hle1 (a (A t)) = a (A' U t) := ha (A t) (A' U t) hle1
  have h3 : rr (𝒳.toCoverOf.inter_le_base t) sec = a (A t) := congrFun hsec t
  rw [h1, rr_rr, ← h2, ← h3, rr_rr]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.Scheme.exists_forall_eq_appLE_of_forall_map_eq_of_bijective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact fX] [IsSeparated fX]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ fX.appTop).hom)
    (a : ∀ U : X.affineOpens, Γ(X, U.1))
    (ha : ∀ (U U' : X.affineOpens) (h : U'.1 ≤ U.1),
      (X.presheaf.map (homOfLE h).op).hom (a U) = a U') :
    ∃ c : R, ∀ U : X.affineOpens,
      a U = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct


namespace G5Body

section Alg

variable {k : Type u} [Field k]
  {C0 C1 C2 : Type u} [AddCommGroup C0] [Module k C0] [AddCommGroup C1] [Module k C1]
  [AddCommGroup C2] [Module k C2]
  (d0 : C0 →ₗ[k] C1) (d1 : C1 →ₗ[k] C2)

abbrev ZZ : Submodule k C1 := LinearMap.ker d1

abbrev BB : Submodule k (ZZ d1) := (LinearMap.range d0).comap (ZZ d1).subtype

abbrev HH : Type u := ZZ d1 ⧸ BB d0 d1

theorem exists_r : ∃ r : C1 →ₗ[k] HH d0 d1, r ∘ₗ (ZZ d1).subtype = (BB d0 d1).mkQ :=
  LinearMap.exists_extend _

variable (r : C1 →ₗ[k] HH d0 d1) (hr : r ∘ₗ (ZZ d1).subtype = (BB d0 d1).mkQ)
  (hdd : d1 ∘ₗ d0 = 0)
include hr in
theorem r_apply_of_mem (z : C1) (hz : z ∈ ZZ d1) : r z = (BB d0 d1).mkQ ⟨z, hz⟩ := by
  have := LinearMap.congr_fun hr ⟨z, hz⟩
  simpa using this

include hr hdd in
theorem r_comp_d0 : r ∘ₗ d0 = 0 := by
  ext c
  have hz : d0 c ∈ ZZ d1 := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, r_apply_of_mem d0 d1 r hr _ hz,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨c, rfl⟩

variable (A : Type u) [AddCommGroup A] [Module k A]

abbrev cl : A ⊗[k] C1 →ₗ[k] A ⊗[k] HH d0 d1 := LinearMap.lTensor A r

include hr hdd in
theorem cl_lTensor_d0 (w : A ⊗[k] C0) : cl d0 d1 r A (LinearMap.lTensor A d0 w) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, r_comp_d0 d0 d1 r hr hdd,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

def d0' : C0 →ₗ[k] BB d0 d1 :=
  LinearMap.codRestrict (BB d0 d1)
    (LinearMap.codRestrict (ZZ d1) d0 (fun c => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]))
    (fun c => ⟨c, rfl⟩)

theorem d0'_surjective : Function.Surjective (d0' d0 d1 hdd) := by
  rintro ⟨⟨z, hz⟩, ⟨c, hc⟩⟩
  exact ⟨c, Subtype.ext (Subtype.ext hc)⟩

theorem subtype_comp_subtype_comp_d0' :
    (ZZ d1).subtype ∘ₗ (BB d0 d1).subtype ∘ₗ d0' d0 d1 hdd = d0 := by
  ext c; rfl

include hr hdd in

theorem exists_of_cl_eq_zero (z : A ⊗[k] C1) (hz : LinearMap.lTensor A d1 z = 0)
    (hcl : cl d0 d1 r A z = 0) : ∃ w : A ⊗[k] C0, LinearMap.lTensor A d0 w = z := by

  have hex1 : Function.Exact (LinearMap.lTensor A (ZZ d1).subtype) (LinearMap.lTensor A d1) :=
    Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map d1)
  obtain ⟨ζ, rfl⟩ := (hex1 z).mp hz

  have hq : LinearMap.lTensor A (BB d0 d1).mkQ ζ = 0 := by
    rw [← hr, LinearMap.lTensor_comp, LinearMap.comp_apply]
    exact hcl
  have hex2 : Function.Exact (LinearMap.lTensor A (BB d0 d1).subtype)
      (LinearMap.lTensor A (BB d0 d1).mkQ) :=
    lTensor_exact A (LinearMap.exact_subtype_mkQ (BB d0 d1)) (Submodule.mkQ_surjective _)
  obtain ⟨β, rfl⟩ := (hex2 ζ).mp hq

  obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective A (d0'_surjective d0 d1 hdd) β
  refine ⟨w, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    ← LinearMap.lTensor_comp, LinearMap.comp_assoc, subtype_comp_subtype_comp_d0']

include hr in

theorem cl_tmul_of_mem (a : A) (z : C1) (hz : z ∈ ZZ d1) :
    cl d0 d1 r A (a ⊗ₜ[k] z) = a ⊗ₜ[k] (BB d0 d1).mkQ ⟨z, hz⟩ := by
  rw [LinearMap.lTensor_tmul, r_apply_of_mem d0 d1 r hr z hz]

theorem map_cl {A' : Type u} [AddCommGroup A'] [Module k A'] (φ : A →ₗ[k] A') (x : A ⊗[k] C1) :
    TensorProduct.map φ LinearMap.id (cl d0 d1 r A x) = cl d0 d1 r A' (TensorProduct.map φ LinearMap.id x) := by
  simp only [LinearMap.lTensor_def, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id]

end Alg

end G5Body

namespace G5Body

section Coord

variable {k : Type u} [Field k] {H : Type u} [AddCommGroup H] [Module k H]
  {Λ : Type u} (bH : Module.Basis Λ k H)

noncomputable def coord (A : Type u) [AddCommGroup A] [Module k A] : A ⊗[k] H ≃ₗ[k] (Λ →₀ A) := by
  classical
  exact (LinearEquiv.lTensor A bH.repr).trans (TensorProduct.finsuppScalarRight k k A Λ)

theorem coord_tmul (A : Type u) [AddCommGroup A] [Module k A] (a : A) (h : H) (l : Λ) :
    coord bH A (a ⊗ₜ[k] h) l = bH.repr h l • a := by
  classical
  simp only [coord, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul,
    TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_apply]
  rw [Finsupp.sum, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; rw [Finsupp.single_apply, if_neg hb]
  · intro hl; simp [Finsupp.notMem_support_iff.mp hl]

theorem coord_map {A A' : Type u} [AddCommGroup A] [Module k A] [AddCommGroup A'] [Module k A']
    (φ : A →ₗ[k] A') (x : A ⊗[k] H) (l : Λ) :
    coord bH A' (TensorProduct.map φ LinearMap.id x) l = φ (coord bH A x l) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a h => rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul, coord_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

end Coord

end G5Body

namespace G5Body

section Generic

variable {P X : Scheme.{u}} (p₁ : P ⟶ X)

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_self {U : P.Opens} (h : U ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), P.presheaf.map_id]; rfl

theorem res_any {U W : P.Opens} (i : op U ⟶ op W) (h : W ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map i).hom x = (P.presheaf.map (homOfLE h).op).hom x := by
  rw [Subsingleton.elim i (homOfLE h).op]

theorem res_appLE {U : X.Opens} {V W : P.Opens} (e : V ≤ p₁ ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(X, U)) :
    (P.presheaf.map (homOfLE h).op).hom ((p₁.appLE U V e).hom y) = (p₁.appLE U W (h.trans e)).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {U U' : X.Opens} {V : P.Opens} (e : V ≤ p₁ ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(X, U')) :
    (p₁.appLE U V e).hom ((X.presheaf.map (homOfLE h).op).hom y)
      = (p₁.appLE U' V (e.trans (p₁.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_of_eq_id (f : X ⟶ X) (hf : f = 𝟙 X) {U V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V ≤ U) (y : Γ(X, U)) :
    (f.appLE U V e).hom y = (X.presheaf.map (homOfLE h).op).hom y := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  change (X.presheaf.map (homOfLE e).op).hom ((𝟙 Γ(X, U) : Γ(X, U) ⟶ Γ(X, U)).hom y) = _
  rw [CommRingCat.id_apply]
  exact res_any _ h y

theorem appLE_top_congr {S : Scheme.{u}} (g g' : P ⟶ S) (hg : g = g') (W : P.Opens) (y : Γ(S, ⊤)) :
    (g.appLE ⊤ W le_top).hom y = (g'.appLE ⊤ W le_top).hom y := by
  subst hg; rfl

end Generic

section Strip

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)

noncomputable def strip (hw : p₁ ≫ fX = p₂ ≫ fY) (U : X.Opens) : OModulePresheaf fY where
  obj V := Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
  addCommGroup _ := inferInstance
  module V := (Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)).toModule
  moduleSections V := Module.compHom _ (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom
  isScalarTower V := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    letI : Module Γ(Y, V) Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) :=
      Module.compHom _ (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom
    refine ⟨fun r a x => ?_⟩
    show (p₂.appLE V _ inf_le_right).hom
          ((fY.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) * a) * x
      = ((p₁ ≫ fX).appLE ⊤ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)
          * ((p₂.appLE V _ inf_le_right).hom a * x)
    rw [map_mul, ← mul_assoc]
    congr 2
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_top_congr (p₂ ≫ fY) (p₁ ≫ fX) hw.symm]
  res h := (OModulePresheaf.unit (p₁ ≫ fX)).res (inf_le_inf_left _ (p₂.preimage_mono h))
  res_smul {V V'} h a x := by
    show (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom
          ((p₂.appLE V' _ inf_le_right).hom a * x)
      = (p₂.appLE V _ inf_le_right).hom ((Y.presheaf.map (homOfLE h).op).hom a)
          * (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := Y.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl V := (OModulePresheaf.unit (p₁ ≫ fX)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p₁ ≫ fX)).res_comp _ _

variable (hw : p₁ ≫ fX = p₂ ≫ fY)

theorem strip_obj (U : X.Opens) (V : Y.Opens) :
    (strip fX fY p₁ p₂ hw U).obj V = Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) := rfl

theorem strip_res_apply (U : X.Opens) {V V' : Y.Opens} (h : V ≤ V') (x : Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V')) :
    (strip fX fY p₁ p₂ hw U).res h (show (strip fX fY p₁ p₂ hw U).obj V' from x)
      = (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom x := rfl

end Strip

end G5Body

namespace G5Body

section Phi

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒱 : Y.OrderedAffineCover)

noncomputable def Φσ (U : X.affineOpens) {n : ℕ} (σ : 𝒱.Idx n) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).obj (𝒱.inter σ)
      ≃ₗ[k] (strip fX fY p₁ p₂ hP.w U.1).obj (𝒱.inter σ) :=
  (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback fX fY p₁ p₂ hP
    U.1 U.2 (𝒱.inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ)).2.choose

theorem Φσ_tmul (U : X.affineOpens) {n : ℕ} (σ : 𝒱.Idx n) (a : Γ(X, U.1)) (b : Γ(Y, 𝒱.inter σ)) :
    Φσ fX fY p₁ p₂ hP 𝒱 U σ (a ⊗ₜ[k] b)
      = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom b :=
  (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback fX fY p₁ p₂ hP
    U.1 U.2 (𝒱.inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ)).2.choose_spec a b

noncomputable def Φ (U : X.affineOpens) (n : ℕ) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n
      ≃ₗ[k] (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n := by
  classical
  exact (TensorProduct.piRight k k ((OModulePresheaf.unit fX).obj U.1)
    (fun σ : 𝒱.Idx n => (OModulePresheaf.unit fY).obj (𝒱.inter σ))).trans
      (LinearEquiv.piCongrRight (fun σ => Φσ fX fY p₁ p₂ hP 𝒱 U σ))

theorem Φ_tmul (U : X.affineOpens) (n : ℕ) (a : Γ(X, U.1)) (f : (OModulePresheaf.unit fY).cochain 𝒱 n)
    (σ : 𝒱.Idx n) :
    Φ fX fY p₁ p₂ hP 𝒱 U n ((show (OModulePresheaf.unit fX).obj U.1 from a) ⊗ₜ[k] f) σ
      = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom (f σ) := by
  classical
  simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
  exact Φσ_tmul fX fY p₁ p₂ hP 𝒱 U σ a (f σ)

theorem Φ_lTensor_d (U : X.affineOpens) (n : ℕ)
    (w : (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n) :
    Φ fX fY p₁ p₂ hP 𝒱 U (n + 1) (LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 n) w)
      = (strip fX fY p₁ p₂ hP.w U.1).d 𝒱 n (Φ fX fY p₁ p₂ hP 𝒱 U n w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a f =>
    rw [LinearMap.lTensor_tmul]
    funext σ
    erw [Φ_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom
        (((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit fY).res (𝒱.inter_le_inter_face σ j) (f (𝒱.face σ j)))
        = ((-1 : ℤ) ^ (j : ℕ)) • (p₂.appLE (𝒱.inter (𝒱.face σ j)) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)
            (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).hom (f (𝒱.face σ j)) := by
      erw [map_zsmul]
      exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (appLE_res p₂ _ _ _)
    have h2 : (strip fX fY p₁ p₂ hP.w U.1).res (𝒱.inter_le_inter_face σ j)
        (Φ fX fY p₁ p₂ hP 𝒱 U n ((show (OModulePresheaf.unit fX).obj U.1 from a) ⊗ₜ[k] f) (𝒱.face σ j))
        = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter (𝒱.face σ j)) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)
            (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).hom (f (𝒱.face σ j)) := by
      rw [Φ_tmul, strip_res_apply, map_mul, res_appLE, res_appLE]
    erw [h1, h2, mul_smul_comm]

noncomputable def resS {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n) : (strip fX fY p₁ p₂ hP.w U'.1).cochain 𝒱 n :=
  fun σ => (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) (p₁.preimage_mono hle) :
    p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (x σ)

theorem resS_apply {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n) (σ : 𝒱.Idx n) :
    resS fX fY p₁ p₂ hP 𝒱 hle n x σ = (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
      (p₁.preimage_mono hle) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (x σ) :=
  rfl

theorem resS_Φ {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n) :
    resS fX fY p₁ p₂ hP 𝒱 hle n (Φ fX fY p₁ p₂ hP 𝒱 U n x)
      = Φ fX fY p₁ p₂ hP 𝒱 U' n (TensorProduct.map ((OModulePresheaf.unit fX).res hle) LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]; funext σ; rw [resS_apply, Pi.zero_apply, Pi.zero_apply]
    exact (P.presheaf.map _).hom.map_zero
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]; funext σ; simp only [resS_apply, Pi.add_apply]
    exact (P.presheaf.map _).hom.map_add _ _
  | tmul a f =>
    funext σ
    rw [resS_apply, TensorProduct.map_tmul, LinearMap.id_apply, OModulePresheaf.unit_res_apply, Φ_tmul, Φ_tmul,
      map_mul, res_appLE, res_appLE, appLE_res]

end Phi

end G5Body

namespace G5Body

section Eval

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (x₀ : Spec (CommRingCat.of k) ⟶ X)
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
  (𝒱 : Y.OrderedAffineCover) (U₀ : X.affineOpens) (hU₀ : x₀ ⁻¹ᵁ U₀.1 = ⊤)

include fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀

theorem hEle (V : Y.Opens) : V ≤ iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ V) := by
  intro y hy
  refine ⟨?_, ?_⟩
  · show y ∈ (iY ≫ p₁) ⁻¹ᵁ U₀.1
    rw [hiY₁, Scheme.Hom.comp_preimage, hU₀]; trivial
  · show y ∈ (iY ≫ p₂) ⁻¹ᵁ V
    rw [hiY₂]; exact hy

noncomputable def E (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    (OModulePresheaf.unit fY).cochain 𝒱 n :=
  fun σ => (iY.appLE (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (𝒱.inter σ)
    (hEle fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ (𝒱.inter σ))).hom (x σ)

theorem E_apply (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) (σ : 𝒱.Idx n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x σ
      = (iY.appLE (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (𝒱.inter σ)
          (hEle fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ (𝒱.inter σ))).hom (x σ) := rfl

theorem E_sub (n : ℕ) (x y : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n (x - y)
      = E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x - E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n y := by
  funext σ; simp only [E_apply, Pi.sub_apply]; exact map_sub _ _ _

theorem E_d (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ (n + 1) ((strip fX fY p₁ p₂ hP.w U₀.1).d 𝒱 n x)
      = (OModulePresheaf.unit fY).d 𝒱 n (E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x) := by
  funext σ
  rw [E_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  erw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [map_zsmul]
  rw [strip_res_apply, appLE_res, E_apply, OModulePresheaf.unit_res_apply, res_appLE]

theorem E_Φ_one_tmul (n : ℕ) (f : (OModulePresheaf.unit fY).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n
        (Φ fX fY p₁ p₂ hP 𝒱 U₀ n ((show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1))) ⊗ₜ[k] f))
      = f := by
  funext σ
  rw [E_apply, Φ_tmul, map_one, one_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_of_eq_id _ hiY₂ _ le_rfl, res_self]

end Eval

end G5Body

namespace G5Body

section YRes
variable {Y : Scheme.{u}}
theorem resY_res {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x)
      = (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
end YRes

section Assembly

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒱 : Y.OrderedAffineCover)
  (r : (OModulePresheaf.unit fY).cochain 𝒱 1 →ₗ[k]
    HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  {Λ : Type u} (bH : Module.Basis Λ k (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)))
  (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))

noncomputable def ζ (U : X.affineOpens) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 1 :=
  (Φ fX fY p₁ p₂ hP 𝒱 U 1).symm (e U)

theorem Φ_ζ (U : X.affineOpens) : Φ fX fY p₁ p₂ hP 𝒱 U 1 (ζ fX fY p₁ p₂ hP 𝒱 e U) = e U :=
  LinearEquiv.apply_symm_apply _ _

noncomputable def mcl (U : X.affineOpens) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1) :=
  cl _ _ r _ (ζ fX fY p₁ p₂ hP 𝒱 e U)

noncomputable def acoord (U : X.affineOpens) (l : Λ) : (OModulePresheaf.unit fX).obj U.1 :=
  coord bH _ (mcl fX fY p₁ p₂ hP 𝒱 r e U) l

theorem lTensor_d_ζ (U : X.affineOpens)
    (heU : ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0) :
    LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U) = 0 := by
  apply (Φ fX fY p₁ p₂ hP 𝒱 U 2).injective
  rw [Φ_lTensor_d, Φ_ζ, map_zero]
  funext ρ
  rw [OModulePresheaf.d_apply, Pi.zero_apply]
  exact heU ρ

theorem res_acoord (hr : r ∘ₗ (ZZ _).subtype = (BB ((OModulePresheaf.unit fY).d 𝒱 0) _).mkQ)
    {U U' : X.affineOpens} (hle : U'.1 ≤ U.1)
    (g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i))
    (hg : ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (l : Λ) :
    (OModulePresheaf.unit fX).res hle (acoord fX fY p₁ p₂ hP 𝒱 r bH e U l)
      = acoord fX fY p₁ p₂ hP 𝒱 r bH e U' l := by
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0
  have hw : TensorProduct.map ((OModulePresheaf.unit fX).res hle) LinearMap.id (ζ fX fY p₁ p₂ hP 𝒱 e U)
      = ζ fX fY p₁ p₂ hP 𝒱 e U'
        + LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 0) ((Φ fX fY p₁ p₂ hP 𝒱 U' 0).symm g) := by
    apply (Φ fX fY p₁ p₂ hP 𝒱 U' 1).injective
    rw [← resS_Φ, Φ_ζ, map_add, Φ_ζ, Φ_lTensor_d, LinearEquiv.apply_symm_apply]
    funext σ
    change _ = (show (strip fX fY p₁ p₂ hP.w U'.1).obj (𝒱.inter σ) from e U' σ)
      + (strip fX fY p₁ p₂ hP.w U'.1).d 𝒱 0 g σ
    rw [resS_apply, OModulePresheaf.d_apply]
    erw [(sub_eq_iff_eq_add'.mp (hg σ)), add_comm]
  unfold acoord mcl
  rw [← coord_map, map_cl, hw, map_add, cl_lTensor_d0 _ _ r hr hdd, add_zero]

end Assembly

end G5Body

namespace G5Body

section Final

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (x₀ : Spec (CommRingCat.of k) ⟶ X)
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
  (𝒱 : Y.OrderedAffineCover)
  (r : (OModulePresheaf.unit fY).cochain 𝒱 1 →ₗ[k]
    HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  (hr : r ∘ₗ (ZZ _).subtype = (BB ((OModulePresheaf.unit fY).d 𝒱 0) _).mkQ)
  {Λ : Type u} (bH : Module.Basis Λ k (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)))
  (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
  (c : Λ → k)
  (hc : ∀ (l : Λ) (U : X.affineOpens), acoord fX fY p₁ p₂ hP 𝒱 r bH e U l
    = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c l)))
  (U₀ : X.affineOpens) (hU₀ : x₀ ⁻¹ᵁ U₀.1 = ⊤)

include hr hc hU₀ hiY₁ hiY₂

theorem c_eq_zero
    (hzU₀ : LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U₀) = 0)
    (g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)))
    (hg : ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U₀ σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U₀.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j)))
    (l : Λ) : c l = 0 := by
  classical
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0

  haveI : Nontrivial Γ(Spec (CommRingCat.of k), x₀ ⁻¹ᵁ U₀.1) := by rw [hU₀]; infer_instance
  haveI : Nontrivial Γ(X, U₀.1) := RingHom.domain_nontrivial (x₀.app U₀.1).hom
  have hinj : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appLE ⊤ U₀.1 le_top).hom :=
    RingHom.injective _
  have hc0 : ∀ l, acoord fX fY p₁ p₂ hP 𝒱 r bH e U₀ l = 0 → c l = 0 := by
    intro l hl
    apply hinj
    rw [CommRingCat.comp_apply, ← hc l U₀, hl]
    exact (map_zero _).symm

  let f₀ : Λ →₀ k := Finsupp.onFinset (coord bH _ (mcl fX fY p₁ p₂ hP 𝒱 r e U₀)).support (fun l => c l)
    (fun l hl => by
      by_contra h'
      exact hl (hc0 l (Finsupp.notMem_support_iff.mp h')))
  have hf₀ : ∀ l, f₀ l • (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1)))
      = acoord fX fY p₁ p₂ hP 𝒱 r bH e U₀ l := by
    intro l
    rw [Finsupp.onFinset_apply, hc l U₀]
    change (fX.appLE ⊤ U₀.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c l)) * 1 = _
    rw [mul_one]
  have hm₀ : mcl fX fY p₁ p₂ hP 𝒱 r e U₀
      = (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1))) ⊗ₜ[k] bH.repr.symm f₀ := by
    apply (coord bH _).injective
    ext l
    rw [coord_tmul, LinearEquiv.apply_symm_apply, hf₀]
    rfl
  obtain ⟨z₀, hz₀⟩ := Submodule.mkQ_surjective
    (BB ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)) (bH.repr.symm f₀)

  have hcl0 : cl ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1) r _
      (ζ fX fY p₁ p₂ hP 𝒱 e U₀ - (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1))) ⊗ₜ[k] z₀.1) = 0 := by
    rw [map_sub, cl_tmul_of_mem _ _ r hr _ _ z₀.1 z₀.2]
    change mcl fX fY p₁ p₂ hP 𝒱 r e U₀ - _ = 0
    rw [hm₀, ← hz₀, sub_eq_zero]
  have hz0 : LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1)
      (ζ fX fY p₁ p₂ hP 𝒱 e U₀ - (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1))) ⊗ₜ[k] z₀.1) = 0 := by
    rw [map_sub, hzU₀, LinearMap.lTensor_tmul, LinearMap.mem_ker.mp z₀.2, TensorProduct.tmul_zero, sub_zero]
  obtain ⟨w₀, hw₀⟩ := exists_of_cl_eq_zero _ _ r hr hdd _ _ hz0 hcl0

  let ĝ : (OModulePresheaf.unit fY).cochain 𝒱 0 := fun i =>
    (Y.presheaf.map (homOfLE (hEle fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ (𝒱.inter i))).op).hom (g i)
  have hE : E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 1 (e U₀) = (OModulePresheaf.unit fY).d 𝒱 0 ĝ := by
    funext σ
    rw [E_apply, Scheme.Hom.appLE, CommRingCat.comp_apply, hg σ, map_sum, OModulePresheaf.d_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, resY_res, OModulePresheaf.unit_res_apply, resY_res]
  have hkey : z₀.1 = (OModulePresheaf.unit fY).d 𝒱 0
      (ĝ - E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 0 (Φ fX fY p₁ p₂ hP 𝒱 U₀ 0 w₀)) := by
    have h1 := congrArg (Φ fX fY p₁ p₂ hP 𝒱 U₀ 1) hw₀
    rw [Φ_lTensor_d, map_sub, Φ_ζ] at h1
    have h2 := congrArg (E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 1) h1
    rw [E_d, E_sub, hE, E_Φ_one_tmul] at h2
    rw [map_sub, h2, sub_sub_cancel]
  have hB : z₀ ∈ BB ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1) := ⟨_, hkey.symm⟩
  have hh₀ : bH.repr.symm f₀ = 0 := by rw [← hz₀]; exact (Submodule.Quotient.mk_eq_zero _).mpr hB
  have hf₀0 : f₀ = 0 := by
    have : bH.repr (bH.repr.symm f₀) = f₀ := LinearEquiv.apply_symm_apply _ _
    rw [← this, hh₀, map_zero]
  have : f₀ l = c l := Finsupp.onFinset_apply
  rw [← this, hf₀0, Finsupp.zero_apply]

end Final

end G5Body

namespace G5Body

theorem main
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j))  := by
  classical
  obtain ⟨r, hr⟩ := exists_r ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0
  let bH := Module.Free.chooseBasis k
    (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  have hz : ∀ U : X.affineOpens,
      LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U) = 0 :=
    fun U => lTensor_d_ζ fX fY p₁ p₂ hP 𝒱 e U (he U)
  have hcoord : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1) (l : _),
      (OModulePresheaf.unit fX).res hle (acoord fX fY p₁ p₂ hP 𝒱 r bH e U l)
        = acoord fX fY p₁ p₂ hP 𝒱 r bH e U' l := by
    intro U U' hle l
    obtain ⟨g, hg⟩ := hcompat U U' hle
    exact res_acoord fX fY p₁ p₂ hP 𝒱 r bH e hr hle g hg l
  have hconst : ∀ l, ∃ c : k, ∀ U : X.affineOpens, acoord fX fY p₁ p₂ hP 𝒱 r bH e U l
      = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
    fun l => AlgebraicGeometry.Scheme.exists_forall_eq_appLE_of_forall_map_eq_of_bijective fX hX
      (fun U => acoord fX fY p₁ p₂ hP 𝒱 r bH e U l) (fun U U' h => hcoord U U' h l)
  choose c hc using hconst

  let pt : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨U₀', hU₀'aff, hmem, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X))
      (show x₀.base pt ∈ (⊤ : X.Opens) from trivial)
  have hU₀ : x₀ ⁻¹ᵁ U₀' = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have : y = pt := Subsingleton.elim _ _
    rw [this]; exact hmem
  obtain ⟨g, hg⟩ := hslice ⟨U₀', hU₀'aff⟩ hU₀
  have hall : ∀ l, c l = 0 :=
    c_eq_zero fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 r hr bH e c hc ⟨U₀', hU₀'aff⟩ hU₀ (hz _) g hg

  intro U
  have hmU : mcl fX fY p₁ p₂ hP 𝒱 r e U = 0 := by
    apply (coord bH _).injective
    ext l
    change acoord fX fY p₁ p₂ hP 𝒱 r bH e U l = _
    rw [map_zero, Finsupp.zero_apply, hc l U, hall l, map_zero, map_zero]
  obtain ⟨w, hw⟩ := exists_of_cl_eq_zero _ _ r hr hdd _ (ζ fX fY p₁ p₂ hP 𝒱 e U) (hz U) hmU
  refine ⟨Φ fX fY p₁ p₂ hP 𝒱 U 0 w, fun σ => ?_⟩
  have h1 := congrArg (Φ fX fY p₁ p₂ hP 𝒱 U 1) hw
  rw [Φ_lTensor_d, Φ_ζ] at h1
  rw [← h1, OModulePresheaf.d_apply]
  rfl

end G5Body

theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by
  exact G5Body.main fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 e he hcompat hslice
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by
  classical
  have h1 : ∀ U' : X.affineOpens, _ := fun U' =>
    AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c hc U'.1 U'.2
  choose γ e hV hH hZ using h1
  have h5 := AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ (𝒲.comap iY) e hZ
    (fun U₁ U₂ hle => AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
      fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c U₁.1 U₁.2 (γ U₁) (e U₁) (hV U₁) (hH U₁)
      U₂.1 U₂.2 hle (γ U₂) (e U₂) (hV U₂) (hH U₂))
    (fun U₁ hU₁ => AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
      fX fY x₀ p₁ p₂ iY hiY₁ hiY₂ 𝒲 c hcY U₁.1 hU₁ (γ U₁) (e U₁) (hV U₁) (hH U₁))
  have hg := h5 ⟨U, hU⟩
  exact AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
    fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c U hU (γ ⟨U, hU⟩) (e ⟨U, hU⟩) (hV ⟨U, hU⟩) (hH ⟨U, hU⟩) hg
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iX : X ⟶ P) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 X) (hiX₂ : iX ≫ p₂ = fX ≫ y₀)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcX : ∃ b : (OModulePresheaf.unit fX).cochain (𝒲.comap iX) 0,
      (OModulePresheaf.unit fX).d (𝒲.comap iX) 0 b = fun s =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le iX s)).op).hom ((iX.app (𝒲.inter s)).hom (c s)))
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s))) :
    ∃ b : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 0, (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 0 b = c := by
  haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)
  haveI : IsSeparated (p₁ ≫ fX) := inferInstance
  exact AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
    fX p₁ iX hiX₁
    (fun U hU => (AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
      fX fY hY p₁ p₂ hP U hU).2)
    𝒲 c hc
    (fun i => AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
      fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒲 c hc hcY (iX ⁻¹ᵁ 𝒲.U i) ((𝒲.isAffineOpen i).preimage iX))
    hcX
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iX : X ⟶ P) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 X) (hiX₂ : iX ≫ p₂ = fX ≫ y₀)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcX : ∃ b : (OModulePresheaf.unit fX).cochain (𝒲.comap iX) 0,
      (OModulePresheaf.unit fX).d (𝒲.comap iX) 0 b = fun s =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le iX s)).op).hom ((iX.app (𝒲.inter s)).hom (c s)))
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s))) :
    ∃ b : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 0, (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 0 b = c := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback

set_option autoImplicit false


namespace DCommAux

open Equiv

section Comb

variable {ι : Type*} [LinearOrder ι] {n : ℕ}

theorem units_pow_mul_self (m : ℕ) : ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := Int.units_mul_self _

theorem sorted_face_apply (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) (k : Fin n) :
    (u ∘ j.succAbove) (Tuple.sort (u ∘ j.succAbove) k) = (u ∘ Tuple.sort u) (((Tuple.sort u).symm j).succAbove k) := by
  show u (j.succAbove (Tuple.sort (u ∘ j.succAbove) k)) = u (Tuple.sort u (((Tuple.sort u).symm j).succAbove k))
  rw [Tuple.succAbove_sort_comp_succAbove_eq u hu j k]

theorem sign_sort_face (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) :
    Equiv.Perm.sign (Tuple.sort (u ∘ j.succAbove)) =
      (-1) ^ ((((Tuple.sort u).symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign (Tuple.sort u) := by
  set σ := Tuple.sort u with hσ
  set i := σ.symm j with hi
  have hσi : σ i = j := by rw [hi, Equiv.apply_symm_apply]
  obtain ⟨τ, hτ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq σ i
  rw [hσi] at hτ hsign
  have hτeq : τ = Tuple.sort (u ∘ j.succAbove) := by
    refine Equiv.ext fun k => ?_
    apply Fin.succAbove_right_injective (p := j)
    show j.succAbove (τ k) = j.succAbove (Tuple.sort (u ∘ j.succAbove) k)
    rw [← hτ k, Tuple.succAbove_sort_comp_succAbove_eq u hu j k]
  rw [← hτeq, hsign, ← mul_assoc, units_pow_mul_self, one_mul]

theorem collision (u : Fin (n + 1) → ι) {a b : Fin (n + 1)} (hab : a ≠ b) (huab : u a = u b)
    (ha : Function.Injective (u ∘ a.succAbove)) :
    Function.Injective (u ∘ b.succAbove) ∧
    (u ∘ b.succAbove) ∘ Tuple.sort (u ∘ b.succAbove) = (u ∘ a.succAbove) ∘ Tuple.sort (u ∘ a.succAbove) ∧
    Equiv.Perm.sign (Tuple.sort (u ∘ b.succAbove)) = -((-1) ^ ((a : ℕ) + (b : ℕ)) * Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove))) := by
  obtain ⟨π, hπ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq (Equiv.swap a b) b
  rw [Equiv.swap_apply_right] at hπ hsign

  have hcomp : u ∘ b.succAbove = (u ∘ a.succAbove) ∘ π := by
    funext k
    show u (b.succAbove k) = u (a.succAbove (π k))
    rw [← hπ k]
    by_cases hk : b.succAbove k = a
    · rw [hk, Equiv.swap_apply_left, huab]
    · rw [Equiv.swap_apply_of_ne_of_ne hk (Fin.succAbove_ne b k)]
  have hinjb : Function.Injective (u ∘ b.succAbove) := by rw [hcomp]; exact ha.comp π.injective
  refine ⟨hinjb, ?_, ?_⟩
  · rw [hcomp]; exact Tuple.comp_perm_comp_sort_eq_comp_sort
  ·
    have hsort : π⁻¹ * Tuple.sort (u ∘ a.succAbove) = Tuple.sort (u ∘ b.succAbove) := by
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · rw [hcomp]
        intro x y hxy
        show ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) x) ≤ ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) y)
        have hππ : ∀ z, π (π⁻¹ z) = z := fun z => Equiv.apply_symm_apply π z
        simp only [Function.comp_apply, Equiv.Perm.coe_mul, hππ]
        exact Tuple.monotone_sort (u ∘ a.succAbove) hxy
      · intro x y hxy heq
        exact absurd ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)).injective (hinjb heq) ▸ hxy) (lt_irrefl _)
    rw [← hsort, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab] at *

    have hπs : Equiv.Perm.sign π = -((-1) ^ ((a : ℕ) + (b : ℕ))) := by
      have := hsign
      rw [add_comm] at this
      calc Equiv.Perm.sign π = ((-1) ^ ((a : ℕ) + (b : ℕ)) * (-1) ^ ((a : ℕ) + (b : ℕ))) * Equiv.Perm.sign π := by
            rw [units_pow_mul_self, one_mul]
        _ = (-1) ^ ((a : ℕ) + (b : ℕ)) * -1 := by rw [mul_assoc, ← this]
        _ = -((-1) ^ ((a : ℕ) + (b : ℕ))) := mul_neg_one _
    rw [hπs, neg_mul]

theorem exists_partner (u : Fin (n + 1) → ι) (hu : ¬ Function.Injective u) {a : Fin (n + 1)}
    (ha : Function.Injective (u ∘ a.succAbove)) :
    ∃ b, b ≠ a ∧ u a = u b ∧ ∀ c, c ≠ a → c ≠ b → ¬ Function.Injective (u ∘ c.succAbove) := by

  have : ∃ x y, x ≠ y ∧ u x = u y := by
    by_contra h; push Not at h; exact hu fun x y hxy => by_contra fun hne => h x y hne hxy
  obtain ⟨x, y, hxy, huxy⟩ := this

  have key : ∀ x y, x ≠ y → u x = u y → x = a ∨ y = a := by
    intro x y hxy huxy
    by_contra h; push Not at h
    obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq h.1
    obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq h.2
    have : x' = y' := ha (by show u (a.succAbove x') = u (a.succAbove y'); rw [hx', hy', huxy])
    exact hxy (by rw [← hx', ← hy', this])

  have hb : ∃ b, b ≠ a ∧ u a = u b := by
    rcases key x y hxy huxy with rfl | rfl
    · exact ⟨y, hxy.symm, huxy⟩
    · exact ⟨x, hxy, huxy.symm⟩
  obtain ⟨b, hba, huab⟩ := hb
  refine ⟨b, hba, huab, fun c hca hcb hinj => ?_⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hca.symm
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hcb.symm
  have : a' = b' := hinj (by show u (c.succAbove a') = u (c.succAbove b'); rw [ha', hb', huab])
  exact hba (by rw [← hb', ← ha', this])

end Comb

end DCommAux

namespace DCommAux
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

section Sheaf

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) {m : ℕ} (z : (OModulePresheaf.unit πY).cochain 𝒦 m)

noncomputable def pb (T : 𝒦.Idx m) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) : Γ(X, W) :=
  (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter T)).hom (z T))

theorem map_pb (T : 𝒦.Idx m) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ 𝒦.inter T) :
    (X.presheaf.map (homOfLE hW').op).hom (pb h 𝒦 z T W hW) = pb h 𝒦 z T W' hW'' := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem pb_congr {T T' : 𝒦.Idx m} (e : T = T') (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W ≤ h ⁻¹ᵁ 𝒦.inter T') :
    pb h 𝒦 z T W hW = pb h 𝒦 z T' W hW' := by
  subst e; rfl

theorem map_app_map_eq_pb (S : 𝒦.Idx (m + 1)) (i : Fin (m + 2)) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter S) :
    (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter S)).hom
      ((Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face S i)).op).hom (z (𝒦.face S i)))) =
      pb h 𝒦 z (𝒦.face S i) W (hW.trans (h.preimage_mono (𝒦.inter_le_inter_face S i))) := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality_assoc, ← X.presheaf.map_comp,
    ← CommRingCat.comp_apply]
  rfl

end Sheaf

theorem val_negOne_pow (m : ℕ) : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  have h1 : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) ^ m := Units.val_pow_eq_pow_val _ _
  rw [h1, Units.val_neg, Units.val_one]

end DCommAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

open DCommAux in
theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).d 𝒲 n (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).d 𝒦 n z) := by
  classical
  funext s
  rw [OModulePresheaf.d_apply]

  have hterm : ∀ (j : Fin (n + 2)) (hj : Function.Injective (lam ∘ (𝒲.face s j).1)),
      (OModulePresheaf.unit πX).res (𝒲.inter_le_inter_face s j)
        (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z (𝒲.face s j)) =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ (𝒲.face s j).1)) : ℤˣ) : ℤ) •
        pb h 𝒦 z (𝒲.sortIdx 𝒦 lam (𝒲.face s j) hj) (𝒲.inter s)
          ((𝒲.inter_le_inter_face s j).trans (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam (𝒲.face s j) hj)) := by
    intro j hj
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n z _ hj]
    show (X.presheaf.map (homOfLE (𝒲.inter_le_inter_face s j)).op).hom (_ • _) = _
    rw [map_zsmul]
    congr 1
    exact map_pb h 𝒦 z _ _ _ _
  have hterm0 : ∀ (j : Fin (n + 2)) (hj : ¬ Function.Injective (lam ∘ (𝒲.face s j).1)),
      (OModulePresheaf.unit πX).res (𝒲.inter_le_inter_face s j)
        (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z (𝒲.face s j)) = 0 := by
    intro j hj
    rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n z _ hj]
    exact map_zero _
  by_cases hinj : Function.Injective (lam ∘ s.1)
  ·
    set σ := Tuple.sort (lam ∘ s.1) with hσ
    set S := 𝒲.sortIdx 𝒦 lam s hinj with hS
    have hle : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter S := 𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj
    have hfinj : ∀ j : Fin (n + 2), Function.Injective (lam ∘ (𝒲.face s j).1) := fun j =>
      hinj.comp Fin.succAbove_right_injective

    have hface : ∀ j : Fin (n + 2), 𝒲.sortIdx 𝒦 lam (𝒲.face s j) (hfinj j) = 𝒦.face S (σ.symm j) := by
      intro j
      apply Subtype.ext
      funext k
      show ((lam ∘ (s.1 ∘ Fin.succAbove j)) ∘ Tuple.sort (lam ∘ (s.1 ∘ Fin.succAbove j))) k =
        (((lam ∘ s.1) ∘ Tuple.sort (lam ∘ s.1)) ∘ Fin.succAbove (σ.symm j)) k
      exact sorted_face_apply (lam ∘ s.1) hinj j k
    have hleS : ∀ i, 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter (𝒦.face S i) := fun i => hle.trans (h.preimage_mono (𝒦.inter_le_inter_face S i))

    have hL : ∀ j : Fin (n + 2),
        (-1 : ℤ) ^ (j : ℕ) • (OModulePresheaf.unit πX).res (𝒲.inter_le_inter_face s j)
          (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z (𝒲.face s j)) =
        ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
          pb h 𝒦 z (𝒦.face S (σ.symm j)) (𝒲.inter s) (hleS (σ.symm j)) := by
      intro j
      rw [hterm j (hfinj j), pb_congr h 𝒦 z (hface j) _ _ (hleS (σ.symm j)),
        show Tuple.sort (lam ∘ (𝒲.face s j).1) = Tuple.sort ((lam ∘ s.1) ∘ j.succAbove) from rfl,
        sign_sort_face (lam ∘ s.1) hinj j]
      show (-1 : ℤ) ^ (j : ℕ) • ((_ : ℤ) • pb h 𝒦 z (𝒦.face S (σ.symm j)) (𝒲.inter s) (hleS (σ.symm j))) = _
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hL j)]

    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) _ s hinj, OModulePresheaf.d_apply]
    symm
    show ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter S)).hom
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face S i)).op).hom (z (𝒦.face S i)))) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
          pb h 𝒦 z (𝒦.face S (σ.symm j)) (𝒲.inter s) (hleS (σ.symm j))
    rw [map_sum, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv σ _ _ fun i => ?_
    rw [map_zsmul, map_zsmul, map_app_map_eq_pb h 𝒦 z S i (𝒲.inter s) hle, smul_smul, Equiv.symm_apply_apply]
    congr 1
    rw [Units.val_mul, val_negOne_pow, pow_add]

    have h2 : ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) * ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-((-1 : ℤ) ^ (i : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) * h2
  ·
    rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) _ s hinj]
    by_cases hnone : ∀ j : Fin (n + 2), ¬ Function.Injective (lam ∘ (𝒲.face s j).1)
    · exact Finset.sum_eq_zero fun j _ => by rw [hterm0 j (hnone j), smul_zero]
    push Not at hnone
    obtain ⟨a, ha⟩ := hnone
    obtain ⟨b, hba, huab, hothers⟩ := exists_partner (lam ∘ s.1) hinj (a := a) ha
    obtain ⟨hb, hsorted, hsignb⟩ := collision (lam ∘ s.1) hba.symm huab ha
    rw [Fintype.sum_eq_add a b hba.symm (fun c hc => by rw [hterm0 c (hothers c hc.1 hc.2), smul_zero]),
      hterm a ha, hterm b hb]
    have hidx : 𝒲.sortIdx 𝒦 lam (𝒲.face s b) hb = 𝒲.sortIdx 𝒦 lam (𝒲.face s a) ha := by
      apply Subtype.ext
      exact hsorted
    have hlea : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam (𝒲.face s a) ha) :=
      (𝒲.inter_le_inter_face s a).trans (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam (𝒲.face s a) ha)
    rw [pb_congr h 𝒦 z hidx _ _ hlea]
    show (-1 : ℤ) ^ (a : ℕ) • (((Equiv.Perm.sign (Tuple.sort ((lam ∘ s.1) ∘ a.succAbove)) : ℤˣ) : ℤ) •
          pb h 𝒦 z (𝒲.sortIdx 𝒦 lam (𝒲.face s a) ha) (𝒲.inter s) hlea) +
        (-1 : ℤ) ^ (b : ℕ) • (((Equiv.Perm.sign (Tuple.sort ((lam ∘ s.1) ∘ b.succAbove)) : ℤˣ) : ℤ) •
          pb h 𝒦 z (𝒲.sortIdx 𝒦 lam (𝒲.face s a) ha) (𝒲.inter s) hlea) = 0
    rw [smul_smul, smul_smul, ← add_smul, hsignb, Units.val_neg, Units.val_mul, val_negOne_pow, pow_add]
    have h2 : ((-1 : ℤ) ^ (b : ℕ)) * ((-1 : ℤ) ^ (b : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have : (-1 : ℤ) ^ (a : ℕ) * ((Equiv.Perm.sign (Tuple.sort ((lam ∘ s.1) ∘ a.succAbove)) : ℤˣ) : ℤ) +
        (-1 : ℤ) ^ (b : ℕ) * -((-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (b : ℕ) * ((Equiv.Perm.sign (Tuple.sort ((lam ∘ s.1) ∘ a.succAbove)) : ℤˣ) : ℤ)) = 0 := by
      linear_combination (-((-1 : ℤ) ^ (a : ℕ)) * ((Equiv.Perm.sign (Tuple.sort ((lam ∘ s.1) ∘ a.succAbove)) : ℤˣ) : ℤ)) * h2
    rw [this, zero_smul]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback -/

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

private theorem AlgebraicGeometry.OModulePresheaf.d_unitPullback
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).d 𝒲 n (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).d 𝒦 n z) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback.solution
/- Adapted from P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero -/

namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero.GoodReductionJacobian"
open scoped TensorProduct DirectSum


namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback"
namespace P2mPrimDeg1
p2m_open "GoodReductionJacobian"

theorem unitPullback_congr {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h h' : X ⟶ Y) (e : h = h') (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h' ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z = OModulePresheaf.unitPullback (πX := πX) h' 𝒲 𝒦 lam hlam' n z := by
  subst e; rfl

theorem unitPullback_const_one {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (j₀ : 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U ((fun _ => j₀) w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 (fun _ => j₀) hlam 1 z = 0 := by
  funext s
  rw [Pi.zero_apply]
  apply OModulePresheaf.unitPullback_apply_of_not_injective
  intro hinj
  have := @hinj 0 1 rfl
  exact absurd this (by decide)

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (0 : (OModulePresheaf.unit πY).cochain 𝒦 n) = 0 := by
  classical
  funext s
  rw [Pi.zero_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · exact OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj

end GoodReductionJacobian.P2mPrimDeg1

open GoodReductionJacobian.P2mPrimDeg1

theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒦.U (lam₃ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 0,
      (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 𝒲 𝒦 lam₃ h₃ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z := by
  classical

  haveI : IsProper f := hA.proper
  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 _)).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  let p₁ := pullback.fst f f
  let p₂ := pullback.snd f f
  let μ : pullback f f ⟶ A := (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
  have hμ : μ ≫ f = pullback.fst f f ≫ f :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

  have hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom := by
    refine GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback hA (RingHom.id k) f (𝟙 A) ?_
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ := by rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

  let iX : A ⟶ pullback f f := pullback.lift (𝟙 A) (f ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  let iY : A ⟶ pullback f f := pullback.lift (f ≫ e) (𝟙 A) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  have hiX₁ : iX ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hiX₂ : iX ≫ pullback.snd f f = f ≫ e := pullback.lift_snd _ _ _
  have hiY₁ : iY ≫ pullback.fst f f = f ≫ e := pullback.lift_fst _ _ _
  have hiY₂ : iY ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion iX := by
    have : IsClosedImmersion (iX ≫ pullback.fst f f) := by rw [hiX₁]; infer_instance
    exact IsClosedImmersion.of_comp iX (pullback.fst f f)
  haveI : IsClosedImmersion iY := by
    have : IsClosedImmersion (iY ≫ pullback.snd f f) := by rw [hiY₂]; infer_instance
    exact IsClosedImmersion.of_comp iY (pullback.snd f f)

  have hone : ∀ (g : A ⟶ Spec (CommRingCat.of k)) (hg : g = f), (⟨f ≫ e, by rw [Category.assoc, he, Category.comp_id]⟩ : SchemeHomOver f f) = L.one f := by
    intro g hg
    have := L.one_natural (𝟙 _) f f (Category.comp_id f)
    rw [← this]
    rfl
  have hμX : iX ≫ μ = 𝟙 A := by
    have hψ : iX ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hiX₁, Category.id_comp]
    have key := L.mul_natural (pullback.fst f f ≫ f) f iX hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have e1 : schemeHomOverComp iX hψ ⟨pullback.fst f f, rfl⟩ = (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) := Subtype.ext hiX₁
    have e2 : schemeHomOverComp iX hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = L.one f := by
      rw [← hone f rfl]; exact Subtype.ext hiX₂
    rw [e1, e2, L.mul_one] at key
    exact congrArg Subtype.val key
  have hμY : iY ≫ μ = 𝟙 A := by
    have hψ : iY ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hiY₁, Category.assoc, he, Category.comp_id]
    have key := L.mul_natural (pullback.fst f f ≫ f) f iY hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have e1 : schemeHomOverComp iY hψ ⟨pullback.fst f f, rfl⟩ = L.one f := by
      rw [← hone f rfl]; exact Subtype.ext hiY₁
    have e2 : schemeHomOverComp iY hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) :=
      Subtype.ext hiY₂
    rw [e1, e2, L.one_mul] at key
    exact congrArg Subtype.val key

  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : 𝒦.ι, e ⁻¹ᵁ 𝒦.U j₀ = ⊤ := by
    have hpt : (e.base (IsLocalRing.closedPoint k) : A) ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒦.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hpt
    obtain ⟨j₀, hj⟩ := hpt
    refine ⟨j₀, eq_top_iff.mpr fun x _ => ?_⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    change e.base x ∈ 𝒦.U j₀
    rw [hx]; exact hj

  set c : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1 :=
    OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲 𝒦 lam₃ h₃ 1 z -
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z -
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z with hcdef
  have hc : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 c = 0 := by
    rw [hcdef, map_sub, map_sub, OModulePresheaf.d_unitPullback, OModulePresheaf.d_unitPullback, OModulePresheaf.d_unitPullback, hz,
      unitPullback_zero, unitPullback_zero, unitPullback_zero, sub_zero, sub_zero]

  have hrestr : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (s : (𝒲.comap i).Idx 1)
      (g₃ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ μ) ⁻¹ᵁ 𝒦.U (lam₃ w))
      (g₁ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ pullback.fst f f) ⁻¹ᵁ 𝒦.U (lam₁ w))
      (g₂ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ pullback.snd f f) ⁻¹ᵁ 𝒦.U (lam₂ w)),
      (A.presheaf.map (homOfLE (𝒲.comap_inter_le i s)).op).hom ((i.app (𝒲.inter s)).hom (c s)) =
        (OModulePresheaf.unitPullback (πX := f) (i ≫ μ) (𝒲.comap i) 𝒦 lam₃ g₃ 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ pullback.fst f f) (𝒲.comap i) 𝒦 lam₁ g₁ 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ pullback.snd f f) (𝒲.comap i) 𝒦 lam₂ g₂ 1 z) s := by
    intro i _ s g₃ g₁ g₂
    rw [hcdef, Pi.sub_apply, Pi.sub_apply]
    erw [map_sub, map_sub, map_sub, map_sub]
    rw [Pi.sub_apply, Pi.sub_apply,
      OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp (pullback.fst f f ≫ f) f f μ i 𝒲 𝒦 lam₃ h₃ g₃,
      OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp (pullback.fst f f ≫ f) f f (pullback.fst f f) i 𝒲 𝒦 lam₁ h₁ g₁,
      OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp (pullback.fst f f ≫ f) f f (pullback.snd f f) i 𝒲 𝒦 lam₂ h₂ g₂]
  have hle_comp : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (g : pullback f f ⟶ A) (lam : 𝒲.ι → 𝒦.ι)
      (hl : ∀ w, 𝒲.U w ≤ g ⁻¹ᵁ 𝒦.U (lam w)) (w : (𝒲.comap i).ι), (𝒲.comap i).U w ≤ (i ≫ g) ⁻¹ᵁ 𝒦.U (lam w) := by
    intro i _ g lam hl w
    change i ⁻¹ᵁ 𝒲.U w ≤ (i ≫ g) ⁻¹ᵁ 𝒦.U (lam w)
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono i (hl w)

  have hslice : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (hiμ : i ≫ μ = 𝟙 A)
      (q q' : pullback f f ⟶ A) (lamq lamq' : 𝒲.ι → 𝒦.ι) (hq : ∀ w, 𝒲.U w ≤ q ⁻¹ᵁ 𝒦.U (lamq w))
      (hq' : ∀ w, 𝒲.U w ≤ q' ⁻¹ᵁ 𝒦.U (lamq' w)),
      i ≫ q = 𝟙 A → i ≫ q' = f ≫ e →
      ∃ b : (OModulePresheaf.unit f).cochain (𝒲.comap i) 0, (OModulePresheaf.unit f).d (𝒲.comap i) 0 b =
        OModulePresheaf.unitPullback (πX := f) (i ≫ μ) (𝒲.comap i) 𝒦 lam₃ (hle_comp i μ lam₃ h₃) 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ q) (𝒲.comap i) 𝒦 lamq (hle_comp i q lamq hq) 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ q') (𝒲.comap i) 𝒦 lamq' (hle_comp i q' lamq' hq') 1 z := by
    intro i _ hiμ q q' lamq lamq' hq hq' hiq hiq'

    have g₃ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₃ w) := fun w => by
      rw [← hiμ]; exact hle_comp i μ lam₃ h₃ w
    have g₁ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lamq w) := fun w => by
      rw [← hiq]; exact hle_comp i q lamq hq w
    have g₂ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (f ≫ e) ⁻¹ᵁ 𝒦.U (lamq' w) := fun w => by
      rw [← hiq']; exact hle_comp i q' lamq' hq' w
    have g₀ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (f ≫ e) ⁻¹ᵁ 𝒦.U ((fun _ => j₀) w) := fun w => by
      rw [Scheme.Hom.comp_preimage, hj₀, Scheme.Hom.preimage_top]; exact le_top
    rw [unitPullback_congr f f (i ≫ μ) (𝟙 A) hiμ _ _ _ _ g₃, unitPullback_congr f f (i ≫ q) (𝟙 A) hiq _ _ _ _ g₁,
      unitPullback_congr f f (i ≫ q') (f ≫ e) hiq' _ _ _ _ g₂]
    obtain ⟨b₁, hb₁⟩ := OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero f f (𝟙 A) (𝒲.comap i) 𝒦
      lam₃ lamq g₃ g₁ z hz
    obtain ⟨b₂, hb₂⟩ := OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero f f (f ≫ e) (𝒲.comap i) 𝒦
      lamq' (fun _ => j₀) g₂ g₀ z hz
    rw [unitPullback_const_one, sub_zero] at hb₂
    exact ⟨b₁ - b₂, by rw [map_sub, hb₁, hb₂]⟩

  haveI : IsAffineHom iX := inferInstance
  haveI : IsAffineHom iY := inferInstance
  obtain ⟨b, hb⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap f f hX hX e he e he
    (pullback.fst f f) (pullback.snd f f) (IsPullback.of_hasPullback f f) iX hiX₁ hiX₂ iY hiY₁ hiY₂ 𝒲 c hc
    (by
      obtain ⟨b, hb⟩ := hslice iX hμX (pullback.fst f f) (pullback.snd f f) lam₁ lam₂ h₁ h₂ hiX₁ hiX₂
      refine ⟨b, ?_⟩
      rw [hb]; funext s
      exact (hrestr iX s _ _ _).symm)
    (by
      obtain ⟨b, hb⟩ := hslice iY hμY (pullback.snd f f) (pullback.fst f f) lam₂ lam₁ h₂ h₁ hiY₂ hiY₁
      refine ⟨b, ?_⟩
      rw [hb]; funext s
      rw [hrestr iY s (hle_comp iY μ lam₃ h₃) (hle_comp iY _ lam₁ h₁) (hle_comp iY _ lam₂ h₂)]
      simp only [Pi.sub_apply]
      exact sub_right_comm _ _ _)
  exact ⟨b, by rw [hb]⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
/- Adapted from Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum


private theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒦.U (lam₃ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 0,
      (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 𝒲 𝒦 lam₃ h₃ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


theorem solution
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  subst hh
  refine ⟨{ toFun := fun z => OModulePresheaf.unitPullback (πX := h ≫ πY) h 𝒲 𝒦 lam hlam n z
            map_add' := ?_
            map_smul' := ?_ }, fun z => rfl⟩
  · intro z₁ z₂
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      erw [map_add, map_add, smul_add]
      try rfl
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, add_zero]
  · intro r z
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.smul_apply, RingHom.id_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom πY (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))
      letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom (h ≫ πY) (𝒲.inter s)
      change (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) • (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (algebraMap R Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) r * (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj)))) =
        algebraMap R Γ(X, 𝒲.inter s) r * ((((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) • (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj))))
      rw [map_mul, map_mul, zsmul_eq_mul, zsmul_eq_mul, mul_left_comm]
      congr 1
      change ((πY.appLE ⊤ (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) le_top ≫ h.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj))).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        ((h ≫ πY).appLE ⊤ (𝒲.inter s) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE]
    · rw [Pi.smul_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, smul_zero]
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback.solution
/- Adapted from Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered -/

set_option autoImplicit false

noncomputable section


namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

private abbrev OIdx (n : ℕ) : Type u := Fin (n + 1) → K.ι

private def ointer {n : ℕ} (t : K.OIdx n) : V.Opens := ⨅ j, K.U (t j)

private theorem inter_eq_ointer {n : ℕ} (s : K.Idx n) : K.inter s = K.ointer s.1 := rfl

private theorem ointer_le {n : ℕ} (t : K.OIdx n) (j : Fin (n + 1)) : K.ointer t ≤ K.U (t j) := iInf_le _ j

private def oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) : K.OIdx n := t ∘ Fin.succAbove j

private theorem oface_apply {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    K.oface t j k = t (j.succAbove k) := rfl

private theorem ointer_le_ointer_oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) :
    K.ointer t ≤ K.ointer (K.oface t j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

private def ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx a := fun j => t ⟨j.1, by omega⟩

private def obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx b := fun j => t ⟨a + j.1, by omega⟩

private theorem ofrontFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (a + 1)) :
    K.ofrontFace a b n h t j = t ⟨j.1, by omega⟩ := rfl

private theorem obackFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (b + 1)) :
    K.obackFace a b n h t j = t ⟨a + j.1, by omega⟩ := rfl

private theorem frontFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.frontFace a b n h s).1 = K.ofrontFace a b n h s.1 := rfl

private theorem backFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.backFace a b n h s).1 = K.obackFace a b n h s.1 := rfl

private theorem ointer_le_ointer_ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.ofrontFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _

private theorem ointer_le_ointer_obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.obackFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _

private def osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) : K.Idx n :=
  ⟨t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp (Tuple.sort t).injective)⟩

private theorem osort_val {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    (K.osort t hinj).1 = t ∘ Tuple.sort t := rfl

private theorem ointer_le_inter_osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.ointer t ≤ K.inter (K.osort t hinj) :=
  le_iInf fun j => iInf_le _ (Tuple.sort t j)

private theorem inter_osort_le_ointer {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.inter (K.osort t hinj) ≤ K.ointer t :=
  le_iInf fun j => (iInf_le _ ((Tuple.sort t).symm j)).trans (by
    change K.U (t (Tuple.sort t ((Tuple.sort t).symm j))) ≤ K.U (t j)
    rw [Equiv.apply_symm_apply])

private theorem ointer_le_preimage_ointer_comp {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (t : 𝒲.OIdx n) : 𝒲.ointer t ≤ h ⁻¹ᵁ 𝒦.ointer (lam ∘ t) := by
  change 𝒲.ointer t ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U (lam (t j)))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  exact le_iInf fun j => (iInf_le (fun i => 𝒲.U (t i)) j).trans (hlam _)

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

private abbrev ocochain (n : ℕ) : Type u := ∀ t : K.OIdx n, F.obj (K.ointer t)

private def od (n : ℕ) : F.ocochain K n →ₗ[R] F.ocochain K (n + 1) :=
  LinearMap.pi fun t => ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.ointer_le_ointer_oface t j)).comp (LinearMap.proj (K.oface t j)))

private theorem od_apply (n : ℕ) (c : F.ocochain K n) (t : K.OIdx (n + 1)) :
    F.od K n c t = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.ointer_le_ointer_oface t j) (c (K.oface t j)) := by
  simp only [od, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

private def ocup (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) : F.ocochain K n :=
  fun t => (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
    • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t))

private theorem ocup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) (t : K.OIdx n) :
    F.ocup K a b n h α β t =
      (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
        • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t)) :=
  rfl

private def ores (n : ℕ) : F.ocochain K n →ₗ[R] F.cochain K n :=
  LinearMap.pi fun s => LinearMap.proj (R := R) (φ := fun t : K.OIdx n => F.obj (K.ointer t)) s.1

private theorem ores_apply (n : ℕ) (c : F.ocochain K n) (s : K.Idx n) : F.ores K n c s = c s.1 := rfl

private def oext (n : ℕ) : F.cochain K n →ₗ[R] F.ocochain K n :=
  LinearMap.pi fun t => by
    classical
    exact if hinj : Function.Injective t then
      ((Equiv.Perm.sign (Tuple.sort t) : ℤˣ) : ℤ) •
        ((F.res (K.ointer_le_inter_osort t hinj)).comp (LinearMap.proj (K.osort t hinj)))
    else 0

private theorem oext_apply_of_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : Function.Injective t) :
    F.oext K n z t = ((Equiv.Perm.sign (Tuple.sort t) : ℤˣ) : ℤ) •
      F.res (K.ointer_le_inter_osort t hinj) (z (K.osort t hinj)) := by
  classical
  simp only [oext, LinearMap.pi_apply, dif_pos hinj, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

private theorem oext_apply_of_not_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : ¬ Function.Injective t) :
    F.oext K n z t = 0 := by
  classical
  simp only [oext, LinearMap.pi_apply, dif_neg hinj, LinearMap.zero_apply]

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

private def ounitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) : (unit πX).ocochain 𝒲 n :=
  fun t => (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
    ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t)))

private theorem ounitPullback_apply (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) (t : 𝒲.OIdx n) :
    ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c t =
      (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
        ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t))) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry

end
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace FHSOL

p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme"

theorem comp_eq
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒲 : X.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (𝒦 : Z.OrderedAffineCover)
    (mu : 𝒲.ι → 𝒱.ι) (lam : 𝒱.ι → 𝒦.ι)
    (hmu : ∀ w, 𝒲.U w ≤ g ⁻¹ᵁ 𝒱.U (mu w)) (hlam : ∀ v, 𝒱.U v ≤ h ⁻¹ᵁ 𝒦.U (lam v))
    (hcomp : ∀ w, 𝒲.U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U ((lam ∘ mu) w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) g 𝒲 𝒱 mu hmu n
        (OModulePresheaf.unitPullback (πX := πY) h 𝒱 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) (g ≫ h) 𝒲 𝒦 (lam ∘ mu) hcomp n z := by
  classical
  funext s

  have happLE : ∀ {A B : Scheme.{u}} (f : A ⟶ B) (U : B.Opens) (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) (x : Γ(B, U)),
      (A.presheaf.map (homOfLE e).op).hom ((f.app U).hom x) = (f.appLE U V e).hom x := by
    intro A B f U V e x
    rfl
  by_cases hinj : Function.Injective ((lam ∘ mu) ∘ s.1)
  ·
    have hinj₁ : Function.Injective (mu ∘ s.1) := by
      intro a b hab
      exact hinj (congrArg lam hab)
    have hinj₂ : Function.Injective (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
      rw [Scheme.OrderedAffineCover.sortIdx_val]
      exact hinj.comp (Tuple.sort (mu ∘ s.1)).injective
    rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₁,
      unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₂]

    have hidx : 𝒱.sortIdx 𝒦 lam (𝒲.sortIdx 𝒱 mu s hinj₁) hinj₂ = 𝒲.sortIdx 𝒦 (lam ∘ mu) s hinj := by
      apply Subtype.ext
      simp only [Scheme.OrderedAffineCover.sortIdx_val]
      exact Tuple.comp_perm_comp_sort_eq_comp_sort (f := (lam ∘ mu) ∘ s.1) (σ := Tuple.sort (mu ∘ s.1))

    have hperm : Tuple.sort ((lam ∘ mu) ∘ s.1) =
        Tuple.sort (mu ∘ s.1) * Tuple.sort (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
      apply DFunLike.coe_injective
      apply hinj.comp_left
      show ((lam ∘ mu) ∘ s.1) ∘ ⇑(Tuple.sort ((lam ∘ mu) ∘ s.1)) =
        ((lam ∘ mu) ∘ s.1) ∘ ⇑(Tuple.sort (mu ∘ s.1) * Tuple.sort (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1))
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]
      have h1 := congrArg Subtype.val hidx
      simp only [Scheme.OrderedAffineCover.sortIdx_val] at h1
      exact h1.symm
    rw [map_zsmul, map_zsmul, smul_smul, hperm, Equiv.Perm.sign_mul, Units.val_mul, mul_comm]
    congr 1
    rw [happLE, happLE, happLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

    have key : ∀ (u u' : 𝒦.Idx n) (huu : u = u') (e : 𝒲.inter s ≤ (g ≫ h) ⁻¹ᵁ 𝒦.inter u)
        (e' : 𝒲.inter s ≤ (g ≫ h) ⁻¹ᵁ 𝒦.inter u'),
        ((g ≫ h).appLE (𝒦.inter u) (𝒲.inter s) e).hom (z u) = ((g ≫ h).appLE (𝒦.inter u') (𝒲.inter s) e').hom (z u') := by
      intro u u' huu e e'
      subst huu
      rfl
    exact key _ _ hidx _ _
  ·
    rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    by_cases hinj₁ : Function.Injective (mu ∘ s.1)
    · have hinj₂ : ¬ Function.Injective (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
        intro h2
        apply hinj
        rw [Scheme.OrderedAffineCover.sortIdx_val, ← Function.comp_assoc] at h2
        exact (Function.Injective.of_comp_iff' _ (Tuple.sort (mu ∘ s.1)).bijective).mp h2
      have h0 : OModulePresheaf.unitPullback (πX := πY) h 𝒱 𝒦 lam hlam n z (𝒲.sortIdx 𝒱 mu s hinj₁) =
          (0 : Γ(Y, 𝒱.inter (𝒲.sortIdx 𝒱 mu s hinj₁))) :=
        unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj₂
      rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₁, h0, map_zero, map_zero, smul_zero]
    · rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj₁]

end FHSOL

theorem solution
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (h' : Y ⟶ Z) (h'' : X ⟶ Z) (hh : h'' = h ≫ h')
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (𝒦' : Z.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (lam' : 𝒦.ι → 𝒦'.ι) (lam'' : 𝒲.ι → 𝒦'.ι) (hlc : lam'' = lam' ∘ lam)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ i, 𝒦.U i ≤ h' ⁻¹ᵁ 𝒦'.U (lam' i))
    (hlam'' : ∀ w, 𝒲.U w ≤ h'' ⁻¹ᵁ 𝒦'.U (lam'' w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦' n) (hz : (OModulePresheaf.unit πZ).d 𝒦' n z = 0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (OModulePresheaf.unitPullback (πX := πY) h' 𝒦 𝒦' lam' hlam' n z) -
        OModulePresheaf.unitPullback (πX := πX) h'' 𝒲 𝒦' lam'' hlam'' n z
      ∈ (show Submodule R'' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by
  subst hh hlc
  rw [FHSOL.comp_eq πX πY πZ h h' 𝒲 𝒦 𝒦' lam lam' hlam hlam' hlam'' n z, sub_self]
  exact Submodule.zero_mem _
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (h' : Y ⟶ Z) (h'' : X ⟶ Z) (hh : h'' = h ≫ h')
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (𝒦' : Z.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (lam' : 𝒦.ι → 𝒦'.ι) (lam'' : 𝒲.ι → 𝒦'.ι) (hlc : lam'' = lam' ∘ lam)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ i, 𝒦.U i ≤ h' ⁻¹ᵁ 𝒦'.U (lam' i))
    (hlam'' : ∀ w, 𝒲.U w ≤ h'' ⁻¹ᵁ 𝒦'.U (lam'' w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦' n) (hz : (OModulePresheaf.unit πZ).d 𝒦' n z = 0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (OModulePresheaf.unitPullback (πX := πY) h' 𝒦 𝒦' lam' hlam' n z) -
        OModulePresheaf.unitPullback (πX := πX) h'' 𝒲 𝒦' lam'' hlam'' n z
      ∈ (show Submodule R'' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_od_oext -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_od_oext

set_option autoImplicit false


namespace OextChainAux

open Equiv

section Comb

variable {ι : Type*} [LinearOrder ι] {n : ℕ}

theorem units_pow_mul_self (m : ℕ) : ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := Int.units_mul_self _

theorem sorted_face_apply (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) (k : Fin n) :
    (u ∘ j.succAbove) (Tuple.sort (u ∘ j.succAbove) k) = (u ∘ Tuple.sort u) (((Tuple.sort u).symm j).succAbove k) := by
  show u (j.succAbove (Tuple.sort (u ∘ j.succAbove) k)) = u (Tuple.sort u (((Tuple.sort u).symm j).succAbove k))
  rw [Tuple.succAbove_sort_comp_succAbove_eq u hu j k]

theorem sign_sort_face (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) :
    Equiv.Perm.sign (Tuple.sort (u ∘ j.succAbove)) =
      (-1) ^ ((((Tuple.sort u).symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign (Tuple.sort u) := by
  set σ := Tuple.sort u with hσ
  set i := σ.symm j with hi
  have hσi : σ i = j := by rw [hi, Equiv.apply_symm_apply]
  obtain ⟨τ, hτ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq σ i
  rw [hσi] at hτ hsign
  have hτeq : τ = Tuple.sort (u ∘ j.succAbove) := by
    refine Equiv.ext fun k => ?_
    apply Fin.succAbove_right_injective (p := j)
    show j.succAbove (τ k) = j.succAbove (Tuple.sort (u ∘ j.succAbove) k)
    rw [← hτ k, Tuple.succAbove_sort_comp_succAbove_eq u hu j k]
  rw [← hτeq, hsign, ← mul_assoc, units_pow_mul_self, one_mul]

theorem collision (u : Fin (n + 1) → ι) {a b : Fin (n + 1)} (hab : a ≠ b) (huab : u a = u b)
    (ha : Function.Injective (u ∘ a.succAbove)) :
    Function.Injective (u ∘ b.succAbove) ∧
    (u ∘ b.succAbove) ∘ Tuple.sort (u ∘ b.succAbove) = (u ∘ a.succAbove) ∘ Tuple.sort (u ∘ a.succAbove) ∧
    Equiv.Perm.sign (Tuple.sort (u ∘ b.succAbove)) = -((-1) ^ ((a : ℕ) + (b : ℕ)) * Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove))) := by
  obtain ⟨π, hπ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq (Equiv.swap a b) b
  rw [Equiv.swap_apply_right] at hπ hsign

  have hcomp : u ∘ b.succAbove = (u ∘ a.succAbove) ∘ π := by
    funext k
    show u (b.succAbove k) = u (a.succAbove (π k))
    rw [← hπ k]
    by_cases hk : b.succAbove k = a
    · rw [hk, Equiv.swap_apply_left, huab]
    · rw [Equiv.swap_apply_of_ne_of_ne hk (Fin.succAbove_ne b k)]
  have hinjb : Function.Injective (u ∘ b.succAbove) := by rw [hcomp]; exact ha.comp π.injective
  refine ⟨hinjb, ?_, ?_⟩
  · rw [hcomp]; exact Tuple.comp_perm_comp_sort_eq_comp_sort
  ·
    have hsort : π⁻¹ * Tuple.sort (u ∘ a.succAbove) = Tuple.sort (u ∘ b.succAbove) := by
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · rw [hcomp]
        intro x y hxy
        show ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) x) ≤ ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) y)
        have hππ : ∀ z, π (π⁻¹ z) = z := fun z => Equiv.apply_symm_apply π z
        simp only [Function.comp_apply, Equiv.Perm.coe_mul, hππ]
        exact Tuple.monotone_sort (u ∘ a.succAbove) hxy
      · intro x y hxy heq
        exact absurd ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)).injective (hinjb heq) ▸ hxy) (lt_irrefl _)
    rw [← hsort, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab] at *

    have hπs : Equiv.Perm.sign π = -((-1) ^ ((a : ℕ) + (b : ℕ))) := by
      have := hsign
      rw [add_comm] at this
      calc Equiv.Perm.sign π = ((-1) ^ ((a : ℕ) + (b : ℕ)) * (-1) ^ ((a : ℕ) + (b : ℕ))) * Equiv.Perm.sign π := by
            rw [units_pow_mul_self, one_mul]
        _ = (-1) ^ ((a : ℕ) + (b : ℕ)) * -1 := by rw [mul_assoc, ← this]
        _ = -((-1) ^ ((a : ℕ) + (b : ℕ))) := mul_neg_one _
    rw [hπs, neg_mul]

theorem exists_partner (u : Fin (n + 1) → ι) (hu : ¬ Function.Injective u) {a : Fin (n + 1)}
    (ha : Function.Injective (u ∘ a.succAbove)) :
    ∃ b, b ≠ a ∧ u a = u b ∧ ∀ c, c ≠ a → c ≠ b → ¬ Function.Injective (u ∘ c.succAbove) := by

  have : ∃ x y, x ≠ y ∧ u x = u y := by
    by_contra h; push Not at h; exact hu fun x y hxy => by_contra fun hne => h x y hne hxy
  obtain ⟨x, y, hxy, huxy⟩ := this

  have key : ∀ x y, x ≠ y → u x = u y → x = a ∨ y = a := by
    intro x y hxy huxy
    by_contra h; push Not at h
    obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq h.1
    obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq h.2
    have : x' = y' := ha (by show u (a.succAbove x') = u (a.succAbove y'); rw [hx', hy', huxy])
    exact hxy (by rw [← hx', ← hy', this])

  have hb : ∃ b, b ≠ a ∧ u a = u b := by
    rcases key x y hxy huxy with rfl | rfl
    · exact ⟨y, hxy.symm, huxy⟩
    · exact ⟨x, hxy, huxy.symm⟩
  obtain ⟨b, hba, huab⟩ := hb
  refine ⟨b, hba, huab, fun c hca hcb hinj => ?_⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hca.symm
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hcb.symm
  have : a' = b' := hinj (by show u (c.succAbove a') = u (c.succAbove b'); rw [ha', hb', huab])
  exact hba (by rw [← hb', ← ha', this])

end Comb

theorem val_negOne_pow (m : ℕ) : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  have h1 : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) ^ m := Units.val_pow_eq_pow_val _ _
  rw [h1, Units.val_neg, Units.val_one]

end OextChainAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover

namespace OextChainMain

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
  (F : OModulePresheaf π) (K : V.OrderedAffineCover) {m : ℕ} (z : F.cochain K m)

noncomputable def qb (T : K.Idx m) (W : V.Opens) (hW : W ≤ K.inter T) : F.obj W := F.res hW (z T)

theorem res_qb (T : K.Idx m) {W W' : V.Opens} (hW : W ≤ K.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ K.inter T) :
    F.res hW' (qb F K z T W hW) = qb F K z T W' hW'' := by
  unfold qb; rw [F.res_res]

theorem qb_congr {T T' : K.Idx m} (e : T = T') (W : V.Opens) (hW : W ≤ K.inter T) (hW' : W ≤ K.inter T') :
    qb F K z T W hW = qb F K z T' W hW' := by
  subst e; rfl

end OextChainMain

open OextChainAux OextChainMain in
theorem od_oext_main
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) := by
  classical
  funext t
  rw [od_apply]
  have hterm : ∀ (j : Fin (n + 2)) (hj : Function.Injective (K.oface t j)),
      F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) =
      ((Equiv.Perm.sign (Tuple.sort (K.oface t j)) : ℤˣ) : ℤ) •
        qb F K z (K.osort (K.oface t j) hj) (K.ointer t)
          ((K.ointer_le_ointer_oface t j).trans (K.ointer_le_inter_osort (K.oface t j) hj)) := by
    intro j hj
    rw [oext_apply_of_injective _ _ _ _ _ hj, map_zsmul]
    congr 1
    exact res_qb F K z _ _ _ _
  have hterm0 : ∀ (j : Fin (n + 2)) (hj : ¬ Function.Injective (K.oface t j)),
      F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) = 0 := by
    intro j hj
    rw [oext_apply_of_not_injective _ _ _ _ _ hj, map_zero]
  by_cases hinj : Function.Injective t
  · set σ := Tuple.sort t with hσ
    set S := K.osort t hinj with hS
    have hle : K.ointer t ≤ K.inter S := K.ointer_le_inter_osort t hinj
    have hfinj : ∀ j : Fin (n + 2), Function.Injective (K.oface t j) := fun j =>
      hinj.comp Fin.succAbove_right_injective
    have hface : ∀ j : Fin (n + 2), K.osort (K.oface t j) (hfinj j) = K.face S (σ.symm j) := by
      intro j
      apply Subtype.ext
      funext k
      show ((t ∘ Fin.succAbove j) ∘ Tuple.sort (t ∘ Fin.succAbove j)) k = ((t ∘ Tuple.sort t) ∘ Fin.succAbove (σ.symm j)) k
      exact sorted_face_apply t hinj j k
    have hleS : ∀ i, K.ointer t ≤ K.inter (K.face S i) := fun i => hle.trans (K.inter_le_inter_face S i)
    have hL : ∀ j : Fin (n + 2),
        (-1 : ℤ) ^ (j : ℕ) • F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) =
        ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
          qb F K z (K.face S (σ.symm j)) (K.ointer t) (hleS (σ.symm j)) := by
      intro j
      rw [hterm j (hfinj j), qb_congr F K z (hface j) _ _ (hleS (σ.symm j)),
        show Tuple.sort (K.oface t j) = Tuple.sort (t ∘ j.succAbove) from rfl, sign_sort_face t hinj j, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hL j)]
    rw [oext_apply_of_injective _ _ _ _ _ hinj, d_apply]
    symm
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv σ _ _ fun i => ?_
    rw [map_zsmul, smul_smul, Equiv.symm_apply_apply]
    rw [show F.res hle (F.res (K.inter_le_inter_face S i) (z (K.face S i))) = qb F K z (K.face S i) (K.ointer t) (hleS i) from
      by unfold qb; rw [F.res_res]]
    congr 1
    rw [Units.val_mul, val_negOne_pow, pow_add]
    have h2 : ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) * ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-((-1 : ℤ) ^ (i : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) * h2
  · rw [oext_apply_of_not_injective _ _ _ _ _ hinj]
    by_cases hnone : ∀ j : Fin (n + 2), ¬ Function.Injective (K.oface t j)
    · exact Finset.sum_eq_zero fun j _ => by rw [hterm0 j (hnone j), smul_zero]
    push Not at hnone
    obtain ⟨a, ha⟩ := hnone
    obtain ⟨b, hba, huab, hothers⟩ := exists_partner t hinj (a := a) ha
    obtain ⟨hb, hsorted, hsignb⟩ := collision t hba.symm huab ha
    rw [Fintype.sum_eq_add a b hba.symm (fun c hc => by rw [hterm0 c (hothers c hc.1 hc.2), smul_zero]),
      hterm a ha, hterm b hb]
    have hidx : K.osort (K.oface t b) hb = K.osort (K.oface t a) ha := by
      apply Subtype.ext
      exact hsorted
    have hlea : K.ointer t ≤ K.inter (K.osort (K.oface t a) ha) :=
      (K.ointer_le_ointer_oface t a).trans (K.ointer_le_inter_osort (K.oface t a) ha)
    rw [qb_congr F K z hidx _ _ hlea]
    show (-1 : ℤ) ^ (a : ℕ) • (((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ) •
          qb F K z (K.osort (K.oface t a) ha) (K.ointer t) hlea) +
        (-1 : ℤ) ^ (b : ℕ) • (((Equiv.Perm.sign (Tuple.sort (t ∘ b.succAbove)) : ℤˣ) : ℤ) •
          qb F K z (K.osort (K.oface t a) ha) (K.ointer t) hlea) = 0
    rw [smul_smul, smul_smul, ← add_smul, hsignb, Units.val_neg, Units.val_mul, val_negOne_pow, pow_add]
    have h2 : ((-1 : ℤ) ^ (b : ℕ)) * ((-1 : ℤ) ^ (b : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have : (-1 : ℤ) ^ (a : ℕ) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ) +
        (-1 : ℤ) ^ (b : ℕ) * -((-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (b : ℕ) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ)) = 0 := by
      linear_combination (-((-1 : ℤ) ^ (a : ℕ)) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ)) * h2
    rw [this, zero_smul]

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) :=
  od_oext_main F K n z
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_od_oext
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_oext -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.od_oext
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_od_oext.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_ores_oext -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_oext

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace DORDProofs
open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

theorem ores_od (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.ores K (n + 1) (F.od K n c) = F.d K n (F.ores K n c) := by
  funext s
  rw [ores_apply, od_apply, d_apply]
  rfl

theorem ores_oext (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z := by
  funext s
  have hinj : Function.Injective s.1 := s.2.injective
  have hsort : Tuple.sort s.1 = Equiv.refl _ := (Tuple.sort_eq_refl_iff_monotone).2 s.2.monotone
  have hs : K.osort s.1 hinj = s := Subtype.ext (by rw [osort_val, hsort]; rfl)
  have key : ∀ (s' : K.Idx n) (e : s' = s) (h₁ : K.ointer s.1 ≤ K.inter s'),
      F.res h₁ (z s') = (show F.obj (K.ointer s.1) from z s) := by
    intro s' e h₁; subst e; exact F.res_refl_apply _ _
  rw [ores_apply, oext_apply_of_injective _ _ _ _ _ hinj, key _ hs, hsort, Equiv.Perm.sign_refl, Units.val_one,
    one_smul]

theorem ores_ocup (F : OModulePresheaf π) (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.ores K n (F.ocup K a b n hn α β) = F.cup K a b n hn ((OModulePresheaf.unit π).ores K a α) (F.ores K b β) := by
  funext s
  rfl

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}}

theorem ores_ounitPullback_oext
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  funext s
  rw [ores_apply, ounitPullback_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [oext_apply_of_injective _ _ _ _ _ hinj, unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1)).op).hom
        ((h.app (𝒦.ointer (lam ∘ s.1))).hom
          (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
            (show Γ(Y, 𝒦.ointer (lam ∘ s.1)) from
              (Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op).hom (z (𝒦.osort (lam ∘ s.1) hinj))))) = _
    rw [map_zsmul, map_zsmul]
    congr 1
    change ((Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op ≫
        h.appLE (𝒦.ointer (lam ∘ s.1)) (𝒲.ointer s.1) (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1))).hom
        (z (𝒦.osort (lam ∘ s.1) hinj)) =
      (h.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj))
    rw [Scheme.Hom.map_appLE]
    rfl
  · rw [oext_apply_of_not_injective _ _ _ _ _ hinj, unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, 𝒦.ointer (lam ∘ s.1)))) = (0 : Γ(X, 𝒲.inter s))
    rw [map_zero, map_zero]

theorem od_ounitPullback
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : (OModulePresheaf.unit πY).ocochain 𝒦 n) :
    (OModulePresheaf.unit πX).od 𝒲 n (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c) =
      OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).od 𝒦 n c) := by
  funext t
  rw [od_apply, ounitPullback_apply, od_apply]
  change _ = (X.presheaf.map _).hom ((h.app _).hom (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (show Γ(Y, 𝒦.ointer (lam ∘ t)) from (OModulePresheaf.unit πY).res (𝒦.ointer_le_ointer_oface (lam ∘ t) j) (c (𝒦.oface (lam ∘ t) j)))))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, ounitPullback_apply]
  change ((-1 : ℤ) ^ (j : ℕ)) • ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.oface t j)) ≫
      X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_oface t j)).op).hom (c (lam ∘ 𝒲.oface t j))) =
    ((-1 : ℤ) ^ (j : ℕ)) • ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_oface (lam ∘ t) j)).op ≫
      h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t))).hom (c (𝒦.oface (lam ∘ t) j))
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem ounitPullback_ocup
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit πY).ocochain 𝒦 a) (β : (OModulePresheaf.unit πY).ocochain 𝒦 b) :
    OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).ocup 𝒦 a b n hn α β) =
      (OModulePresheaf.unit πX).ocup 𝒲 a b n hn
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α)
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β) := by
  funext t
  rw [ounitPullback_apply, ocup_apply, ocup_apply, ounitPullback_apply, ounitPullback_apply]
  change (h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).hom
      ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_ofrontFace a b n hn (lam ∘ t))).op).hom (α (𝒦.ofrontFace a b n hn (lam ∘ t))) *
        (Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_obackFace a b n hn (lam ∘ t))).op).hom (β (𝒦.obackFace a b n hn (lam ∘ t)))) =
    (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_ofrontFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.ofrontFace a b n hn t))).hom (α (lam ∘ 𝒲.ofrontFace a b n hn t))) *
      (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_obackFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.obackFace a b n hn t))).hom (β (lam ∘ 𝒲.obackFace a b n hn t)))
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  rfl

end DORDProofs

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z :=
  DORDProofs.ores_oext F K n z
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_oext
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_oext -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.ores_oext
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_oext.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace DORDProofs
open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

theorem ores_od (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.ores K (n + 1) (F.od K n c) = F.d K n (F.ores K n c) := by
  funext s
  rw [ores_apply, od_apply, d_apply]
  rfl

theorem ores_oext (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z := by
  funext s
  have hinj : Function.Injective s.1 := s.2.injective
  have hsort : Tuple.sort s.1 = Equiv.refl _ := (Tuple.sort_eq_refl_iff_monotone).2 s.2.monotone
  have hs : K.osort s.1 hinj = s := Subtype.ext (by rw [osort_val, hsort]; rfl)
  have key : ∀ (s' : K.Idx n) (e : s' = s) (h₁ : K.ointer s.1 ≤ K.inter s'),
      F.res h₁ (z s') = (show F.obj (K.ointer s.1) from z s) := by
    intro s' e h₁; subst e; exact F.res_refl_apply _ _
  rw [ores_apply, oext_apply_of_injective _ _ _ _ _ hinj, key _ hs, hsort, Equiv.Perm.sign_refl, Units.val_one,
    one_smul]

theorem ores_ocup (F : OModulePresheaf π) (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.ores K n (F.ocup K a b n hn α β) = F.cup K a b n hn ((OModulePresheaf.unit π).ores K a α) (F.ores K b β) := by
  funext s
  rfl

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}}

theorem ores_ounitPullback_oext
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  funext s
  rw [ores_apply, ounitPullback_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [oext_apply_of_injective _ _ _ _ _ hinj, unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1)).op).hom
        ((h.app (𝒦.ointer (lam ∘ s.1))).hom
          (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
            (show Γ(Y, 𝒦.ointer (lam ∘ s.1)) from
              (Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op).hom (z (𝒦.osort (lam ∘ s.1) hinj))))) = _
    rw [map_zsmul, map_zsmul]
    congr 1
    change ((Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op ≫
        h.appLE (𝒦.ointer (lam ∘ s.1)) (𝒲.ointer s.1) (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1))).hom
        (z (𝒦.osort (lam ∘ s.1) hinj)) =
      (h.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj))
    rw [Scheme.Hom.map_appLE]
    rfl
  · rw [oext_apply_of_not_injective _ _ _ _ _ hinj, unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, 𝒦.ointer (lam ∘ s.1)))) = (0 : Γ(X, 𝒲.inter s))
    rw [map_zero, map_zero]

theorem od_ounitPullback
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : (OModulePresheaf.unit πY).ocochain 𝒦 n) :
    (OModulePresheaf.unit πX).od 𝒲 n (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c) =
      OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).od 𝒦 n c) := by
  funext t
  rw [od_apply, ounitPullback_apply, od_apply]
  change _ = (X.presheaf.map _).hom ((h.app _).hom (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (show Γ(Y, 𝒦.ointer (lam ∘ t)) from (OModulePresheaf.unit πY).res (𝒦.ointer_le_ointer_oface (lam ∘ t) j) (c (𝒦.oface (lam ∘ t) j)))))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, ounitPullback_apply]
  change ((-1 : ℤ) ^ (j : ℕ)) • ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.oface t j)) ≫
      X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_oface t j)).op).hom (c (lam ∘ 𝒲.oface t j))) =
    ((-1 : ℤ) ^ (j : ℕ)) • ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_oface (lam ∘ t) j)).op ≫
      h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t))).hom (c (𝒦.oface (lam ∘ t) j))
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem ounitPullback_ocup
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit πY).ocochain 𝒦 a) (β : (OModulePresheaf.unit πY).ocochain 𝒦 b) :
    OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).ocup 𝒦 a b n hn α β) =
      (OModulePresheaf.unit πX).ocup 𝒲 a b n hn
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α)
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β) := by
  funext t
  rw [ounitPullback_apply, ocup_apply, ocup_apply, ounitPullback_apply, ounitPullback_apply]
  change (h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).hom
      ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_ofrontFace a b n hn (lam ∘ t))).op).hom (α (𝒦.ofrontFace a b n hn (lam ∘ t))) *
        (Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_obackFace a b n hn (lam ∘ t))).op).hom (β (𝒦.obackFace a b n hn (lam ∘ t)))) =
    (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_ofrontFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.ofrontFace a b n hn t))).hom (α (lam ∘ 𝒲.ofrontFace a b n hn t))) *
      (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_obackFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.obackFace a b n hn t))).hom (β (lam ∘ 𝒲.obackFace a b n hn t)))
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  rfl

end DORDProofs

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z :=
  DORDProofs.ores_ounitPullback_oext πX πY h 𝒲 𝒦 lam hlam n z
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.ores_ounitPullback_oext
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id
set_option maxHeartbeats 1600000

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace KDCat
p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover"

variable {X : Scheme.{u}} (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι)

def cat {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) : Fin m → 𝔓.ι :=
  fun k => if h : (k : ℕ) < a + 1 then σ.1 ⟨k, h⟩ else lam (τ.1 ⟨k - (a + 1), by omega⟩)

theorem cat_apply_lt {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) (k : Fin m)
    (h : (k : ℕ) < a + 1) : cat 𝔓 𝒲 lam σ τ m hm k = σ.1 ⟨k, h⟩ := by
  simp only [cat, dif_pos h]

theorem cat_apply_ge {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) (k : Fin m)
    (h : ¬ (k : ℕ) < a + 1) : cat 𝔓 𝒲 lam σ τ m hm k = lam (τ.1 ⟨k - (a + 1), by omega⟩) := by
  simp only [cat, dif_neg h]

omit 𝔓 𝒲 lam in
theorem val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).1 = if i.1 < p.1 then i.1 else i.1 + 1 := by
  by_cases hi : Fin.castSucc i < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi, if_pos (by simpa [Fin.lt_def] using hi)]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hi), if_neg (by simpa [Fin.lt_def] using hi)]; rfl

theorem oface_cat_left {a b n : ℕ} (σ : 𝔓.Idx (a + 1)) (τ : 𝒲.Idx b) (hm : a + 1 + b + 2 = n + 3)
    (j : Fin (a + 2)) (hj : (j : ℕ) < n + 3) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (n + 3) hm) ⟨j, hj⟩ = cat 𝔓 𝒲 lam (𝔓.face σ j) τ (n + 2) (by omega) := by
  funext k
  rw [oface_apply]
  have hv : (((⟨j, hj⟩ : Fin (n + 3)).succAbove k) : ℕ) = if (k : ℕ) < j then (k : ℕ) else (k : ℕ) + 1 :=
    val_succAbove _ _
  by_cases hk : (k : ℕ) < a + 1
  · rw [cat_apply_lt _ _ _ _ _ _ _ _ hk, face_val, Function.comp_apply]
    have h1 : ((⟨j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_lt _ _ _ _ _ _ _ _ h1]
    refine congrArg σ.1 (Fin.ext ?_)
    have hv2 := val_succAbove j ⟨(k : ℕ), hk⟩
    simp only [Fin.val_mk] at hv2 ⊢
    split_ifs at hv hv2 <;> omega
  · have h1 : ¬ ((⟨j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_ge _ _ _ _ _ _ _ _ hk, cat_apply_ge _ _ _ _ _ _ _ _ h1]
    refine congrArg lam (congrArg τ.1 (Fin.ext ?_))
    simp only [Fin.val_mk]
    split_ifs at hv <;> omega

theorem oface_cat_right {a b n : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx (b + 1)) (hm : a + (b + 1) + 2 = n + 3)
    (j : Fin (b + 2)) (hj : a + 1 + (j : ℕ) < n + 3) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (n + 3) hm) ⟨a + 1 + j, hj⟩ = cat 𝔓 𝒲 lam σ (𝒲.face τ j) (n + 2) (by omega) := by
  funext k
  rw [oface_apply]
  have hv : (((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k) : ℕ) = if (k : ℕ) < a + 1 + j then (k : ℕ) else (k : ℕ) + 1 :=
    val_succAbove _ _
  by_cases hk : (k : ℕ) < a + 1
  · have h1 : ((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_lt _ _ _ _ _ _ _ _ hk, cat_apply_lt _ _ _ _ _ _ _ _ h1]
    refine congrArg σ.1 (Fin.ext ?_)
    simp only [Fin.val_mk]
    split_ifs at hv <;> omega
  · have h1 : ¬ ((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_ge _ _ _ _ _ _ _ _ hk, cat_apply_ge _ _ _ _ _ _ _ _ h1, face_val, Function.comp_apply]
    refine congrArg lam (congrArg τ.1 (Fin.ext ?_))
    have hv2 := val_succAbove j ⟨(k : ℕ) - (a + 1), by omega⟩
    simp only [Fin.val_mk] at hv2 ⊢
    split_ifs at hv hv2 <;> omega

theorem oface_cat_zero {b : ℕ} (σ : 𝔓.Idx 0) (τ : 𝒲.Idx b) (hm : 0 + b + 2 = b + 2) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (b + 2) hm) 0 = lam ∘ τ.1 := by
  funext k
  rw [oface_apply, Fin.succAbove_zero, cat_apply_ge _ _ _ _ _ _ _ _ (by simp), Function.comp_apply]
  exact congrArg lam (congrArg τ.1 (Fin.ext (by simp)))

theorem oface_cat_last {a : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx 0) (hm : a + 0 + 2 = a + 2) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (a + 2) hm) (Fin.last (a + 1)) = σ.1 := by
  funext k
  rw [oface_apply, Fin.succAbove_last, cat_apply_lt _ _ _ _ _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
  rfl

theorem cat_castSucc {a : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx 0) (hm : a + 0 + 2 = a + 2) (k : Fin (a + 1)) :
    cat 𝔓 𝒲 lam σ τ (a + 2) hm (Fin.castSucc k) = σ.1 k := by
  rw [cat_apply_lt _ _ _ _ _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
  rfl

end KDCat

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.Scheme.OrderedAffineCover KDCat

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 0)),
        OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 0 (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) =
          (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 0 0 => (X.presheaf.map (homOfLE ((inf_le_right :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 0 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
              (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1) :
            OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 0 0)) ∧
    ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
      ∃ h : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n,
        DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n h =
          Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(0, n + 1), by omega⟩
              (OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 (n + 1)
                (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1)) -
            Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(n + 1, 0), by omega⟩
              (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 (n + 1) 0 => (X.presheaf.map (homOfLE ((inf_le_right :
                OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
                  (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1)) := by
  classical

  have hle_cat : ∀ {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m + 1),
      biOpen (𝟙 X) 𝔓 𝒲 a b σ τ ≤ 𝔓.ointer (cat 𝔓 𝒲 lam σ τ (m + 1) hm) := by
    intro a b σ τ m hm
    refine le_iInf fun k => ?_
    by_cases hk : (k : ℕ) < a + 1
    · rw [cat_apply_lt _ _ _ _ _ _ _ _ hk]
      exact inf_le_right.trans ((Scheme.Hom.id_preimage _).le.trans (𝔓.inter_le σ ⟨k, hk⟩))
    · rw [cat_apply_ge _ _ _ _ _ _ _ _ hk]
      exact inf_le_left.trans ((𝒲.inter_le τ _).trans ((hlam _).trans (Scheme.Hom.id_preimage _).le))

  have hpb : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (τ : 𝒲.Idx m),
      OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z τ =
        (OModulePresheaf.unit (𝟙 X ≫ π)).res ((𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ.1).trans (Scheme.Hom.id_preimage _).le)
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 m z (lam ∘ τ.1)) := by
    intro m z τ
    rw [← ores_ounitPullback_oext (𝟙 X ≫ π) (𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z, ores_apply, ounitPullback_apply,
      Scheme.Hom.id_app]
    rfl

  have resc : ∀ {m : ℕ} (ζ : (OModulePresheaf.unit (𝟙 X ≫ π)).ocochain 𝔓 m) (t t' : 𝔓.OIdx m) (e : t = t') {U : X.Opens}
      (h : U ≤ 𝔓.ointer t) (h' : U ≤ 𝔓.ointer t'), (OModulePresheaf.unit (𝟙 X ≫ π)).res h (ζ t) = (OModulePresheaf.unit (𝟙 X ≫ π)).res h' (ζ t') := by
    intro m ζ t t' e U h h'; subst e; rfl

  have hcoc : ∀ {m : ℕ} (ζ : (OModulePresheaf.unit (𝟙 X ≫ π)).ocochain 𝔓 m) (hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 m ζ = 0) (t : 𝔓.OIdx (m + 1)) {U : X.Opens}
      (hU : U ≤ 𝔓.ointer t),
      ∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hU.trans (𝔓.ointer_le_ointer_oface t k)) (ζ (𝔓.oface t k)) = 0 := by
    intro m ζ hζ t U hU
    have h0 := congrArg ((OModulePresheaf.unit (𝟙 X ≫ π)).res hU) (congrFun hζ t)
    rw [od_apply, map_sum, Pi.zero_apply, map_zero] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, OModulePresheaf.res_res]

  have hzσ : ∀ {m : ℕ} (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (σ : 𝔓.Idx m), z σ = (OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 m z σ.1 := by
    intro m z σ
    conv_lhs => rw [← ores_oext (OModulePresheaf.unit (𝟙 X ≫ π)) 𝔓 m z]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro z
    funext στ
    obtain ⟨σ, τ⟩ := στ
    have hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 0 ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 0 z.1) = 0 := by
      rw [od_oext, LinearMap.mem_ker.1 z.2, map_zero]
    have hc := hcoc _ hζ (cat 𝔓 𝒲 lam σ τ 2 (by omega)) (hle_cat σ τ 1 (by omega))
    rw [Fin.sum_univ_two] at hc
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, ← sub_eq_add_neg,
      sub_eq_zero] at hc
    have e0 : 𝔓.oface (cat 𝔓 𝒲 lam σ τ 2 (by omega)) 0 = lam ∘ τ.1 := oface_cat_zero 𝔓 𝒲 lam σ τ (by omega)
    have e1 : 𝔓.oface (cat 𝔓 𝒲 lam σ τ 2 (by omega)) 1 = σ.1 := oface_cat_last 𝔓 𝒲 lam σ τ (by omega)
    have h0' : biOpen (𝟙 X) 𝔓 𝒲 0 0 σ τ ≤ 𝔓.ointer (lam ∘ τ.1) :=
      (inf_le_left.trans (𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ.1)).trans (Scheme.Hom.id_preimage _).le
    have h1' : biOpen (𝟙 X) 𝔓 𝒲 0 0 σ τ ≤ 𝔓.ointer σ.1 := inf_le_right.trans (Scheme.Hom.id_preimage _).le
    rw [resc _ _ _ e0 _ h0', resc _ _ _ e1 _ h1'] at hc
    rw [biAug_apply, hpb, hzσ z.1 σ]
    change (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ _) = (OModulePresheaf.unit (𝟙 X ≫ π)).res _ _
    rw [OModulePresheaf.res_res]
    exact hc
  ·
    intro n z
    have hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 (n + 1) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1) = 0 := by
      rw [od_oext, LinearMap.mem_ker.1 z.2, map_zero]

    obtain ⟨hh, hhdef⟩ : ∃ hh : DoubleComplex.Tot (LerayDblCpx (𝟙 X) π 𝔓 𝒲) n, ∀ (a b : ℕ) (hab : a + b = n) (σ : 𝔓.Idx a) (τ : 𝒲.Idx b),
        hh ⟨(a, b), hab⟩ (σ, τ) = ((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat σ τ (n + 1) (by omega))
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega))) :=
      ⟨fun i στ => ((-1 : ℤ) ^ i.1.1) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat στ.1 στ.2 (n + 1) (by have := i.2; omega))
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam στ.1 στ.2 (n + 2) (by have := i.2; omega))),
        fun _ _ _ _ _ => rfl⟩
    refine ⟨hh, ?_⟩
    have map_hh : ∀ (a b : ℕ) (hab : a + b = n) (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) {U : X.Opens}
        (hU : U ≤ biOpen (𝟙 X) 𝔓 𝒲 a b σ τ),
        (X.presheaf.map (homOfLE hU).op).hom (hh ⟨(a, b), hab⟩ (σ, τ)) =
          ((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hU.trans (hle_cat σ τ (n + 1) (by omega)))
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega))) := by
      intro a b hab σ τ U hU
      rw [hhdef]
      show (OModulePresheaf.unit (𝟙 X ≫ π)).res hU (((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat σ τ (n + 1) (by omega))
        ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega)))) = _
      rw [map_zsmul, OModulePresheaf.res_res]

    have hsq : ∀ m : ℕ, ((-1 : ℤ) ^ m) * ((-1 : ℤ) ^ m) = 1 := fun m => by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hpq' : p + q = n + 1 := by simpa using hpq
    funext στ
    change BiIdx 𝔓 𝒲 p q at στ
    obtain ⟨σ', τ'⟩ := στ
    rw [Pi.sub_apply]
    erw [Pi.sub_apply]

    have hc := hcoc _ hζ (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (hle_cat σ' τ' (n + 2) (by omega))
    rcases p with _ | p' <;> rcases q with _ | q'
    · exact absurd hpq (by simp)
    ·
      obtain rfl : n = q' := by omega
      have hne : (⟨(0, n + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simp at this
      rw [DoubleComplex.dTot_apply_zero_succ, Pi.single_eq_same, Pi.single_eq_of_ne hne]
      erw [Pi.zero_apply, sub_zero]
      rw [biAug_apply, hpb]

      have e0 : 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) 0 = lam ∘ τ'.1 := oface_cat_zero 𝔓 𝒲 lam σ' τ' (by omega)
      have es : ∀ j : Fin (n + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) j.succ =
          cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega) := by
        intro j
        rw [← oface_cat_right 𝔓 𝒲 lam σ' τ' (by omega) j (by omega)]
        congr 1
        exact Fin.ext (by simp [Fin.val_succ]; omega)
      have h0' : biOpen (𝟙 X) 𝔓 𝒲 0 (n + 1) σ' τ' ≤ 𝔓.ointer (lam ∘ τ'.1) :=
        (inf_le_left.trans (𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ'.1)).trans (Scheme.Hom.id_preimage _).le
      have hs' : ∀ j : Fin (n + 2), biOpen (𝟙 X) 𝔓 𝒲 0 (n + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega)) := fun j =>
        (inf_le_inf_right _ (𝒲.inter_le_inter_face τ' j)).trans (hle_cat σ' (𝒲.face τ' j) (n + 1) (by omega))
      have hc' : (OModulePresheaf.unit (𝟙 X ≫ π)).res h0' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (lam ∘ τ'.1)) +
          ∑ j : Fin (n + 2), -(((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega)))) = 0 := by
        rw [Fin.sum_univ_succ] at hc
        rw [← hc]
        congr 1
        · rw [Fin.val_zero, pow_zero, one_smul]; exact resc _ _ _ e0.symm _ _
        · exact Finset.sum_congr rfl fun j _ => by
            rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]; congr 2; exact resc _ _ _ (es j).symm _ _
      rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at hc'
      show dV (𝟙 X) π 𝔓 𝒲 0 n (hh ⟨(0, n), by omega⟩) (σ', τ') = _
      rw [dV_apply']
      simp only [map_hh, pow_zero, one_smul]
      show _ = (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ _)
      rw [OModulePresheaf.res_res]
      exact hc'.symm
    ·
      obtain rfl : n = p' := by omega
      have hne : (⟨(n + 1, 0), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simp at this
      rw [DoubleComplex.dTot_apply_succ_zero, Pi.single_eq_of_ne hne, Pi.single_eq_same]
      erw [Pi.zero_apply, zero_sub]
      rw [hzσ z.1 σ']
      have eL : 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (Fin.last (n + 2)) = σ'.1 :=
        oface_cat_last 𝔓 𝒲 lam σ' τ' (by omega)
      have ec : ∀ j : Fin (n + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (Fin.castSucc j) =
          cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega) := fun j =>
        oface_cat_left 𝔓 𝒲 lam σ' τ' (by omega) j (by omega)
      have hL' : biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 σ' τ' ≤ 𝔓.ointer σ'.1 := inf_le_right.trans (Scheme.Hom.id_preimage _).le
      have hs' : ∀ j : Fin (n + 2), biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega)) := fun j =>
        (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝔓.inter_le_inter_face σ' j))).trans
          (hle_cat (𝔓.face σ' j) τ' (n + 1) (by omega))
      have hc' : ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))) +
          ((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res hL' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 σ'.1) = 0 := by
        rw [Fin.sum_univ_castSucc] at hc
        rw [← hc]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by
            rw [Fin.val_castSucc]; congr 1; exact resc _ _ _ (ec j).symm _ _
        · rw [Fin.val_last, pow_succ, pow_succ, mul_neg_one, mul_neg_one, neg_neg]; congr 1
          exact resc _ _ _ eL.symm _ _
      rw [← eq_neg_iff_add_eq_zero] at hc'
      show dH (𝟙 X) π 𝔓 𝒲 n 0 (hh ⟨(n, 0), by omega⟩) (σ', τ') = _
      rw [dH_apply']
      simp only [map_hh]
      have key : ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega)))) =
          -((OModulePresheaf.unit (𝟙 X ≫ π)).res hL' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 σ'.1)) := by
        rw [show (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ n) • ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _,
          hc', smul_neg, smul_smul, hsq, one_smul]
      exact key
    ·
      have hne0 : (⟨(p' + 1, q' + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simp at this
      have hne1 : (⟨(p' + 1, q' + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simp at this
      rw [DoubleComplex.dTot_apply_succ_succ, Pi.single_eq_of_ne hne0, Pi.single_eq_of_ne hne1]
      erw [Pi.zero_apply, sub_zero, Pi.add_apply, Pi.smul_apply]

      let e : Fin (p' + 2) ⊕ Fin (q' + 2) ≃ Fin (n + 3) := finSumFinEquiv.trans (finCongr (by omega))
      have he_inl : ∀ x : Fin (p' + 2), ((e (Sum.inl x) : Fin (n + 3)) : ℕ) = x := fun x => by simp [e]
      have he_inr : ∀ y : Fin (q' + 2), ((e (Sum.inr y) : Fin (n + 3)) : ℕ) = p' + 2 + y := fun y => by simp [e]
      have ecL : ∀ x : Fin (p' + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (e (Sum.inl x)) =
          cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega) := fun x =>
        (congrArg (𝔓.oface _) (Fin.ext (he_inl x))).trans (oface_cat_left 𝔓 𝒲 lam σ' τ' (by omega) x (by omega))
      have ecR : ∀ y : Fin (q' + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (e (Sum.inr y)) =
          cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega) := fun y =>
        (congrArg (𝔓.oface _) (Fin.ext (show ((e (Sum.inr y) : Fin (n + 3)) : ℕ) = p' + 1 + 1 + y by
          have := he_inr y; omega))).trans (oface_cat_right 𝔓 𝒲 lam σ' τ' (by omega) y (by omega))
      have hsL : ∀ x : Fin (p' + 2), biOpen (𝟙 X) 𝔓 𝒲 (p' + 1) (q' + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega)) := fun x =>
        (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝔓.inter_le_inter_face σ' x))).trans
          (hle_cat (𝔓.face σ' x) τ' (n + 1) (by omega))
      have hsR : ∀ y : Fin (q' + 2), biOpen (𝟙 X) 𝔓 𝒲 (p' + 1) (q' + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega)) := fun y =>
        (inf_le_inf_right _ (𝒲.inter_le_inter_face τ' y)).trans (hle_cat σ' (𝒲.face τ' y) (n + 1) (by omega))

      have hc' : ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))) +
          ((-1 : ℤ) ^ p') • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))) = 0 := by
        rw [← e.sum_comp, Fintype.sum_sum_type] at hc
        rw [← hc]
        congr 1
        · exact Finset.sum_congr rfl fun x _ => by rw [he_inl]; congr 1; exact resc _ _ _ (ecL x).symm _ _
        · rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => by
            rw [smul_smul, he_inr]
            congr 1
            · rw [show p' + 2 + (y : ℕ) = (p' + (y : ℕ)) + 2 by omega, pow_add, pow_add, neg_one_sq, mul_one]
            · exact resc _ _ _ (ecR y).symm _ _
      rw [← eq_neg_iff_add_eq_zero] at hc'
      show dH (𝟙 X) π 𝔓 𝒲 p' (q' + 1) (hh ⟨(p', q' + 1), by omega⟩) (σ', τ') +
          ((-1 : ℤ) ^ (p' + 1)) • dV (𝟙 X) π 𝔓 𝒲 (p' + 1) q' (hh ⟨(p' + 1, q'), by omega⟩) (σ', τ') = 0
      rw [dH_apply', dV_apply']
      simp only [map_hh]
      have key : ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (((-1 : ℤ) ^ p') • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega)))) +
          ((-1 : ℤ) ^ (p' + 1)) • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (((-1 : ℤ) ^ (p' + 1)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega)))) = 0 := by
        rw [show (∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (((-1 : ℤ) ^ p') • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ p') • ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _,
          show (∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (((-1 : ℤ) ^ (p' + 1)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ (p' + 1)) • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _,
          hc', smul_neg, smul_smul, smul_smul, hsq, hsq, one_smul, neg_add_cancel]
      exact key
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_dTot_eq_single_biAug_unitPullback_sub_single_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 0)),
        OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 0 (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) =
          (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 0 0 => (X.presheaf.map (homOfLE ((inf_le_right :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 0 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
              (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1) :
            OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 0 0)) ∧
    ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
      ∃ h : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n,
        DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n h =
          Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(0, n + 1), by omega⟩
              (OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 (n + 1)
                (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1)) -
            Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(n + 1, 0), by omega⟩
              (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 (n + 1) 0 => (X.presheaf.map (homOfLE ((inf_le_right :
                OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
                  (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q) (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by
  have h₁ : ∀ {p q : ℕ} (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
      biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ biOpen (𝟙 X) 𝒲 𝔓 p q τ σ := fun σ τ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le) (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  have h₂ : ∀ {p q : ℕ} (τ : 𝒲.Idx p) (σ : 𝔓.Idx q),
      biOpen (𝟙 X) 𝒲 𝔓 p q τ σ ≤ biOpen (𝟙 X) 𝔓 𝒲 q p σ τ := fun τ σ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le) (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  refine ⟨fun p q =>
    { toFun := fun x στ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
      map_add' := fun x y => funext fun στ => map_add _ _ _
      map_smul' := fun r x => funext fun στ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (r • x (στ.2, στ.1)) = r • (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
        exact map_smul _ _ _
      invFun := fun y τσ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₂ τσ.1 τσ.2) (y (τσ.2, τσ.1))
      left_inv := fun x => funext fun τσ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (x (τσ.1, τσ.2))) = x τσ
        rw [OModulePresheaf.res_res]
        exact (OModulePresheaf.unit (𝟙 X ≫ π)).res_refl_apply _ _
      right_inv := fun y => funext fun στ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (y (στ.1, στ.2))) = y στ
        rw [OModulePresheaf.res_res]
        exact (OModulePresheaf.unit (𝟙 X ≫ π)).res_refl_apply _ _ }, ?_, ?_, ?_⟩
  · intro p q x
    funext στ
    obtain ⟨σ, τ'⟩ := στ
    show (X.presheaf.map (homOfLE (h₁ σ τ')).op).hom (dH (𝟙 X) π 𝒲 𝔓 p q x (τ', σ)) =
      dV (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p => (X.presheaf.map (homOfLE (h₁ στ.1 στ.2)).op).hom (x (στ.2, στ.1))) (σ, τ')
    rw [dH_apply', dV_apply', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro p q x
    funext στ
    obtain ⟨σ', τ⟩ := στ
    show (X.presheaf.map (homOfLE (h₁ σ' τ)).op).hom (dV (𝟙 X) π 𝒲 𝔓 p q x (τ, σ')) =
      dH (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p => (X.presheaf.map (homOfLE (h₁ στ.1 στ.2)).op).hom (x (στ.2, στ.1))) (σ', τ)
    rw [dH_apply', dV_apply', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro p q x σ τ
    rfl
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q) (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated -/

namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry


open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    ∃ (e₀ : ↥((OModulePresheaf.unit π).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit π).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit π).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit π).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit π).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit π).H0 𝒲)) : (OModulePresheaf.unit π).cochain 𝒲 0) =
          OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit π).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) := by
  classical
  suffices H : ∃ (e₀ : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit (𝟙 X ≫ π)).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit (𝟙 X ≫ π)).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲)) : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 0) = OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈ LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) by
    rw [Category.id_comp] at H
    exact H

  have upb_zero : ∀ m : ℕ, OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m (0 : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) = 0 := by
    intro m; funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.zero_apply]
      change _ • (X.presheaf.map _).hom ((Scheme.Hom.app (𝟙 X) _).hom (0 : Γ(X, _))) = (0 : Γ(X, _))
      rw [map_zero, map_zero, smul_zero]
    · rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.zero_apply]
  have hcoc : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m), (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 m z = 0 → OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z ∈ LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 m) := by
    intro m z hz
    rw [LinearMap.mem_ker, d_unitPullback, hz, upb_zero]

  obtain ⟨hrowsW, hkerW, hinjW⟩ := rows_exact (𝟙 X) π 𝔓 𝒲
  obtain ⟨hrowsP, hkerP, hinjP⟩ := rows_exact (𝟙 X) π 𝒲 𝔓
  obtain ⟨⟨e0W, he0W⟩, hPW⟩ := DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)
    (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 m) (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 m) (fun m => biAug (𝟙 X) π 𝔓 𝒲 m)
    hinjW (fun m => dV_comp_biAug (𝟙 X) π 𝔓 𝒲 m) hkerW hrowsW
  obtain ⟨⟨e0P, he0P⟩, hPP⟩ := DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓)
    (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 m) (fun m => biAug (𝟙 X) π 𝒲 𝔓 m)
    hinjP (fun m => dV_comp_biAug (𝟙 X) π 𝒲 𝔓 m) hkerP hrowsP
  choose eW heW using hPW
  choose eP heP using hPP

  obtain ⟨el, helH, helV, hel⟩ := exists_levelwise_equiv_transpose_id π 𝔓 𝒲
  have hE1 := fun n => DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓) (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)) el helH helV n
  choose E1 hE1' using hE1
  have hE2 := fun n => DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n
  choose E2 hE2' using hE2
  obtain ⟨hG30, hG3⟩ := exists_dTot_eq_single_biAug_unitPullback_sub_single_id π 𝔓 𝒲 lam hlam

  have hcol : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m),
      (show biC (𝟙 X) π 𝔓 𝒲 m 0 from el 0 m (biAug (𝟙 X) π 𝒲 𝔓 m z)) =
        fun στ : BiIdx 𝔓 𝒲 m 0 => (X.presheaf.map (homOfLE ((inf_le_right :
          biOpen (𝟙 X) 𝔓 𝒲 m 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z στ.1) := by
    intro m z
    funext στ
    obtain ⟨σ, τ⟩ := στ
    rw [hel 0 m _ σ τ, biAug_apply]
    change ((X.presheaf.map _ ≫ X.presheaf.map _)).hom (z σ) = _
    rw [← Functor.map_comp]
    rfl
  refine ⟨((e0P.trans (E1 0)).trans (E2 0)).trans e0W.symm,
    fun n => (((eP n).trans (E1 (n + 1))).trans (E2 (n + 1))).trans (eW n).symm, ?_, ?_⟩
  ·
    intro z
    have hlz := hcoc 0 z.1 (LinearMap.mem_ker.1 z.2)
    obtain ⟨hEP, h1⟩ := he0P z.1 z.2
    obtain ⟨hc1, h2⟩ := hE1' 0 ⟨_, hEP⟩
    obtain ⟨hS, h3⟩ := hE2' 0 _ hc1
    obtain ⟨hEW, h4⟩ := he0W _ hlz
    have key : e0W.symm (E2 0 (E1 0 (e0P z))) = ⟨_, hlz⟩ := by
      rw [LinearEquiv.symm_apply_eq, show e0P z = e0P ⟨z.1, z.2⟩ from rfl, h1, h2, h3, h4]
      congr 1
      apply Subtype.ext
      funext i
      obtain ⟨⟨p, q⟩, hpq⟩ := i
      obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := ⟨by omega, by omega⟩
      dsimp only
      rw [Pi.single_eq_same, Pi.single_eq_same, Nat.mul_zero, pow_zero, one_smul]
      exact (hcol 0 z.1).trans (hG30 z).symm
    change (((e0W.symm (E2 0 (E1 0 (e0P z)))) : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲)) : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 0) = _
    rw [key]
  · intro n z
    have hlz := hcoc (n + 1) z.1 (LinearMap.mem_ker.1 z.2)
    refine ⟨hlz, ?_⟩
    obtain ⟨hEP, h1⟩ := heP n z.1 z.2
    obtain ⟨hc1, h2⟩ := hE1' (n + 1) ⟨_, hEP⟩
    obtain ⟨hS, h3⟩ := hE2' (n + 1) _ hc1
    obtain ⟨hEW, h4⟩ := heW n _ hlz
    obtain ⟨hh, hG3n⟩ := hG3 n z
    change (eW n).symm (E2 (n + 1) (E1 (n + 1) (eP n (Submodule.Quotient.mk z)))) = _
    rw [LinearEquiv.symm_apply_eq, show Submodule.Quotient.mk z = Submodule.Quotient.mk ⟨z.1, z.2⟩ from rfl, h1, h2, h3, h4]

    have hne : ∀ (p q : ℕ) (hpq : p + q = n + 1), q ≠ 0 →
        (⟨(q, p), by omega⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ ∧
        (⟨(p, q), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := by
      intro p q hpq hq
      refine ⟨fun h => hq ?_, fun h => hq ?_⟩
      · have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simpa using this
      · have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simpa using this
    apply (Submodule.Quotient.eq _).2
    change ((_ : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) (n + 1)) - _) ∈ LinearMap.range (DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n)
    refine ⟨-hh, ?_⟩
    rw [map_neg, hG3n, neg_sub]
    congr 1
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    dsimp only
    by_cases hq : q = 0
    · subst hq
      obtain rfl : p = n + 1 := by omega
      rw [Pi.single_eq_same, Pi.single_eq_same, Nat.mul_zero, pow_zero, one_smul]
      exact (hcol (n + 1) z.1).symm
    · obtain ⟨hne1, hne2⟩ := hne p q hpq hq
      rw [Pi.single_eq_of_ne hne2, Pi.single_eq_of_ne hne1, map_zero]
      exact (smul_zero _).symm
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry


private theorem AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    ∃ (e₀ : ↥((OModulePresheaf.unit π).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit π).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit π).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit π).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit π).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit π).H0 𝒲)) : (OModulePresheaf.unit π).cochain 𝒲 0) =
          OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit π).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated.solution
/- Adapted from P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian"


namespace AntiInv

theorem le_preimage_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (hU : U ≤ g ⁻¹ᵁ V) (hV : V ≤ g' ⁻¹ᵁ W) : U ≤ (g ≫ g') ⁻¹ᵁ W := fun x hx => hV (hU hx)

theorem unitPullback_eq_zero_of_subsingleton {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) [Subsingleton 𝒦.ι] (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 (n + 1)) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) z = 0 := by
  funext s
  rw [OModulePresheaf.unitPullback_apply_of_not_injective]
  · rfl
  · intro hinj
    have h01 : (0 : Fin (n + 2)) = 1 := hinj (Subsingleton.elim _ _)
    exact absurd h01 (by simp)

end AntiInv

open AntiInv in
theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 𝒲 : A.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit f).cochain 𝒲 0,
      (OModulePresheaf.unit f).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1 z +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z := by
  classical
  haveI : IsProper f := hA.proper
  haveI : IsSeparated f := inferInstance

  let ι : A ⟶ A := (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1
  have hι : ι ≫ f = f := (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2
  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of k)))).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of k)))).2
  let μ : pullback f f ⟶ A :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
  have hμ : μ ≫ f = pullback.fst f f ≫ f :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

  have w : 𝟙 A ≫ f = ι ≫ f := by rw [Category.id_comp, hι]
  let δ : A ⟶ pullback f f := pullback.lift (𝟙 A) ι w
  have hδ1 : δ ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hδ2 : δ ≫ pullback.snd f f = ι := pullback.lift_snd _ _ _
  have hδμ : δ ≫ μ = f ≫ e := by
    have hψ : δ ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hδ1, Category.id_comp]
    have h := congrArg Subtype.val
      (L.mul_natural (pullback.fst f f ≫ f) f δ hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    have hx : schemeHomOverComp δ hψ ⟨pullback.fst f f, rfl⟩ = ⟨𝟙 A, Category.id_comp f⟩ := Subtype.ext hδ1
    have hy : schemeHomOverComp δ hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
        L.inv f ⟨𝟙 A, Category.id_comp f⟩ := Subtype.ext hδ2
    rw [hx, hy, L.mul_inv_cancel, ← L.one_natural (𝟙 _) f f (Category.comp_id f)] at h
    exact h
  have hδf : δ ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hδ1, Category.id_comp]
  haveI : IsAffineHom δ := by
    have : IsAffineHom (δ ≫ pullback.fst f f) := by rw [hδ1]; infer_instance
    exact IsAffineHom.of_comp δ (pullback.fst f f)

  let zt : (OModulePresheaf.unit f).cochain 𝒲 1 := OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z
  have hzt : (OModulePresheaf.unit f).d 𝒲 1 zt = 0 := by
    obtain ⟨L2, hL2⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f f (𝟙 A)
      (Category.id_comp f) 𝒲 𝒦 lam₂ h₂ 2
    change (OModulePresheaf.unit f).d 𝒲 1 (OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z) = 0
    rw [AlgebraicGeometry.OModulePresheaf.d_unitPullback, hz, ← hL2, map_zero]

  obtain ⟨𝒲', l₁, l₂, l₃, hl₁, hl₂, hl₃⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_pullback_fst_snd_of_isSeparated f 𝒲 μ hμ
  obtain ⟨b', hb'⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
      k f L hA 𝒲 𝒲' l₁ l₂ l₃ hl₁ hl₂ hl₃ zt hzt

  let 𝒱 : A.OrderedAffineCover := 𝒲'.comap δ
  have hv : ∀ v, 𝒱.U v ≤ δ ⁻¹ᵁ 𝒲'.U (id v) := fun v => le_rfl
  have hv1 : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒲.U (l₁ v) := fun v => hδ1 ▸ le_preimage_comp δ (pullback.fst f f) (hv v) (hl₁ v)
  have hv2 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒲.U (l₂ v) := fun v => hδ2 ▸ le_preimage_comp δ (pullback.snd f f) (hv v) (hl₂ v)
  have hv3 : ∀ v, 𝒱.U v ≤ (δ ≫ μ) ⁻¹ᵁ 𝒲.U (l₃ v) := fun v => le_preimage_comp δ μ (hv v) (hl₃ v)

  let S : Submodule k ((OModulePresheaf.unit f).cochain 𝒱 1) := LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0)

  have ha : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲' 𝒲 l₃ hl₃ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f
      δ μ (δ ≫ μ) rfl 𝒱 𝒲' 𝒲 id l₃ l₃ rfl hv hl₃ hv3 1 zt hzt
  have hb : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲' 𝒲 l₁ hl₁ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f
      δ (pullback.fst f f) (𝟙 A) hδ1.symm 𝒱 𝒲' 𝒲 id l₁ l₁ rfl hv hl₁ hv1 1 zt hzt
  have hc : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲' 𝒲 l₂ hl₂ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f
      δ (pullback.snd f f) ι hδ2.symm 𝒱 𝒲' 𝒲 id l₂ l₂ rfl hv hl₂ hv2 1 zt hzt

  have hd : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲' 𝒲 l₃ hl₃ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲' 𝒲 l₁ hl₁ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲' 𝒲 l₂ hl₂ 1 zt) ∈ S := by
    obtain ⟨Lδ, hLδ⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f (pullback.fst f f ≫ f)
      δ hδf 𝒱 𝒲' id hv 1
    rw [← hLδ, ← hLδ, ← hLδ, ← map_sub, ← map_sub, ← hb', hLδ,
      ← AlgebraicGeometry.OModulePresheaf.d_unitPullback]
    exact LinearMap.mem_range_self _ _

  have he' : OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt ∈ S := by

    have hpt : (e.base (IsLocalRing.closedPoint k) : A) ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒲.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hpt
    obtain ⟨i₀, hi₀⟩ := hpt
    let 𝒮 := Scheme.OrderedAffineCover.ofAffine (Spec (CommRingCat.of k))
    haveI : Subsingleton 𝒮.ι := (inferInstance : Subsingleton PUnit)
    have hlamf : ∀ v, 𝒱.U v ≤ f ⁻¹ᵁ 𝒮.U ((fun _ => PUnit.unit) v) := fun v => le_top
    have hlame : ∀ s, 𝒮.U s ≤ e ⁻¹ᵁ 𝒲.U ((fun _ => i₀) s) := by
      intro s x _
      have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hx]; exact hi₀
    have hlam3 : ∀ v, 𝒱.U v ≤ (δ ≫ μ) ⁻¹ᵁ 𝒲.U ((fun _ => i₀) v) := fun v =>
      hδμ ▸ le_preimage_comp f e (hlamf v) (hlame PUnit.unit)
    have h1 := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (𝟙 _) f
      f e (δ ≫ μ) hδμ 𝒱 𝒮 𝒲 (fun _ => PUnit.unit) (fun _ => i₀) (fun _ => i₀) rfl hlamf hlame hlam3 1 zt hzt
    rw [AntiInv.unitPullback_eq_zero_of_subsingleton, zero_sub] at h1
    obtain ⟨b3, hb3⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
      f f (δ ≫ μ) 𝒱 𝒲 l₃ (fun _ => i₀) hv3 hlam3 zt hzt
    have h2 : OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt -
        OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 (fun _ => i₀) hlam3 1 zt ∈ S := ⟨b3, hb3⟩
    have hB := (S.neg_mem_iff).mp h1
    have h3 := S.add_mem h2 hB
    simpa only [sub_add_cancel] using h3

  have key : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt +
      OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt ∈ S := by
    have hμS := S.add_mem ha he'
    simp only [sub_add_cancel] at hμS

    have hsum := S.sub_mem hμS hd

    have := S.sub_mem (S.sub_mem hsum hb) hc
    convert this using 1
    abel

  let uu : (OModulePresheaf.unit f).cochain 𝒲 1 :=
    OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1 z +
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z
  have hu0 : (OModulePresheaf.unit f).d 𝒲 1 uu = 0 := by
    obtain ⟨L1, hL1⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f f ι hι 𝒲 𝒦 lam₁ h₁ 2
    obtain ⟨L2, hL2⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f f (𝟙 A)
      (Category.id_comp f) 𝒲 𝒦 lam₂ h₂ 2
    change (OModulePresheaf.unit f).d 𝒲 1 (OModulePresheaf.unitPullback (πX := f) ι 𝒲 𝒦 lam₁ h₁ 1 z +
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z) = 0
    rw [map_add, AlgebraicGeometry.OModulePresheaf.d_unitPullback, AlgebraicGeometry.OModulePresheaf.d_unitPullback, hz,
      ← hL1, ← hL2, map_zero, map_zero, add_zero]
  have hkey2 : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 uu ∈ S := by
    obtain ⟨L1, hL1⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f f (𝟙 A)
      (Category.id_comp f) 𝒱 𝒲 l₁ hv1 1
    have hsplit : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 uu =
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1
            (OModulePresheaf.unitPullback (πX := f) ι 𝒲 𝒦 lam₁ h₁ 1 z) +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt := by
      rw [← hL1, ← hL1, ← hL1, ← map_add]
    rw [hsplit]

    have hg1 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒦.U ((lam₁ ∘ l₁) v) := fun v =>
      (Category.id_comp ι) ▸ le_preimage_comp (𝟙 A) ι (hv1 v) (h₁ (l₁ v))
    have hg := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f
      (𝟙 A) ι ι (Category.id_comp ι).symm 𝒱 𝒲 𝒦 l₁ lam₁ (lam₁ ∘ l₁) rfl hv1 h₁ hg1 1 z hz
    have hh1 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒦.U ((lam₂ ∘ l₂) v) := fun v =>
      (Category.comp_id ι) ▸ le_preimage_comp ι (𝟙 A) (hv2 v) (h₂ (l₂ v))
    have hh := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f
      ι (𝟙 A) ι (Category.comp_id ι).symm 𝒱 𝒲 𝒦 l₂ lam₂ (lam₂ ∘ l₂) rfl hv2 h₂ hh1 1 z hz
    obtain ⟨bi, hbi⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
      f f ι 𝒱 𝒦 (lam₁ ∘ l₁) (lam₂ ∘ l₂) hg1 hh1 z hz
    have hi : OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒦 (lam₁ ∘ l₁) hg1 1 z -
        OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒦 (lam₂ ∘ l₂) hh1 1 z ∈ S := ⟨bi, hbi⟩

    have := S.add_mem (S.sub_mem (S.add_mem hg hi) hh) key
    convert this using 1
    change _ = _ - (OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt - _) + _
    abel

  obtain ⟨e₀, eH, -, heH⟩ := AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated f 𝒲 𝒱 l₁ hv1
  obtain ⟨huv, heq⟩ := heH 0 ⟨uu, hu0⟩
  have hzero : eH 0 (Submodule.Quotient.mk ⟨uu, hu0⟩) = 0 := by
    rw [heq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hkey2
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hzero
  obtain ⟨b, hb⟩ := hzero
  exact ⟨b, hb⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
/- Adapted from Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian


private theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 𝒲 : A.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit f).cochain 𝒲 0,
      (OModulePresheaf.unit f).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1 z +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem solution
    {S : Type u} [CommRing S] [IsLocalRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by
  classical
  constructor
  · intro h
    obtain ⟨U, hsU, ⟨e⟩⟩ := h (IsLocalRing.closedPoint S)
    have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hsU
    subst hU

    let ι : (↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) : Scheme.{u}) ⟶ X := (g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)).ι
    let j : X ⟶ ↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) := (Scheme.topIso X).inv
    have hj : j ≫ ι = 𝟙 X := (Scheme.topIso X).inv_hom_id
    let Φ : 𝟭 X.Modules ≅ Scheme.Modules.pullback ι ⋙ Scheme.Modules.pullback j :=
      (Scheme.Modules.pullbackId X).symm ≪≫ eqToIso (by rw [hj]) ≪≫ (Scheme.Modules.pullbackComp j ι).symm
    exact ⟨Φ.app M ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫ (Φ.app M').symm⟩
  · rintro ⟨e⟩ s
    exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
/- Adapted from Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

private theorem AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing
    {S : Type u} [CommRing S] [IsLocalRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry


theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) [IsAffineHom h] (𝒦 : Y.OrderedAffineCover)
    (hlam : ∀ w : (𝒦.comap h).ι, (𝒦.comap h).U w ≤ h ⁻¹ᵁ 𝒦.U w)
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒦.comap h).Idx n) :
    OModulePresheaf.unitPullback (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s =
      (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by
  classical
  have hinj : Function.Injective ((fun w : (𝒦.comap h).ι => w) ∘ s.1) := s.2.injective
  have hgen : ∀ (f : Fin (n + 1) → 𝒦.ι), Monotone f → Tuple.sort f = Equiv.refl _ :=
    fun f hf => Tuple.sort_eq_refl_iff_monotone.mpr hf
  have hmono : Monotone (((fun w : (𝒦.comap h).ι => w) ∘ s.1 : Fin (n + 1) → 𝒦.ι)) := fun i j hij => s.2.monotone hij
  rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s hinj]
  have hidx : (𝒦.comap h).sortIdx 𝒦 (fun w => w) s hinj = s := by
    apply Subtype.ext
    rw [Scheme.OrderedAffineCover.sortIdx_val]
    rw [hgen _ hmono]
    rfl

  have key : ∀ (t : 𝒦.Idx n) (ht : t = s) (hle : (𝒦.comap h).inter s ≤ h ⁻¹ᵁ 𝒦.inter t) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ = Equiv.refl _),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter t)).hom (z t)) =
        (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by
    intro t ht hle σ hσ; subst ht; subst hσ
    rw [Equiv.Perm.sign_refl, Units.val_one, one_smul]
  exact key _ hidx _ _ (hgen _ hmono)
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply
/- Adapted from Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply -/

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

private theorem AlgebraicGeometry.OModulePresheaf.unitPullback_comap_id_apply
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) [IsAffineHom h] (𝒦 : Y.OrderedAffineCover)
    (hlam : ∀ w : (𝒦.comap h).ι, (𝒦.comap h).U w ≤ h ⁻¹ᵁ 𝒦.U w)
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒦.comap h).Idx n) :
    OModulePresheaf.unitPullback (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s =
      (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply.solution
/- Adapted from P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian


namespace Ws23K1

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n 0 = 0 := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj, Pi.zero_apply]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    rfl

end Ws23K1

open Ws23K1 in
theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)

    (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)
    (s₁ s₂ : A ⟶ pullback f f)
    (hs₁ : s₁ ≫ pullback.fst f f = 𝟙 A) (hs₁' : s₁ ≫ pullback.snd f f = f ≫ e)
    (hs₂ : s₂ ≫ pullback.fst f f = f ≫ e) (hs₂' : s₂ ≫ pullback.snd f f = 𝟙 A)

    (𝒲 : (pullback f f).OrderedAffineCover) (𝒱₁ 𝒱₂ : A.OrderedAffineCover)
    (lam₁ : 𝒱₁.ι → 𝒲.ι) (lam₂ : 𝒱₂.ι → 𝒲.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ s₁ ⁻¹ᵁ 𝒲.U (lam₁ v)) (hl₂ : ∀ v, 𝒱₂.U v ≤ s₂ ⁻¹ᵁ 𝒲.U (lam₂ v))

    (Z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1)
    (hZ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 Z = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) s₁ 𝒱₁ 𝒲 lam₁ hl₁ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) s₂ 𝒱₂ 𝒲 lam₂ hl₂ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0)) :
    Z ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0) := by
  classical
  haveI : IsProper f := hA.proper

  haveI hcl₁ : IsClosedImmersion s₁ := by
    have : IsClosedImmersion (s₁ ≫ pullback.fst f f) := by rw [hs₁]; infer_instance
    exact IsClosedImmersion.of_comp s₁ (pullback.fst f f)
  haveI hcl₂ : IsClosedImmersion s₂ := by
    have : IsClosedImmersion (s₂ ≫ pullback.snd f f) := by rw [hs₂']; infer_instance
    exact IsClosedImmersion.of_comp s₂ (pullback.snd f f)

  have hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom := by
    have hsq : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
      have e1 : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ := by
        rw [CommRingCat.ofHom_id]; exact Spec.map_id _
      rw [e1]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact hA.bijective_specIso_inv_comp_appTop_of_isPullback (RingHom.id k) f (𝟙 A) hsq

  have bridge : ∀ (s : A ⟶ pullback f f) [IsClosedImmersion s] (𝒱 : A.OrderedAffineCover) (lam : 𝒱.ι → 𝒲.ι)
      (hl : ∀ v, 𝒱.U v ≤ s ⁻¹ᵁ 𝒲.U (lam v)),
      OModulePresheaf.unitPullback (πX := f) s 𝒱 𝒲 lam hl 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) →
      ∃ b : (OModulePresheaf.unit f).cochain (𝒲.comap s) 0,
        (OModulePresheaf.unit f).d (𝒲.comap s) 0 b = fun t =>
          (A.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (Z t)) := by
    intro s _ 𝒱 lam hl hmem
    have hlamC : ∀ w : (𝒲.comap s).ι, (𝒲.comap s).U w ≤ s ⁻¹ᵁ 𝒲.U w := fun w => le_rfl

    have hr : OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z = fun t =>
        (A.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (Z t)) :=
      funext fun t => OModulePresheaf.unitPullback_comap_id_apply f (pullback.fst f f ≫ f) s 𝒲 hlamC 1 Z t

    have hdr : (OModulePresheaf.unit f).d (𝒲.comap s) 1
        (OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z) = 0 := by
      rw [OModulePresheaf.d_unitPullback, hZ, unitPullback_zero]

    have hl' : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ (𝒲.comap s).U (lam v) := fun v => hl v

    have hcomp := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
      f f (pullback.fst f f ≫ f) (𝟙 A) s s (Category.id_comp s).symm 𝒱 (𝒲.comap s) 𝒲 lam (fun w => w) lam rfl
      hl' hlamC hl 1 Z hZ
    change _ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) at hcomp
    have hmem' : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 (𝒲.comap s) lam hl' 1
        (OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z) ∈
        LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) := by
      have := Submodule.add_mem _ hcomp hmem
      rwa [sub_add_cancel] at this

    obtain ⟨-, eH, -, heH⟩ :=
      OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated f (𝒲.comap s) 𝒱 lam hl'
    obtain ⟨hz, hclass⟩ := heH 0 ⟨_, hdr⟩
    have hzero : (eH 0) (Submodule.Quotient.mk ⟨_, hdr⟩) = 0 := by
      rw [hclass, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hmem'
    have hzero' : (Submodule.Quotient.mk ⟨_, hdr⟩ : (OModulePresheaf.unit f).HSucc (𝒲.comap s) 0) = 0 :=
      (eH 0).map_eq_zero_iff.mp hzero
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hzero'
    obtain ⟨b, hb⟩ := hzero'
    exact ⟨b, hb.trans hr⟩
  obtain hcX := bridge s₁ 𝒱₁ lam₁ hl₁ h₁
  obtain hcY := bridge s₂ 𝒱₂ lam₂ hl₂ h₂
  obtain ⟨b, hb⟩ := OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap f f hX hX e he e he
    (pullback.fst f f) (pullback.snd f f) (IsPullback.of_hasPullback f f) s₁ hs₁ hs₁' s₂ hs₂ hs₂' 𝒲 Z hZ hcX hcY
  exact ⟨b, hb⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range
/- Adapted from Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian


private theorem GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)

    (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)
    (s₁ s₂ : A ⟶ pullback f f)
    (hs₁ : s₁ ≫ pullback.fst f f = 𝟙 A) (hs₁' : s₁ ≫ pullback.snd f f = f ≫ e)
    (hs₂ : s₂ ≫ pullback.fst f f = f ≫ e) (hs₂' : s₂ ≫ pullback.snd f f = 𝟙 A)

    (𝒲 : (pullback f f).OrderedAffineCover) (𝒱₁ 𝒱₂ : A.OrderedAffineCover)
    (lam₁ : 𝒱₁.ι → 𝒲.ι) (lam₂ : 𝒱₂.ι → 𝒲.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ s₁ ⁻¹ᵁ 𝒲.U (lam₁ v)) (hl₂ : ∀ v, 𝒱₂.U v ≤ s₂ ⁻¹ᵁ 𝒲.U (lam₂ v))

    (Z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1)
    (hZ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 Z = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) s₁ 𝒱₁ 𝒲 lam₁ hl₁ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) s₂ 𝒱₂ 𝒲 lam₂ hl₂ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0)) :
    Z ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


namespace UASRestrict

theorem unit_app_one_res {Y : Scheme.{u}}
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))
  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

end UASRestrict

open UASRestrict in
theorem solution
    {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (ψ.hom.val.app (op W)).hom (1 : Y.presheaf.obj (op W)) := by
  unfold Scheme.Modules.unitAutSection
  erw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  rw [← unit_app_one_res ψ (homOfLE (le_top : W ≤ ⊤))]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
  rw [← CommRingCat.comp_apply]
  erw [← Functor.map_comp]
  rfl
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
/- Adapted from Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


private theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
    {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (ψ.hom.val.app (op W)).hom (1 : Y.presheaf.obj (op W)) := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


namespace PicDefRescale

theorem uAS_trans {Y : Scheme.{u}} (W : Y.Opens)
    (e₁ e₂ : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W (e₁ ≪≫ e₂) =
      Scheme.Modules.unitAutSection W e₁ * Scheme.Modules.unitAutSection W e₂ :=
  (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).1 e₁ e₂

theorem unit_app_one_res {Y : Scheme.{u}} (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))

  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

theorem uAS_conj_res {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (Scheme.Modules.unitAutSection ⊤
          ((Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι).symm ≪≫
            (Scheme.Modules.pullback (⊤ : Y.Opens).ι).mapIso ψ ≪≫
            Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι)) := by
  rw [Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one,
    Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one, unit_app_one_res]

variable {X : Scheme.{u}}

theorem res_res {U V : X.Opens} (h : V ≤ U) (x : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom x := by
  have hc : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [← Functor.map_comp]; rfl
  rw [← hc]; rfl

end PicDefRescale

open PicDefRescale in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules)
    (φ₀ φ₀' : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (u u' : Γ(X, ⊤)) (huu' : u * u' = 1)
    (hu : g.appTop.hom u =
      Scheme.Modules.unitAutSection ⊤
        ((Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι).symm ≪≫
          (Scheme.Modules.pullback (⊤ : X₀.Opens).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
          Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀' w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw

  let ru : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op).hom u
  let ru' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op).hom u'
  have hru : ∀ a, ru a * ru' a = 1 := fun a => by
    simp only [ru, ru', ← map_mul, huu', map_one]
  refine ⟨τ, fun a => ea a * ru a, fun a => ea' a * ru' a, fun a => ?_, fun a => ?_, fun s => ?_⟩
  ·
    calc ea a * ru a * (ea' a * ru' a) = (ea a * ea' a) * (ru a * ru' a) := by ring
      _ = 1 := by rw [h1 a, hru a, one_mul]
  ·
    have hsplit : ((τ.comap g a).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀' ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι :
          SheafOfModules.unit (((𝒰.comap g).U a : Scheme.{u})).ringCatSheaf ≅
            SheafOfModules.unit (((𝒰.comap g).U a : Scheme.{u})).ringCatSheaf) =
        ((τ.comap g a).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) ≪≫
        ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) := by
      apply Iso.ext
      change (τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀'.hom ≫
          (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom =
        ((τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀.hom ≫
          (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom) ≫
        ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).inv ≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map (φ₀.inv ≫ φ₀'.hom) ≫
            (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom)
      simp
    have key : Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀' ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) =
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) *
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) := by
      rw [hsplit]
      exact uAS_trans _ _ _
    refine Eq.trans ?_ key.symm
    rw [map_mul, ← h2 a, uAS_conj_res, ← hu]
    congr 1

    have nat := congrArg (fun φ => φ.hom u) (g.naturality (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op)
    exact nat
  ·
    have hres : (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1)) = 1 := by
      simp only [ru, ru', PicDefRescale.res_res, ← map_mul, ← map_one (X.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op).hom,
        mul_comm u' u, huu']
    have key : τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0) * ru' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1) * ru (s.1 1)) - 1 =
        τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) - 1 := by
      rw [map_mul, map_mul]
      calc _ = τ.transition s *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) *
            ((X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
              (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1))) - 1 := by ring
        _ = _ := by rw [hres, mul_one]
    rw [key]
    exact h3 s
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection
/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules)
    (φ₀ φ₀' : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (u u' : Γ(X, ⊤)) (huu' : u * u' = 1)
    (hu : g.appTop.hom u =
      Scheme.Modules.unitAutSection ⊤
        ((Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι).symm ≪≫
          (Scheme.Modules.pullback (⊤ : X₀.Opens).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
          Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀' w := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁)
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
    (s : Γ(X₀, ⊤)) (hs : IsUnit s) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ g.appTop.hom u = s := by
  classical

  have hnat : ∀ c : B₁, g.appTop.hom (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c) =
      ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom (π c) := by
    intro c
    have hN := congrArg (fun k => (k.hom) c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
    have hC := congrArg (fun k => (k.hom) ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom c))
      (show f.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom π)).appTop ≫ f₀.appTop from by
        rw [← Scheme.Hom.comp_appTop, hg, Scheme.Hom.comp_appTop])
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hN hC ⊢
    rw [hC, ← hN]
    rfl

  let e₀ := RingEquiv.ofBijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom h₀
  obtain ⟨c₀, hc₀⟩ := h₀.2 s
  have hc₀u : IsUnit c₀ := by
    have h' : e₀.symm s = c₀ := e₀.injective (by rw [RingEquiv.apply_symm_apply]; exact hc₀.symm)
    exact h' ▸ hs.map e₀.symm
  obtain ⟨c, rfl⟩ := hπ c₀
  have hcu : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal B₁ := (IsLocalRing.mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hcu)
    obtain ⟨d₀, hd₀⟩ := hc₀u.exists_right_inv
    obtain ⟨d, rfl⟩ := hπ d₀
    have hk : c * d - 1 ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, map_mul, map_one, hd₀, sub_self]
    have h1 : (1 : B₁) ∈ IsLocalRing.maximalIdeal B₁ := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right d _ hcm) (hI hk)
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal B₁).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  exact ⟨((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c, hcu.map _, by rw [hnat, hc₀]⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
/- Adapted from Theorems.Thm_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁)
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
    (s : Γ(X₀, ⊤)) (hs : IsUnit s) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ g.appTop.hom u = s := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal.solution
/- Adapted from P2M.Sol.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


namespace UnitClassZero
p2m_open "AlgebraicGeometry.Scheme.Modules"

section coh
variable {T' T : Scheme.{u}}

lemma congr_unit_hom {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H; simp [pullbackCongr]

lemma congr_unit_inv {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).inv.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f').hom := by
  subst H; simp [pullbackCongr]

lemma comp_inv_map_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso (f ≫ g)).hom := by
  erw [← Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom f g]
  erw [Iso.inv_hom_id_app_assoc]

end coh

variable {X : Scheme.{u}}

noncomputable def canTriv (𝒰 : X.OrderedAffineCover) :
    CechTrivialisation 𝒰 (SheafOfModules.unit X.ringCatSheaf) := fun a => pullbackUnitIso (𝒰.U a).ι

lemma canTriv_restrict (𝒰 : X.OrderedAffineCover) {a : 𝒰.ι} {W : X.Opens} (h : W ≤ 𝒰.U a) :
    (canTriv 𝒰).restrict h = pullbackUnitIso W.ι := by
  apply Iso.ext
  change (pullbackCongr (X.homOfLE_ι h)).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackComp (X.homOfLE h) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback (X.homOfLE h)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
          (pullbackUnitIso (X.homOfLE h)).hom =
    (pullbackUnitIso W.ι).hom
  rw [comp_inv_map_unit]
  exact congr_unit_inv _

lemma uAS_eq_one_of_eq_refl {Y : Scheme.{u}} (W : Y.Opens)
    (e : SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf)
    (h : e = Iso.refl _) : unitAutSection W e = 1 := by
  subst h
  exact (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).2

lemma uAS_symm_trans {Y : Scheme.{u}} (W : Y.Opens) {A : ((W : Scheme.{u})).Modules}
    (e : A ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf) :
    unitAutSection W (e.symm ≪≫ e) = 1 :=
  uAS_eq_one_of_eq_refl W _ (Iso.symm_self_id e)

lemma canTriv_transition (𝒰 : X.OrderedAffineCover) (s : 𝒰.Idx 1) : (canTriv 𝒰).transition s = 1 := by
  simp only [CechTrivialisation.transition, canTriv_restrict]
  exact uAS_symm_trans _ _

lemma canTriv_comap (𝒰 : X.OrderedAffineCover) {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g] (a : 𝒰.ι) :
    (canTriv 𝒰).comap g a =
      (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (pullbackUnitIso g) ≪≫
        pullbackUnitIso ((𝒰.comap g).U a).ι := by
  apply Iso.ext
  change (pullbackComp (g ⁻¹ᵁ 𝒰.U a).ι g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackCongr (morphismRestrict_ι g (𝒰.U a)).symm).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackComp (g ∣_ 𝒰.U a) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pullback (g ∣_ 𝒰.U a)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
            (pullbackUnitIso (g ∣_ 𝒰.U a)).hom =
    (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒰.U a).ι).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso (g ⁻¹ᵁ 𝒰.U a).ι).hom
  rw [comp_inv_map_unit, congr_unit_hom]
  exact Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom _ _

end UnitClassZero

theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g) 0 := by
  refine ⟨UnitClassZero.canTriv 𝒰, fun _ => 1, fun _ => 1, fun _ => mul_one 1, fun a => ?_, fun s => ?_⟩
  ·
    rw [map_one, UnitClassZero.canTriv_comap]
    exact (UnitClassZero.uAS_symm_trans _ _).symm
  ·
    rw [UnitClassZero.canTriv_transition, map_one, map_one]
    refine ⟨0, fun _ => 0, fun _ => 0, ?_, fun ξ => ?_⟩
    · simp
    · simp only [LinearMap.comp_apply, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
      rfl
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero
/- Adapted from Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g) 0 := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero.solution
/- Adapted from P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing -/
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension"


noncomputable section

namespace T3G1Kit

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

include hom in

theorem locIso_sliceAt_iff (hP : IsPullback u f' f ψ) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    {R : Type u} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) (x' : SchemeHomOver t' f') :
    LocIsoOnBase (pullback.snd f' t')
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)))
        (𝟙_ ((pullback f' t').Modules)) ↔
      LocIsoOnBase (pullback.snd f (t' ≫ ψ))
        ((Scheme.Modules.pullback (sliceAt f (pushAlong ψ u hu t' x'))).obj (mumfordBundle f L 𝓛))
        (𝟙_ ((pullback f (t' ≫ ψ)).Modules)) := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  let x : SchemeHomOver (t' ≫ ψ) f := pushAlong ψ u hu t' x'
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm

  let r : pullback f (t' ≫ ψ) ⟶ pullback f' t' :=
    pullback.lift
      (hP.lift (pullback.fst f (t' ≫ ψ)) (pullback.snd f (t' ≫ ψ) ≫ t')
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.snd f (t' ≫ ψ)) (by rw [IsPullback.lift_snd])
  let s : pullback f' t' ⟶ pullback f (t' ≫ ψ) :=
    pullback.lift (pullback.fst f' t' ≫ u) (pullback.snd f' t')
      (by rw [Category.assoc, hu, ← Category.assoc, pullback.condition, Category.assoc])
  have hr : r ≫ pullback.snd f' t' = pullback.snd f (t' ≫ ψ) ≫ 𝟙 _ := by
    simp only [r, pullback.lift_snd, Category.comp_id]
  have hs : s ≫ pullback.snd f (t' ≫ ψ) = pullback.snd f' t' ≫ 𝟙 _ := by
    simp only [s, pullback.lift_snd, Category.comp_id]
  have hslice_r : (r ≫ sliceAt f' x') ≫ pp = sliceAt f x := by
    apply pullback.hom_ext
    · simp only [r, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · simp only [r, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have hslice_s : s ≫ sliceAt f x = sliceAt f' x' ≫ pp := by
    apply pullback.hom_ext
    · simp only [s, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [s, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

  let I1r : (Scheme.Modules.pullback r).obj (𝟙_ (pullback f' t').Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso r
  let I2r : (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) :=
    (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso) ≪≫
      (Scheme.Modules.pullbackComp r (sliceAt f' x')).app _ ≪≫
        (Scheme.Modules.pullbackComp (r ≫ sliceAt f' x') pp).app _ ≪≫
          (Scheme.Modules.pullbackCongr hslice_r).app _

  let I1s : (Scheme.Modules.pullback s).obj (𝟙_ (pullback f (t' ≫ ψ)).Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso s
  let I2s : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) :=
    (Scheme.Modules.pullbackComp s (sliceAt f x)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice_s).app _ ≪≫
        ((Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _).symm ≪≫
          (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso.symm
  constructor
  · intro H'
    have Hr := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f' t') (pullback.snd f (t' ≫ ψ)) r (𝟙 _) hr H'
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2r.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hr (locIsoOnBase_of_iso _ I1r))
  · intro H
    have Hs := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f (t' ≫ ψ)) (pullback.snd f' t') s (𝟙 _) hs H
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2s.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hs (locIsoOnBase_of_iso _ I1s))

include hom in

theorem mul_self_eq_one_iff (hP : IsPullback u f' f ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (x' : SchemeHomOver t' f') :
    L'.mul t' x' x' = L'.one t' ↔
      L.mul (t' ≫ ψ) (pushAlong ψ u hu t' x') (pushAlong ψ u hu t' x') = L.one (t' ≫ ψ) := by
  constructor
  · intro h
    rw [← pushAlong_mul L L' ψ u hu hom, h, pushAlong_one L L' ψ u hu hom]
  · intro h
    apply Subtype.ext
    apply hP.hom_ext
    · rw [one_val_comp L L' ψ u hu hom t']
      exact (hom T t' x' x').trans (congrArg Subtype.val h)
    · rw [(L'.mul t' x' x').2, (L'.one t').2]

include hom in

theorem kernelTrivial_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hker : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x' H'
  have hx : pushAlong ψ u hu t' x' = L.one (t' ≫ ψ) :=
    hker R (t' ≫ ψ) (pushAlong ψ u hu t' x') ((locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x').1 H')
  apply Subtype.ext
  apply hP.hom_ext
  · rw [one_val_comp L L' ψ u hu hom t']
    exact congrArg Subtype.val hx
  · rw [x'.2, (L'.one t').2]

include hom in

theorem kernelIsTwoTorsion_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x'
  rw [locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x', hK R (t' ≫ ψ) (pushAlong ψ u hu t' x'),
    mul_self_eq_one_iff L L' ψ u hu hom hP t' x']

include hom in
theorem rosatiCompatible_of_comm {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b : I, act b ≫ f = f)
    (act' : I → (A' ⟶ A')) (act'_over : ∀ b : I, act' b ≫ f' = f') (hact : ∀ b : I, act' b ≫ u = u ≫ act b)
    (star : I → I) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    (hros : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f' L' ((Scheme.Modules.pullback u).obj 𝓛) act' act'_over star := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  intro b
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have comm : pp ≫ (pullback.fst f f ≫ f) = (pullback.fst f' f' ≫ f') ≫ ψ := by
    simp only [pp, Category.assoc, pullback.lift_fst_assoc, hu]
  have H := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    (g := pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') pp ψ comm (hros b)

  let m : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let m' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b)
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  let n : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
      (by rw [Category.assoc, act_over]; exact pullback.condition)
  let n' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f')
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  have hm : m' ≫ pp = pp ≫ m := by
    apply pullback.hom_ext
    · simp only [m, m', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [m, m', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hact]
  have hn : n' ≫ pp = pp ≫ n := by
    apply pullback.hom_ext
    · simp only [n, n', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hact]
    · simp only [n, n', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  let Im : (Scheme.Modules.pullback m').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback m).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback m').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp m' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hm).app _ ≪≫ ((Scheme.Modules.pullbackComp pp m).app _).symm
  let In : (Scheme.Modules.pullback n').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback n).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback n').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp n' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hn).app _ ≪≫ ((Scheme.Modules.pullbackComp pp n).app _).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ Im)
    ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans H (locIsoOnBase_of_iso _ In.symm))

include hom in

theorem isSymmetric_of_comm (𝓛 : A.Modules) (hs : IsSymmetric f L 𝓛) :
    IsSymmetric f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  have h1 : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛))
      ((Scheme.Modules.pullback u).obj 𝓛) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu hs
  have e : (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom)).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans (locIsoOnBase_of_iso f' e) h1

include hom in

theorem root_transport (hP : IsPullback u f' f ψ) (M 𝓛₀ : A.Modules) (h0inv : Scheme.Modules.IsInvertible 𝓛₀)
    (h0ker : KernelTrivial f L 𝓛₀)
    (h0loc : LocIsoOnBase f M (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
        ((Scheme.Modules.pullback u).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛₀)) := by
  refine ⟨h0inv.pullback u, kernelTrivial_of_isPullback L L' ψ u hu hom hP 𝓛₀ h0inv h0ker, ?_⟩
  have H : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
      ((Scheme.Modules.pullback u).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu h0loc
  refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans H (locIsoOnBase_of_iso f' ?_)
  exact Scheme.Modules.pullbackTensorObjIso u _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛₀ ≪≫
        (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom).symm).app 𝓛₀ ≪≫
        ((Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛₀).symm)

end Hom

end T3G1Kit
p2m_reactivate "ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.T3G1Kit"

namespace P2N12

noncomputable def dualIso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm
end P2N12
p2m_reactivate "ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.T3G1Kit"

theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [IsNoetherianRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hK : RingHom.ker (algebraMap B₁ B₀) * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    (hKm : IsLocalRing.maximalIdeal B₁ * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of B₁)}
    (L : RelativeGroupLaw B₁ f) (hA : AbelianSchemePropertyBundle B₁ f)
    {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t' f₀),
      (L₀.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (M M' : (pullback f f).Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')

    (h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M'))

    (h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M ≅ 𝟙_ _))
    (h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M) ≅ 𝟙_ _))
    (h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M' ≅ 𝟙_ _))
    (h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M') ≅ 𝟙_ _)) :
    Nonempty (M ≅ M') := by
  classical

  let π : B₁ →+* B₀ := algebraMap B₁ B₀
  let X := pullback f f
  let F : X ⟶ Spec (CommRingCat.of B₁) := pullback.fst f f ≫ f
  let X₀ := pullback f₀ f₀
  let F₀ : X₀ ⟶ Spec (CommRingCat.of B₀) := pullback.fst f₀ f₀ ≫ f₀
  let gg : X₀ ⟶ X := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc])
  let rk := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B₁))
  let Ak := pullback f rk
  let gk : Ak ⟶ A := pullback.fst f rk
  let fk : Ak ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) := pullback.snd f rk
  have hAk_sq : IsPullback gk fk f rk := IsPullback.of_hasPullback _ _
  let Xk := pullback fk fk
  let Fk : Xk ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) := pullback.fst fk fk ≫ fk
  let ii : Xk ⟶ X := pullback.lift (pullback.fst fk fk ≫ gk) (pullback.snd fk fk ≫ gk)
    (by rw [Category.assoc, Category.assoc, hAk_sq.w, ← Category.assoc, pullback.condition, Category.assoc])

  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : IsSeparated f := inferInstance
  haveI : Flat f := inferInstance
  haveI : IsSeparated F := inferInstance
  haveI : Flat F := inferInstance
  haveI : CompactSpace ↥A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)

  have prodCart : ∀ {S' : Scheme.{u}} {A' : Scheme.{u}} (f' : A' ⟶ S') (u : A' ⟶ A) (s : S' ⟶ Spec (CommRingCat.of B₁))
      (hu : IsPullback u f' f s) (uu : pullback f' f' ⟶ X) (h1 : uu ≫ pullback.fst f f = pullback.fst f' f' ≫ u)
      (h2 : uu ≫ pullback.snd f f = pullback.snd f' f' ≫ u),
      IsPullback uu (pullback.fst f' f' ≫ f') F s := by
    intro S' A' f' u s hu uu h1 h2
    have sq₀ : IsPullback (pullback.snd f' f') (pullback.fst f' f') f' f' := (IsPullback.of_hasPullback _ _).flip
    have sqX : IsPullback (pullback.snd f f) (pullback.fst f f) f f := (IsPullback.of_hasPullback _ _).flip
    have O : IsPullback (uu ≫ pullback.snd f f) (pullback.fst f' f') f (u ≫ f) := by
      rw [h2, hu.w]; exact sq₀.paste_horiz hu
    have hq : IsPullback uu (pullback.fst f' f') (pullback.fst f f) u := IsPullback.of_right O h1 sqX
    exact hq.paste_vert hu
  have hgg : IsPullback gg F₀ F (Spec.map (CommRingCat.ofHom π)) :=
    prodCart f₀ g _ hg gg (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hii : IsPullback ii Fk F rk :=
    prodCart fk gk rk hAk_sq ii (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion gg := MorphismProperty.of_isPullback hgg.flip inferInstance
  haveI : IsClosedImmersion rk := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion ii := MorphismProperty.of_isPullback hii.flip inferInstance
  haveI : IsClosedImmersion gk := MorphismProperty.of_isPullback hAk_sq.flip inferInstance
  haveI : IsClosedImmersion g := MorphismProperty.of_isPullback hg.flip inferInstance
  have hAk : AbelianSchemePropertyBundle (IsLocalRing.ResidueField B₁) fk := hA.of_isPullback hAk_sq

  have hker_top : RingHom.ker π ≠ ⊤ := by
    intro h
    have h1 : (1 : B₁) ∈ RingHom.ker π * RingHom.ker π := by
      simpa only [h, Ideal.top_mul] using (Submodule.mem_top : (1 : B₁) ∈ (⊤ : Ideal B₁))
    rw [hK] at h1
    exact one_ne_zero ((Submodule.mem_bot B₁).mp h1)
  have hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁ := IsLocalRing.le_maximalIdeal hker_top
  have hsmall' : RingHom.ker π * IsLocalRing.maximalIdeal B₁ = ⊥ := by rw [mul_comm]; exact hKm
  let V : Submodule B₁ B₁ := RingHom.ker π
  have hVtors : Module.IsTorsionBySet B₁ ↥V (IsLocalRing.maximalIdeal B₁ : Set B₁) := by
    rintro v ⟨m, hm⟩
    refine Subtype.ext ?_
    have : m * (v : B₁) ∈ IsLocalRing.maximalIdeal B₁ * RingHom.ker π := Ideal.mul_mem_mul hm v.2
    rw [hKm] at this
    simpa [smul_eq_mul, mul_comm] using (Submodule.mem_bot B₁).mp this
  letI modV : Module (IsLocalRing.ResidueField B₁) ↥V := hVtors.module
  haveI : IsScalarTower B₁ (IsLocalRing.ResidueField B₁) ↥V := hVtors.isScalarTower
  haveI : Module.Finite B₁ ↥V := inferInstance
  haveI : Module.Finite (IsLocalRing.ResidueField B₁) ↥V :=
    Module.Finite.of_restrictScalars_finite B₁ (IsLocalRing.ResidueField B₁) ↥V
  have hιI : LinearMap.range V.subtype = Submodule.restrictScalars B₁ (RingHom.ker π) := by
    rw [Submodule.range_subtype, Submodule.restrictScalars_self]
  have hJ : ∀ v w : ↥V, V.subtype v * V.subtype w = 0 := by
    intro v w
    have : (v : B₁) * (w : B₁) ∈ RingHom.ker π * RingHom.ker π := Ideal.mul_mem_mul v.2 w.2
    rw [hK] at this
    exact (Submodule.mem_bot B₁).mp this

  let N : X.Modules := M ⊗ Scheme.Modules.dual M'
  have hN : Scheme.Modules.IsInvertible N :=
    hM.tensor_monoidalV2 (Scheme.Modules.IsInvertible.dual_monoidalV2 hM').1
  obtain ⟨e0⟩ := h0
  let φ₀ : (Scheme.Modules.pullback gg).obj N ≅ SheafOfModules.unit X₀.ringCatSheaf :=
    Scheme.Modules.pullbackTensorObjIso gg M (Scheme.Modules.dual M') ≪≫
      whiskerLeftIso _ ((Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 gg hM').some ≪≫
        (P2N12.dualIso e0).symm) ≪≫
      (Scheme.Modules.IsInvertible.dual_monoidalV2 (hM.pullback gg)).2.some

  obtain ⟨𝒰₀, ⟨τ⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible (𝟙 X) N hN
  obtain ⟨w, hw, hwcl⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_cechTrivialisation
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI
      F F₀ gg hgg Fk ii hii (𝒰₀.comap (𝟙 _)) N τ φ₀

  let e₁ : Spec (CommRingCat.of B₁) ⟶ A := (L.one (𝟙 _)).1
  have he₁ : e₁ ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  let e₀ : Spec (CommRingCat.of B₀) ⟶ A₀ := (L₀.one (𝟙 _)).1
  have he₀ : e₀ ≫ f₀ = 𝟙 _ := (L₀.one (𝟙 _)).2
  let Lk := L.baseChange rk
  let ek : Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) ⟶ Ak := (Lk.one (𝟙 _)).1
  have hek : ek ≫ fk = 𝟙 _ := (Lk.one (𝟙 _)).2

  have homk : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)))
      (P Q : SchemeHomOver t' fk),
      (Lk.mul t' P Q).1 ≫ gk =
        (L.mul (t' ≫ rk) ⟨P.1 ≫ gk, by rw [Category.assoc, hAk_sq.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gk, by rw [Category.assoc, hAk_sq.w, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul rk L t' P Q)
  have he₀g : e₀ ≫ g = Spec.map (CommRingCat.ofHom π) ≫ e₁ := by
    have h1 := T3G1Kit.one_val_comp L L₀ (Spec.map (CommRingCat.ofHom π)) g hg.w (fun T t' P Q => hg_mul t' P Q) (𝟙 _)
    have h2 := congrArg Subtype.val
      (L.one_natural (𝟙 _) ((𝟙 _) ≫ Spec.map (CommRingCat.ofHom π)) (Spec.map (CommRingCat.ofHom π)) (by simp))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    exact h1.trans h2.symm
  have hekg : ek ≫ gk = rk ≫ e₁ := by
    have h1 := T3G1Kit.one_val_comp L Lk rk gk hAk_sq.w homk (𝟙 _)
    have h2 := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 _) ≫ rk) rk (by simp))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    exact h1.trans h2.symm
  let s₁ : A ⟶ X := pullback.lift (𝟙 A) (f ≫ e₁) (by simp [he₁])
  let s₂ : A ⟶ X := pullback.lift (f ≫ e₁) (𝟙 A) (by simp [he₁])
  let s0₁ : A₀ ⟶ X₀ := pullback.lift (𝟙 A₀) (f₀ ≫ e₀) (by simp [he₀])
  let s0₂ : A₀ ⟶ X₀ := pullback.lift (f₀ ≫ e₀) (𝟙 A₀) (by simp [he₀])
  let sk₁ : Ak ⟶ Xk := pullback.lift (𝟙 Ak) (fk ≫ ek) (by simp [hek])
  let sk₂ : Ak ⟶ Xk := pullback.lift (fk ≫ ek) (𝟙 Ak) (by simp [hek])
  have s₁f : s₁ ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have s₁s : s₁ ≫ pullback.snd f f = f ≫ e₁ := pullback.lift_snd _ _ _
  have s₂f : s₂ ≫ pullback.fst f f = f ≫ e₁ := pullback.lift_fst _ _ _
  have s₂s : s₂ ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
  have s0₁f : s0₁ ≫ pullback.fst f₀ f₀ = 𝟙 A₀ := pullback.lift_fst _ _ _
  have s0₁s : s0₁ ≫ pullback.snd f₀ f₀ = f₀ ≫ e₀ := pullback.lift_snd _ _ _
  have s0₂f : s0₂ ≫ pullback.fst f₀ f₀ = f₀ ≫ e₀ := pullback.lift_fst _ _ _
  have s0₂s : s0₂ ≫ pullback.snd f₀ f₀ = 𝟙 A₀ := pullback.lift_snd _ _ _
  have sk₁f : sk₁ ≫ pullback.fst fk fk = 𝟙 Ak := pullback.lift_fst _ _ _
  have sk₁s : sk₁ ≫ pullback.snd fk fk = fk ≫ ek := pullback.lift_snd _ _ _
  have sk₂f : sk₂ ≫ pullback.fst fk fk = fk ≫ ek := pullback.lift_fst _ _ _
  have sk₂s : sk₂ ≫ pullback.snd fk fk = 𝟙 Ak := pullback.lift_snd _ _ _
  have ggf : gg ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g := pullback.lift_fst _ _ _
  have ggs : gg ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g := pullback.lift_snd _ _ _
  have iif : ii ≫ pullback.fst f f = pullback.fst fk fk ≫ gk := pullback.lift_fst _ _ _
  have iis : ii ≫ pullback.snd f f = pullback.snd fk fk ≫ gk := pullback.lift_snd _ _ _
  have hs₁F : s₁ ≫ F = f := by
    show s₁ ≫ pullback.fst f f ≫ f = f
    rw [← Category.assoc, s₁f, Category.id_comp]
  have hs₂F : s₂ ≫ F = f := by
    show s₂ ≫ pullback.fst f f ≫ f = f
    rw [← Category.assoc, s₂f, Category.assoc, he₁, Category.comp_id]
  have hs0₁ : s0₁ ≫ gg = g ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ggf, ← Category.assoc, s0₁f, Category.id_comp, Category.assoc, s₁f, Category.comp_id]
    · rw [Category.assoc, ggs, ← Category.assoc, s0₁s, Category.assoc, he₀g, ← Category.assoc, ← hg.w]
      simp only [Category.assoc, s₁s]
  have hs0₂ : s0₂ ≫ gg = g ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ggf, ← Category.assoc, s0₂f, Category.assoc, he₀g, ← Category.assoc, ← hg.w]
      simp only [Category.assoc, s₂f]
    · rw [Category.assoc, ggs, ← Category.assoc, s0₂s, Category.id_comp, Category.assoc, s₂s, Category.comp_id]
  have hsk₁ : sk₁ ≫ ii = gk ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, iif, ← Category.assoc, sk₁f, Category.id_comp, Category.assoc, s₁f, Category.comp_id]
    · rw [Category.assoc, iis, ← Category.assoc, sk₁s, Category.assoc, hekg, ← Category.assoc, ← hAk_sq.w]
      simp only [Category.assoc, s₁s]
  have hsk₂ : sk₂ ≫ ii = gk ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, iif, ← Category.assoc, sk₂f, Category.assoc, hekg, ← Category.assoc, ← hAk_sq.w]
      simp only [Category.assoc, s₂f]
    · rw [Category.assoc, iis, ← Category.assoc, sk₂s, Category.id_comp, Category.assoc, s₂s, Category.comp_id]
  have hsk₁F : sk₁ ≫ Fk = fk := by
    show sk₁ ≫ pullback.fst fk fk ≫ fk = fk
    rw [← Category.assoc, sk₁f, Category.id_comp]
  have hsk₂F : sk₂ ≫ Fk = fk := by
    show sk₂ ≫ pullback.fst fk fk ≫ fk = fk
    rw [← Category.assoc, sk₂f, Category.assoc, hek, Category.comp_id]

  obtain ⟨𝒱, lam, hlam⟩ := AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    (fun _ : Fin 2 => X) (fun j => if j = 0 then s₁ else s₂) (fun _ => 𝒰₀.comap (𝟙 _))
  have hlam₁ : ∀ v, 𝒱.U v ≤ s₁ ⁻¹ᵁ (𝒰₀.comap (𝟙 _)).U (lam 0 v) := fun v => by simpa using hlam 0 v
  have hlam₂ : ∀ v, 𝒱.U v ≤ s₂ ⁻¹ᵁ (𝒰₀.comap (𝟙 _)).U (lam 1 v) := fun v => by simpa using hlam 1 v
  have hlamk₁ : ∀ v, (𝒱.comap gk).U v ≤ sk₁ ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap ii).U (lam 0 v) := by
    intro v
    show gk ⁻¹ᵁ 𝒱.U v ≤ sk₁ ⁻¹ᵁ (ii ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam 0 v)))
    rw [← Scheme.Hom.comp_preimage, hsk₁, Scheme.Hom.comp_preimage]
    exact fun p hp => hlam₁ v hp
  have hlamk₂ : ∀ v, (𝒱.comap gk).U v ≤ sk₂ ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap ii).U (lam 1 v) := by
    intro v
    show gk ⁻¹ᵁ 𝒱.U v ≤ sk₂ ⁻¹ᵁ (ii ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam 1 v)))
    rw [← Scheme.Hom.comp_preimage, hsk₂, Scheme.Hom.comp_preimage]
    exact fun p hp => hlam₂ v hp

  obtain ⟨w₁, hw₁eq, hw₁⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      F f gg g Fk fk ii gk s₁ hs₁F s0₁ hs0₁ sk₁ hsk₁ hsk₁F (𝒰₀.comap (𝟙 _)) 𝒱 (lam 0) hlam₁ hlamk₁ N φ₀ w hw
  obtain ⟨w₂, hw₂eq, hw₂⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      F f gg g Fk fk ii gk s₂ hs₂F s0₂ hs0₂ sk₂ hsk₂ hsk₂F (𝒰₀.comap (𝟙 _)) 𝒱 (lam 1) hlam₂ hlamk₂ N φ₀ w hw

  let φ := pullback.fst f (𝟙 (Spec (CommRingCat.of B₁)))
  have hφ : pullback.snd f (𝟙 (Spec (CommRingCat.of B₁))) = φ ≫ f := by
    have := pullback.condition (f := f) (g := 𝟙 (Spec (CommRingCat.of B₁)))
    rw [Category.comp_id] at this
    exact this.symm
  have hsl₁ : sliceAt f (L.one (𝟙 _)) = φ ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, s₁f, Category.comp_id]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, s₁s, ← Category.assoc, ← hφ]; exact pullback.lift_snd _ _ _
  have hsl₂ : sliceAt f (L.one (𝟙 _)) ≫ (pullbackSymmetry f f).hom = φ ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, Category.assoc, s₂f, ← Category.assoc, ← hφ]
      exact pullback.lift_snd _ _ _
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, Category.assoc, s₂s, Category.comp_id]
      exact pullback.lift_fst _ _ _
  have bridge : ∀ (t : pullback f (𝟙 (Spec (CommRingCat.of B₁))) ⟶ X) (s : A ⟶ X) (hts : t = φ ≫ s) (P : X.Modules)
      (e : (Scheme.Modules.pullback t).obj P ≅ 𝟙_ _), Nonempty ((Scheme.Modules.pullback s).obj P ≅ 𝟙_ A.Modules) := by
    intro t s hts P e
    have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback s).obj P) ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackComp φ s).app P ≪≫ (Scheme.Modules.pullbackCongr hts.symm).app P ≪≫ e
    let back : ∀ Q : A.Modules, (Scheme.Modules.pullback (inv φ)).obj ((Scheme.Modules.pullback φ).obj Q) ≅ Q := fun Q =>
      (Scheme.Modules.pullbackComp (inv φ) φ).app Q ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app Q ≪≫
        (Scheme.Modules.pullbackId A).app Q
    exact ⟨(back _).symm ≪≫ (Scheme.Modules.pullback (inv φ)).mapIso e1 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso (inv φ)⟩
  have trivN : ∀ (s : A ⟶ X) (a : (Scheme.Modules.pullback s).obj M ≅ 𝟙_ _) (b : (Scheme.Modules.pullback s).obj M' ≅ 𝟙_ _),
      (Scheme.Modules.pullback s).obj N ≅ SheafOfModules.unit A.ringCatSheaf := fun s a b =>
    Scheme.Modules.pullbackTensorObjIso s M (Scheme.Modules.dual M') ≪≫
      (a ⊗ᵢ ((Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 s hM').some ≪≫ P2N12.dualIso b)) ≪≫
      (Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.isInvertible_unit A)).2.some
  obtain ⟨a₁⟩ := bridge _ s₁ hsl₁ M h1.some
  obtain ⟨b₁⟩ := bridge _ s₁ hsl₁ M' h1'.some
  obtain ⟨a₂⟩ := bridge _ s₂ hsl₂ M
    (((Scheme.Modules.pullbackComp (sliceAt f (L.one (𝟙 _))) (pullbackSymmetry f f).hom).app M).symm ≪≫ h2.some)
  obtain ⟨b₂⟩ := bridge _ s₂ hsl₂ M'
    (((Scheme.Modules.pullbackComp (sliceAt f (L.one (𝟙 _))) (pullbackSymmetry f f).hom).app M').symm ≪≫ h2'.some)
  have ε₁ : (Scheme.Modules.pullback s₁).obj N ≅ SheafOfModules.unit A.ringCatSheaf := trivN s₁ a₁ b₁
  have ε₂ : (Scheme.Modules.pullback s₂).obj N ≅ SheafOfModules.unit A.ringCatSheaf := trivN s₂ a₂ b₂

  have hH1 : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom := by
    have hsq : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id B₁))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact hA.bijective_specIso_inv_comp_appTop_of_isPullback (RingHom.id B₁) f (𝟙 A) hsq
  have hH0 : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom :=
    hA.bijective_specIso_inv_comp_appTop_of_isPullback π f₀ g hg
  obtain ⟨uas_trans, uas_refl⟩ := AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl (Y := A₀) ⊤

  have hcob : ∀ (s : A ⟶ X) (ε : (Scheme.Modules.pullback s).obj N ≅ SheafOfModules.unit A.ringCatSheaf)
      (φ' : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj N) ≅ SheafOfModules.unit A₀.ringCatSheaf)
      (w' : Module.Dual (IsLocalRing.ResidueField B₁) ↥V →ₗ[IsLocalRing.ResidueField B₁]
        (OModulePresheaf.unit fk).cochain (𝒱.comap gk) 1)
      (hw' : IsPicDeformationCocycle ↥V V.subtype f fk gk g 𝒱 ((Scheme.Modules.pullback s).obj N) φ' w'),
      ∀ ξ, w' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒱.comap gk) 0) := by
    intro s ε φ' w' hw' ξ

    have h7 := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso ↥V V.subtype f fk gk g 𝒱 ε φ' w' hw'
    let ψ := (Scheme.Modules.pullback g).mapIso ε.symm ≪≫ φ'
    let φc := Scheme.Modules.pullbackUnitIso g
    let δ := (Scheme.Modules.pullbackUnitIso (⊤ : A₀.Opens).ι).symm ≪≫
      (Scheme.Modules.pullback (⊤ : A₀.Opens).ι).mapIso (ψ.symm ≪≫ φc) ≪≫ Scheme.Modules.pullbackUnitIso (⊤ : A₀.Opens).ι
    have hδu : IsUnit (Scheme.Modules.unitAutSection ⊤ δ) := by
      refine IsUnit.of_mul_eq_one (b := Scheme.Modules.unitAutSection ⊤ δ.symm) ?_
      rw [← uas_trans]
      convert uas_refl using 2
      exact Iso.self_symm_id δ
    obtain ⟨u, hu, hgu⟩ := AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
      π hπ hI f f₀ g hg.w hH1 hH0 _ hδu
    have h8 := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection ↥V V.subtype f fk gk g 𝒱
      (SheafOfModules.unit A.ringCatSheaf) ψ φc u (↑hu.unit⁻¹ : Γ(A, ⊤)) hu.mul_val_inv hgu w' h7

    have h0' := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero ↥V V.subtype f fk gk g 𝒱
    have hd := AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI f f₀ g hg fk gk hAk_sq 𝒱 _ _ w' 0 h8 h0' ξ
    simpa using hd
  have hc₁ := hcob s₁ ε₁ _ w₁ hw₁
  have hc₂ := hcob s₂ ε₂ _ w₂ hw₂

  have hKun : ∀ ξ, w ξ ∈ LinearMap.range ((OModulePresheaf.unit Fk).d ((𝒰₀.comap (𝟙 _)).comap ii) 0) := by
    intro ξ
    refine GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
      (IsLocalRing.ResidueField B₁) fk hAk ek hek sk₁ sk₂ sk₁f sk₁s sk₂f sk₂s ((𝒰₀.comap (𝟙 _)).comap ii) (𝒱.comap gk) (𝒱.comap gk)
      (lam 0) (lam 1) hlamk₁ hlamk₂ (w ξ) (hwcl ξ) ?_ ?_
    · rw [← hw₁eq ξ]; exact hc₁ ξ
    · rw [← hw₂eq ξ]; exact hc₂ ξ

  obtain ⟨eN⟩ := AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI F F₀ gg hgg Fk ii hii (𝒰₀.comap (𝟙 _)) N φ₀ w hw hKun
  have eMM' : Scheme.Modules.dual M' ⊗ M' ≅ 𝟙_ X.Modules :=
    β_ _ _ ≪≫ (Scheme.Modules.IsInvertible.dual_monoidalV2 hM').2.some
  exact ⟨(ρ_ M).symm ≪≫ whiskerLeftIso M eMM'.symm ≪≫ (α_ M (Scheme.Modules.dual M') M').symm ≪≫
    whiskerRightIso eN M' ≪≫ λ_ M'⟩
end
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
/- Adapted from Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

private theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [IsNoetherianRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hK : RingHom.ker (algebraMap B₁ B₀) * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    (hKm : IsLocalRing.maximalIdeal B₁ * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of B₁)}
    (L : RelativeGroupLaw B₁ f) (hA : AbelianSchemePropertyBundle B₁ f)
    {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t' f₀),
      (L₀.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (M M' : (pullback f f).Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')

    (h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M'))

    (h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M ≅ 𝟙_ _))
    (h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M) ≅ 𝟙_ _))
    (h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M' ≅ 𝟙_ _))
    (h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M') ≅ 𝟙_ _)) :
    Nonempty (M ≅ M') := by p2m_exact_reverting @_root_.ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.solution
#print axioms ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.Deformation.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.solution
end


universe u
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeGeometry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped CategoryTheory.MonObj

noncomputable section

namespace CubePBS

p2m_open "CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry.RelPicard"

section Skel

universe v' u'
variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]

theorem cls_tensor (A B : C) : toSkeleton (A ⊗ B) = toSkeleton A * toSkeleton B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

theorem cls_congr {A B : C} (e : A ≅ B) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

theorem cls_of_nonempty {A B : C} (e : Nonempty (A ≅ B)) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr e

end Skel

section Pull

variable {S T V : Scheme.{u}}

noncomputable abbrev pcls (φ : S ⟶ T) (A : T.Modules) : Skeleton S.Modules :=
  toSkeleton ((Scheme.Modules.pullback φ).obj A)

theorem pcls_tensor (φ : S ⟶ T) (A B : T.Modules) :
    pcls φ (A ⊗ B) = pcls φ A * pcls φ B := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorObjIso φ A B), cls_tensor]

theorem pcls_unit (φ : S ⟶ T) : pcls φ (𝟙_ T.Modules) = 1 := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorUnitObjIso φ), cls_unit]

theorem pcls_comp (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    pcls φ ((Scheme.Modules.pullback ψ).obj A) = pcls (φ ≫ ψ) A :=
  cls_congr ((Scheme.Modules.pullbackComp φ ψ).app A)

theorem pcls_congr_hom {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) : pcls φ A = pcls ψ A := by
  subst h; rfl

theorem pcls_congr_obj (φ : S ⟶ T) {A B : T.Modules} (h : toSkeleton A = toSkeleton B) :
    pcls φ A = pcls φ B :=
  cls_congr ((Scheme.Modules.pullback φ).mapIso (Skeleton.isoOfEq h))

theorem pcls_eq_one_of_cls_eq_one (φ : S ⟶ T) {A : T.Modules} (h : toSkeleton A = 1) :
    pcls φ A = 1 := by
  rw [pcls_congr_obj φ (h.trans cls_unit.symm), pcls_unit]

theorem cls_mul_cls_dual {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    toSkeleton A * toSkeleton (Scheme.Modules.dual A) = 1 := by
  rw [← cls_tensor, cls_of_nonempty hA.dual_monoidalV2.2, cls_unit]

theorem pcls_dual (φ : S ⟶ T) {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    pcls φ (Scheme.Modules.dual A) =
      toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback φ).obj A)) :=
  cls_of_nonempty (hA.pullback_dual_monoidalV2 φ)

end Pull

section Generic

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    [GrpObj (Over.mk f)] (𝓛 : X.Modules) (e : Spec (CommRingCat.of S) ⟶ X)

noncomputable abbrev P {T : Over (Spec (CommRingCat.of S))} (g : T ⟶ Over.mk f) : T.left.Modules :=
  (Scheme.Modules.pullback g.left).obj 𝓛

noncomputable abbrev Λ {T : Over (Spec (CommRingCat.of S))} (g : T ⟶ Over.mk f) : Skeleton T.left.Modules :=
  pcls g.left 𝓛

theorem Λ_comp {T T' : Over (Spec (CommRingCat.of S))} (σ : T' ⟶ T) (g : T ⟶ Over.mk f) :
    pcls σ.left (P f 𝓛 g) = Λ f 𝓛 (σ ≫ g) := by
  rw [Λ, Over.comp_left]; exact pcls_comp _ _ _

noncomputable abbrev EM (T : Over (Spec (CommRingCat.of S))) : T.left.Modules :=
  (Scheme.Modules.pullback T.hom).obj ((Scheme.Modules.pullback e).obj 𝓛)

noncomputable abbrev Ecls (T : Over (Spec (CommRingCat.of S))) : Skeleton T.left.Modules :=
  pcls T.hom ((Scheme.Modules.pullback e).obj 𝓛)

theorem Ecls_comp {T T' : Over (Spec (CommRingCat.of S))} (σ : T' ⟶ T) :
    pcls σ.left (EM 𝓛 e T) = Ecls 𝓛 e T' := by
  rw [EM, pcls_comp, pcls_congr_hom (Over.w σ)]

abbrev A3 : Over (Spec (CommRingCat.of S)) := (Over.mk f ⊗ Over.mk f) ⊗ Over.mk f

abbrev p₁ : A3 f ⟶ Over.mk f := fst _ _ ≫ fst _ _
abbrev p₂ : A3 f ⟶ Over.mk f := fst _ _ ≫ snd _ _
abbrev p₃ : A3 f ⟶ Over.mk f := snd _ _

noncomputable abbrev M₁ : (A3 f).left.Modules :=
  P f 𝓛 (p₁ f * p₂ f * p₃ f) ⊗ (P f 𝓛 (p₁ f) ⊗ (P f 𝓛 (p₂ f) ⊗ P f 𝓛 (p₃ f)))

noncomputable abbrev M₂ : (A3 f).left.Modules :=
  P f 𝓛 (p₁ f * p₂ f) ⊗ (P f 𝓛 (p₁ f * p₃ f) ⊗ (P f 𝓛 (p₂ f * p₃ f) ⊗ EM 𝓛 e (A3 f)))

theorem isInvertible_M₁ (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (M₁ f 𝓛) :=
  (hL.pullback _).tensor_monoidalV2 ((hL.pullback _).tensor_monoidalV2
    ((hL.pullback _).tensor_monoidalV2 (hL.pullback _)))

theorem isInvertible_M₂ (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (M₂ f 𝓛 e) :=
  (hL.pullback _).tensor_monoidalV2 ((hL.pullback _).tensor_monoidalV2
    ((hL.pullback _).tensor_monoidalV2 ((hL.pullback _).pullback _)))

theorem pcls_M₁ {T : Over (Spec (CommRingCat.of S))} (σ : T ⟶ A3 f) (a b c : T ⟶ Over.mk f)
    (ha : σ ≫ p₁ f = a) (hb : σ ≫ p₂ f = b) (hc : σ ≫ p₃ f = c) :
    pcls σ.left (M₁ f 𝓛) =
      Λ f 𝓛 (a * b * c) * (Λ f 𝓛 a * (Λ f 𝓛 b * Λ f 𝓛 c)) := by
  rw [M₁, pcls_tensor, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp, Λ_comp,
    MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

theorem pcls_M₂ {T : Over (Spec (CommRingCat.of S))} (σ : T ⟶ A3 f) (a b c : T ⟶ Over.mk f)
    (ha : σ ≫ p₁ f = a) (hb : σ ≫ p₂ f = b) (hc : σ ≫ p₃ f = c) :
    pcls σ.left (M₂ f 𝓛 e) =
      Λ f 𝓛 (a * b) * (Λ f 𝓛 (a * c) * (Λ f 𝓛 (b * c) * Ecls 𝓛 e T)) := by
  rw [M₂, pcls_tensor, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp, Ecls_comp,
    MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

noncomputable abbrev N : (A3 f).left.Modules :=
  M₁ f 𝓛 ⊗ Scheme.Modules.dual (M₂ f 𝓛 e)

theorem isInvertible_N (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (N f 𝓛 e) :=
  (isInvertible_M₁ f 𝓛 hL).tensor_monoidalV2 (isInvertible_M₂ f 𝓛 e hL).dual_monoidalV2.1

theorem slice_trivial (hL : Scheme.Modules.IsInvertible 𝓛) {T : Over (Spec (CommRingCat.of S))}
    (σ : T ⟶ A3 f)
    (h : pcls σ.left (M₁ f 𝓛) = pcls σ.left (M₂ f 𝓛 e)) :
    Nonempty ((Scheme.Modules.pullback σ.left).obj (N f 𝓛 e) ≅ 𝟙_ _) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [← pcls, N, pcls_tensor, h, pcls_dual _ (isInvertible_M₂ f 𝓛 e hL), pcls,
    cls_mul_cls_dual ((isInvertible_M₂ f 𝓛 e hL).pullback _), cls_unit]

theorem cls_M₁_eq_cls_M₂ (hL : Scheme.Modules.IsInvertible 𝓛) (hN : Nonempty (N f 𝓛 e ≅ 𝟙_ _)) :
    toSkeleton (M₁ f 𝓛) = toSkeleton (M₂ f 𝓛 e) := by
  have h1 : toSkeleton (N f 𝓛 e) = 1 := by rw [cls_of_nonempty hN, cls_unit]
  rw [N, cls_tensor] at h1
  have h2 := cls_mul_cls_dual (isInvertible_M₂ f 𝓛 e hL)
  calc toSkeleton (M₁ f 𝓛)
      = toSkeleton (M₁ f 𝓛) * (toSkeleton (M₂ f 𝓛 e) * toSkeleton (Scheme.Modules.dual (M₂ f 𝓛 e))) := by
        rw [h2, mul_one]
    _ = toSkeleton (M₁ f 𝓛) * toSkeleton (Scheme.Modules.dual (M₂ f 𝓛 e)) * toSkeleton (M₂ f 𝓛 e) := by
        rw [mul_assoc, mul_comm (toSkeleton (M₂ f 𝓛 e))]
    _ = toSkeleton (M₂ f 𝓛 e) := by rw [h1, one_mul]

theorem main (hL : Scheme.Modules.IsInvertible 𝓛) (hN : Nonempty (N f 𝓛 e ≅ 𝟙_ _))
    {Y : Over (Spec (CommRingCat.of S))} (g₁ g₂ g₃ : Y ⟶ Over.mk f) :
    Nonempty (
      (Scheme.Modules.pullback (g₁ * g₂ * g₃).left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₁.left).obj 𝓛 ⊗
          (Scheme.Modules.pullback g₂.left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₃.left).obj 𝓛 ≅
        (Scheme.Modules.pullback (g₁ * g₂).left).obj 𝓛 ⊗ (Scheme.Modules.pullback (g₁ * g₃).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (g₂ * g₃).left).obj 𝓛 ⊗
            (Scheme.Modules.pullback Y.hom).obj ((Scheme.Modules.pullback e).obj 𝓛)) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  let φ : Y ⟶ A3 f := lift (lift g₁ g₂) g₃
  have ha : φ ≫ p₁ f = g₁ := by rw [lift_fst_assoc, lift_fst]
  have hb : φ ≫ p₂ f = g₂ := by rw [lift_fst_assoc, lift_snd]
  have hc : φ ≫ p₃ f = g₃ := lift_snd _ _
  have E := pcls_congr_obj φ.left (cls_M₁_eq_cls_M₂ f 𝓛 e hL hN)
  rw [pcls_M₁ f 𝓛 φ g₁ g₂ g₃ ha hb hc, pcls_M₂ f 𝓛 e φ g₁ g₂ g₃ ha hb hc] at E
  simpa only [cls_tensor] using E

end Generic

section WithLaw

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (G : RelativeGroupLaw S f) (𝓛 : X.Modules)

abbrev eG : Spec (CommRingCat.of S) ⟶ X := (G.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem one_left (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    (1 : T ⟶ Over.mk f).left = (G.one T.hom).1 := by
  letI := G.grpObjOverMk
  exact congrArg Subtype.val (G.overHomEquivSchemeHomOver_one T)

theorem one_left' (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    (1 : T ⟶ Over.mk f).left = T.hom ≫ eG f G := by
  letI := G.grpObjOverMk
  rw [one_left]
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of S))) T.hom T.hom (Category.comp_id _)
  exact (congrArg Subtype.val h).symm

theorem Λ_one (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    Λ f 𝓛 (1 : T ⟶ Over.mk f) = Ecls 𝓛 (eG f G) T := by
  letI := G.grpObjOverMk
  rw [Λ, pcls_congr_hom (one_left' f G T)]
  exact (pcls_comp _ _ _).symm

abbrev F₁ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift
    (pullback.lift (G.one (prodStr f f)).1 (pullback.fst f f) (by rw [(G.one _).2]))
    (pullback.snd f f)
    (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition)

abbrev F₂ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift
    (pullback.lift (pullback.fst f f) (G.one (prodStr f f)).1 (by rw [(G.one _).2]))
    (pullback.snd f f)
    (by rw [pullback.lift_fst_assoc]; exact pullback.condition)

abbrev F₃ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift (𝟙 _) (G.one (prodStr f f)).1 (by rw [Category.id_comp, (G.one _).2])

abbrev F₀ : X ⟶ pullback (prodStr f f) f :=
  rigSection (prodStr f f) f ((G.prod G).one (𝟙 (Spec (CommRingCat.of S))))

theorem F₁_fst_fst : F₁ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_fst_assoc, pullback.lift_fst]
theorem F₁_fst_snd : F₁ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, pullback.lift_snd]
theorem F₁_snd : F₁ f G ≫ pullback.snd _ _ = pullback.snd f f := by
  rw [pullback.lift_snd]
theorem F₂_fst_fst : F₂ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, pullback.lift_fst]
theorem F₂_fst_snd : F₂ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_fst_assoc, pullback.lift_snd]
theorem F₂_snd : F₂ f G ≫ pullback.snd _ _ = pullback.snd f f := by
  rw [pullback.lift_snd]
theorem F₃_fst_fst : F₃ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, Category.id_comp]
theorem F₃_fst_snd : F₃ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f f := by
  rw [pullback.lift_fst_assoc, Category.id_comp]
theorem F₃_snd : F₃ f G ≫ pullback.snd _ _ = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_snd]
theorem F₀_fst_fst : F₀ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = f ≫ eG f G := by
  simp only [F₀, rigSection, RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_fst_assoc, pullback.lift_fst,
    Category.assoc]
theorem F₀_fst_snd : F₀ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = f ≫ eG f G := by
  simp only [F₀, rigSection, RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_fst_assoc, pullback.lift_snd,
    Category.assoc]
theorem F₀_snd : F₀ f G ≫ pullback.snd _ _ = 𝟙 X := by
  simp only [F₀, rigSection, pullback.lift_snd]

def σ₁ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₁ f G) (by
    show F₁ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]; exact (G.one _).2)

def σ₂ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₂ f G) (by
    show F₂ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc])

def σ₃ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₃ f G) (by
    show F₃ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, Category.id_comp])

def σ₀ : Over.mk f ⟶ A3 f :=
  Over.homMk (F₀ f G) (by
    show F₀ f G ≫ pullback.fst (prodStr f f) f ≫ prodStr f f = f
    rw [F₀, rigSection, pullback.lift_fst_assoc, Category.assoc, ((G.prod G).one _).2, Category.comp_id])

theorem σ₁_p₁ : letI := G.grpObjOverMk; σ₁ f G ≫ p₁ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₁_fst_fst f G
theorem σ₁_p₂ : σ₁ f G ≫ p₂ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₁_fst_snd f G
theorem σ₁_p₃ : σ₁ f G ≫ p₃ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₁_snd f G
theorem σ₂_p₁ : σ₂ f G ≫ p₁ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₂_fst_fst f G
theorem σ₂_p₂ : letI := G.grpObjOverMk; σ₂ f G ≫ p₂ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₂_fst_snd f G
theorem σ₂_p₃ : σ₂ f G ≫ p₃ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₂_snd f G
theorem σ₃_p₁ : σ₃ f G ≫ p₁ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₃_fst_fst f G
theorem σ₃_p₂ : σ₃ f G ≫ p₂ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₃_fst_snd f G
theorem σ₃_p₃ : letI := G.grpObjOverMk; σ₃ f G ≫ p₃ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₃_snd f G
theorem σ₀_p₁ : letI := G.grpObjOverMk; σ₀ f G ≫ p₁ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left']; exact F₀_fst_fst f G
theorem σ₀_p₂ : letI := G.grpObjOverMk; σ₀ f G ≫ p₂ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left']; exact F₀_fst_snd f G
theorem σ₀_p₃ : σ₀ f G ≫ p₃ f = 𝟙 _ := by
  apply Over.OverMorphism.ext; exact F₀_snd f G

theorem pcls_σ₁ : letI := G.grpObjOverMk
    pcls (σ₁ f G).left (M₁ f 𝓛) = pcls (σ₁ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₁ f G) 1 (fst _ _) (snd _ _) (σ₁_p₁ f G) (σ₁_p₂ f G) (σ₁_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₁ f G) 1 (fst _ _) (snd _ _) (σ₁_p₁ f G) (σ₁_p₂ f G) (σ₁_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem pcls_σ₂ : letI := G.grpObjOverMk
    pcls (σ₂ f G).left (M₁ f 𝓛) = pcls (σ₂ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₂ f G) (fst _ _) 1 (snd _ _) (σ₂_p₁ f G) (σ₂_p₂ f G) (σ₂_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₂ f G) (fst _ _) 1 (snd _ _) (σ₂_p₁ f G) (σ₂_p₂ f G) (σ₂_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem pcls_σ₃ : letI := G.grpObjOverMk
    pcls (σ₃ f G).left (M₁ f 𝓛) = pcls (σ₃ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₃ f G) (fst _ _) (snd _ _) 1 (σ₃_p₁ f G) (σ₃_p₂ f G) (σ₃_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₃ f G) (fst _ _) (snd _ _) 1 (σ₃_p₁ f G) (σ₃_p₂ f G) (σ₃_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]

theorem pcls_σ₀ : letI := G.grpObjOverMk
    pcls (σ₀ f G).left (M₁ f 𝓛) = pcls (σ₀ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₀ f G) 1 1 (𝟙 _) (σ₀_p₁ f G) (σ₀_p₂ f G) (σ₀_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₀ f G) 1 1 (𝟙 _) (σ₀_p₁ f G) (σ₀_p₂ f G) (σ₀_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem locIsoOnBase_of_nonempty {S' : Type u} [CommRing S'] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of S'))
    {M M' : Z.Modules} (h : Nonempty (M ≅ M')) : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso h.some⟩⟩

def Nrig (hL : Scheme.Modules.IsInvertible 𝓛) :
    letI := G.grpObjOverMk
    RigidifiedLineBundle (prodStr f f) ((G.prod G).one (𝟙 (Spec (CommRingCat.of S)))) f := by
  letI := G.grpObjOverMk
  exact
    { L := N f 𝓛 (eG f G)
      isInvertible := isInvertible_N f 𝓛 (eG f G) hL
      rigidified := slice_trivial f 𝓛 (eG f G) hL (σ₀ f G) (pcls_σ₀ f G 𝓛) }


#print axioms Nrig
end WithLaw
end CubePBS
end
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeGeometry


noncomputable section
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian ArithmeticThetaLegendreAtlasR0176
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
local instance : CommGroup (curvePoint E) :=
  { E.law.pointGroup E.projection with mul_comm := E.commutative E.projection }

/-- Pullback of one global cube-line trivialization supplies the concrete cube
comparisons for every three actual E-valued points. -/
theorem actualCube_of_N_trivial
    (hN : letI := E.law.grpObjOverMk
      Nonempty (CubeGeometry.CubePBS.N E.projection (primitiveThetaLine E) (zero E) ≅ 𝟙_ _)) :
    ActualPrimitiveCube E := by
  letI := E.law.grpObjOverMk
  intro a b c
  let g : curvePoint E → (Over.mk E.projection ⟶ Over.mk E.projection) :=
    schemeHomOverToOverHom
  have hmul (x y : curvePoint E) : (g x * g y).left = (x * y).val := by
    exact congrArg Subtype.val (E.law.overHomToSchemeHomOver_mul E.projection (g x) (g y))
  have htriple : (g a * g b * g c).left = (a * b * c).val := by
    have h := E.law.overHomToSchemeHomOver_mul E.projection (g a * g b) (g c)
    have hab := E.law.overHomToSchemeHomOver_mul E.projection (g a) (g b)
    exact (congrArg Subtype.val h).trans
      (congrArg (fun x => (E.law.mul E.projection x c).val) hab)
  obtain ⟨e⟩ := CubeGeometry.CubePBS.main E.projection (primitiveThetaLine E) (zero E)
    (primitiveThetaLine_invertible E) hN (g a) (g b) (g c)
  have h := CategoryTheory.toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
  have hbase : toSkeleton ((Scheme.Modules.pullback E.projection).obj
      ((Scheme.Modules.pullback (zero E)).obj (primitiveThetaLine E))) =
      (1 : Skeleton E.curve.Modules) := by
    exact (toSkeleton_eq_toSkeleton_iff.mpr ⟨
      (Scheme.Modules.pullback E.projection).mapIso (primitiveRigidification E) ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso E.projection⟩).trans Skeleton.one_eq.symm
  simp only [Skeleton.toSkeleton_tensorObj] at h
  change toSkeleton _ * (toSkeleton _ * (toSkeleton _ * toSkeleton _)) =
    toSkeleton _ * (toSkeleton _ * (toSkeleton _ * toSkeleton _)) at h
  rw [htriple, hmul, hmul, hmul] at h
  change toSkeleton (pullbackPrimitive E (a * b * c)) *
      (toSkeleton (pullbackPrimitive E a) * (toSkeleton (pullbackPrimitive E b) *
      toSkeleton (pullbackPrimitive E c))) =
    toSkeleton (pullbackPrimitive E (a * b)) *
      (toSkeleton (pullbackPrimitive E (a * c)) * (toSkeleton (pullbackPrimitive E (b * c)) *
      toSkeleton ((Scheme.Modules.pullback E.projection).obj
        ((Scheme.Modules.pullback (zero E)).obj (primitiveThetaLine E))))) at h
  rw [hbase, mul_one] at h
  apply toSkeleton_eq_toSkeleton_iff.mp
  simpa only [Skeleton.toSkeleton_tensorObj, pullbackPrimitive, mul_assoc, mul_left_comm, mul_comm] using h

#print axioms actualCube_of_N_trivial
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255
end

noncomputable section
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ClopenIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Ws23G2


theorem eq_univ_of_isClopen_of_section {X S : Scheme.{u}} (g : X ⟶ S) (Z : Set X) (hZ : IsClopen Z)
    (hconn : ∀ s : S, _root_.IsPreconnected (g.base ⁻¹' {s}))
    (σ : S ⟶ X) (hσ : σ ≫ g = 𝟙 S) (hσZ : ∀ s : S, σ.base s ∈ Z) : Z = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hfib : (g.base ⁻¹' {g.base x}) ⊆ Z := by
    refine (hconn (g.base x)).subset_isClopen hZ ⟨σ.base (g.base x), ?_, hσZ _⟩
    show g.base (σ.base (g.base x)) = g.base x
    have := congrArg (fun φ => φ.base (g.base x)) hσ
    simpa using this
  exact hfib (Set.mem_preimage.2 rfl)

end Ws23G2

theorem solution
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (hconn : ∀ y : Y, _root_.IsConnected (p.base ⁻¹' {y}))
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hZ : ∃ e₀ : Y ⟶ Z, e₀ ≫ ι = e) :
    IsIso ι := by
  obtain ⟨e₀, he₀⟩ := hZ
  have hrange : Set.range ι.base = Set.univ := by
    refine Ws23G2.eq_univ_of_isClopen_of_section p (Set.range ι.base)
      ⟨ι.isClosedEmbedding.isClosed_range, ι.isOpenEmbedding.isOpen_range⟩
      (fun y => (hconn y).isPreconnected) e he (fun y => ?_)
    refine ⟨e₀.base y, ?_⟩
    have := congrArg (fun φ => φ.base y) he₀
    simpa using this
  haveI : Surjective ι := ⟨Set.range_eq_univ.1 hrange⟩
  exact (isIso_iff_isOpenImmersion_and_surjective ι).mpr ⟨inferInstance, inferInstance⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ClopenIso

namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ProductPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S R : Type u} [CommRing S] [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by
  have hg : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
  have s₁ : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ)) (pullback.fst (pullback.snd f σ) (pullback.snd f σ))
      (pullback.snd f σ) (pullback.snd f σ) := (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rw [hg.w]
    exact s₁.paste_horiz hg
  have s' : IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rwa [pullback.lift_snd]
  have step1 := IsPullback.of_right s' (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip
  exact step1.paste_vert hg
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ProductPullback

namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.SmallExtension

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

namespace Ws23RC


noncomputable def pullbackComp₃ {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback c).obj M)) ≅
      (Scheme.Modules.pullback (a ≫ b ≫ c)).obj M :=
  (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b c).app M) ≪≫ (Scheme.Modules.pullbackComp a (b ≫ c)).app M

noncomputable def pullbackInvHomIso {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M

theorem one_coe_congr {S : Type u} [CommRing S] {A Z : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {b₁ b₂ : Z ⟶ Spec (CommRingCat.of S)} (hb : b₁ = b₂) : (L.one b₁).1 = (L.one b₂).1 := by
  subst hb; rfl

theorem comp_one_coe {S : Type u} [CommRing S] {A Z Z' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (t : Z ⟶ Spec (CommRingCat.of S)) (ψ : Z' ⟶ Z) : ψ ≫ (L.one t).1 = (L.one (ψ ≫ t)).1 := by
  have := congrArg Subtype.val (L.one_natural t (ψ ≫ t) ψ rfl)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

end Ws23RC

theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [CommRing T] [Nontrivial T]
    (p : T' →+* T) (hp : Function.Surjective p) (hsmall : RingHom.ker p * IsLocalRing.maximalIdeal T' = ⊥)
    (s : Spec (CommRingCat.of T') ⟶ A)
    (hs : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom p) ≫ s, rfl⟩ : SchemeHomOver ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) f)).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) _).L)) :
    Nonempty ((M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) _).L) := by
  classical
  obtain ⟨iT⟩ := hs
  letI : Algebra T' T := p.toAlgebra

  let σ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S) := s ≫ f
  let f₁ := pullback.snd f σ
  let g₁ := pullback.fst f σ
  let L₁ : RelativeGroupLaw T' f₁ := L.baseChange σ
  have hA₁ : AbelianSchemePropertyBundle T' f₁ := hA.of_isPullback (IsPullback.of_hasPullback f σ)

  let π : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T') := Spec.map (CommRingCat.ofHom (algebraMap T' T))
  let f₀ := pullback.snd f₁ π
  let g := pullback.fst f₁ π
  have hg : IsPullback g f₀ f₁ (Spec.map (CommRingCat.ofHom (algebraMap T' T))) := IsPullback.of_hasPullback f₁ π
  let L₀ : RelativeGroupLaw T (pullback.snd f₁ π) := L₁.baseChange π

  have hβ := ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ProductPullback.solution f σ
  let e : pullback f₁ f₁ ≅ pullback (prodStr f f) σ := hβ.isoPullback
  have he₁ : e.hom ≫ pullback.fst _ _ = pullback.lift (pullback.fst f₁ f₁ ≫ g₁) (pullback.snd f₁ f₁ ≫ g₁)
      (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) := hβ.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd _ _ = pullback.fst f₁ f₁ ≫ f₁ := hβ.isoPullback_hom_snd

  let N := (M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).L
  let M₈ : (pullback f₁ f₁).Modules := (Scheme.Modules.pullback e.hom).obj N
  have hM₈ : Scheme.Modules.IsInvertible M₈ := (M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).isInvertible.pullback _

  have hkm : RingHom.ker (algebraMap T' T) ≤ IsLocalRing.maximalIdeal T' :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap T' T))
  have hKm : IsLocalRing.maximalIdeal T' * RingHom.ker (algebraMap T' T) = ⊥ := by
    rw [mul_comm]; exact hsmall
  have hK : RingHom.ker (algebraMap T' T) * RingHom.ker (algebraMap T' T) = ⊥ :=
    le_bot_iff.1 ((Ideal.mul_mono_left hkm).trans (le_of_eq hKm))

  have h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M₈ ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj (𝟙_ _)) := by
    have hc₁ : g₁ ≫ f = f₁ ≫ σ := pullback.condition
    have hc₀ : g ≫ f₁ = f₀ ≫ π := pullback.condition
    have hc₀₀ : pullback.fst f₀ f₀ ≫ f₀ = pullback.snd f₀ f₀ ≫ f₀ := pullback.condition
    have hπ : π = Spec.map (CommRingCat.ofHom p) := rfl
    have he₁₁ : e.hom ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₁ f₁ ≫ g₁ := by
      rw [← Category.assoc, he₁, pullback.lift_fst]
    have he₁₂ : e.hom ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₁ f₁ ≫ g₁ := by
      rw [← Category.assoc, he₁, pullback.lift_snd]
    let gg : pullback f₀ f₀ ⟶ pullback f₁ f₁ := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
      (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc])
    have hgg₁ : gg ≫ pullback.fst f₁ f₁ = pullback.fst f₀ f₀ ≫ g := pullback.lift_fst _ _ _
    have hgg₂ : gg ≫ pullback.snd f₁ f₁ = pullback.snd f₀ f₀ ≫ g := pullback.lift_snd _ _ _
    let ψ₀ : SchemeHomOver ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) f := ⟨Spec.map (CommRingCat.ofHom p) ≫ s, rfl⟩
    let κ : pullback f₀ f₀ ⟶ pullback (prodStr f f) ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) :=
      pullback.lift
        (pullback.lift (pullback.fst f₀ f₀ ≫ g ≫ g₁) (pullback.snd f₀ f₀ ≫ g ≫ g₁)
          (by rw [Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀, Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀,
            reassoc_of% hc₀₀]))
        (pullback.fst f₀ f₀ ≫ f₀)
        (by
          show _ ≫ (pullback.fst f f ≫ f) = _
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀]
          simp only [Category.assoc]
          rfl)
    have hκa : κ ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g ≫ g₁ := by
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    have hκb : κ ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g ≫ g₁ := by
      rw [pullback.lift_fst_assoc, pullback.lift_snd]
    have hκc : κ ≫ pullback.snd _ _ = pullback.fst f₀ f₀ ≫ f₀ := pullback.lift_snd _ _ _
    have hb1 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.fst _ _ = pullback.fst _ _ := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have hb2 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ s := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
    have hb1' : baseChangeSnd (prodStr f f) ψ₀ ≫ pullback.fst _ _ = pullback.fst _ _ := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have hb2' : baseChangeSnd (prodStr f f) ψ₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (Spec.map (CommRingCat.ofHom p) ≫ s) := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
      rfl
    have hκ : gg ≫ e.hom ≫ baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) =
        κ ≫ baseChangeSnd (prodStr f f) ψ₀ := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [reassoc_of% hb1, he₁₁, reassoc_of% hgg₁, reassoc_of% hb1', hκa]
        · simp only [Category.assoc]
          rw [reassoc_of% hb1, he₁₂, reassoc_of% hgg₂, reassoc_of% hb1', hκb]
      · simp only [Category.assoc]
        rw [hb2, reassoc_of% he₂, reassoc_of% hgg₁, reassoc_of% hc₀, hb2', reassoc_of% hκc]
        exact congrArg (fun t => pullback.fst f₀ f₀ ≫ f₀ ≫ t ≫ s) hπ
    refine ⟨Ws23RC.pullbackComp₃ _ _ _ M.L ≪≫ (Scheme.Modules.pullbackCongr hκ).app M.L ≪≫
      ((Scheme.Modules.pullbackComp κ _).app M.L).symm ≪≫ (Scheme.Modules.pullback κ).mapIso iT ≪≫
      Scheme.Modules.pullbackUnitIso κ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm⟩

  let θ : pullback f₁ (𝟙 (Spec (CommRingCat.of T'))) ⟶ pullback f f :=
    pullback.lift (pullback.fst f₁ (𝟙 _) ≫ g₁) (pullback.fst f₁ (𝟙 _) ≫ f₁ ≫ s)
      (by rw [Category.assoc, pullback.condition, Category.assoc, Category.assoc])
  have hθc : θ ≫ prodStr f f = pullback.snd f₁ (𝟙 _) ≫ σ := by
    show θ ≫ (pullback.fst f f ≫ f) = _
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, Category.id_comp]
  have he₁₁ : e.hom ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₁ f₁ ≫ g₁ := by
    rw [← Category.assoc, he₁, pullback.lift_fst]
  have he₁₂ : e.hom ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₁ f₁ ≫ g₁ := by
    rw [← Category.assoc, he₁, pullback.lift_snd]
  have hone₁ : (L₁.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ g₁ = (L.one (𝟙 _ ≫ σ)).1 :=
    congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one σ L (𝟙 _))
  have hone₁f : (L₁.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ f₁ = 𝟙 _ := (L₁.one (𝟙 _)).2

  let face₂ : pullback f f ⟶ pullback (prodStr f f) f :=
    pullback.lift (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
      (pullback.snd f f) (by rw [pullback.lift_fst_assoc]; exact pullback.condition)
  let face₁ : pullback f f ⟶ pullback (prodStr f f) f :=
    pullback.lift (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
      (pullback.snd f f) (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition)
  have hF2a : face₂ ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hF2b : face₂ ≫ pullback.fst _ _ ≫ pullback.snd f f = (L.one (prodStr f f)).1 := by
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hF2c : face₂ ≫ pullback.snd _ _ = pullback.snd f f := pullback.lift_snd _ _ _
  have hF1a : face₁ ≫ pullback.fst _ _ ≫ pullback.fst f f = (L.one (prodStr f f)).1 := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hF1b : face₁ ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.fst f f := by
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hF1c : face₁ ≫ pullback.snd _ _ = pullback.snd f f := pullback.lift_snd _ _ _
  have hθa : θ ≫ pullback.fst f f = pullback.fst f₁ (𝟙 _) ≫ g₁ := pullback.lift_fst _ _ _
  have hθb : θ ≫ pullback.snd f f = pullback.fst f₁ (𝟙 _) ≫ f₁ ≫ s := pullback.lift_snd _ _ _
  have hsla : sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))) ≫ pullback.fst f₁ f₁ = pullback.fst f₁ (𝟙 _) := by
    rw [sliceAt, pullback.lift_fst]
  have hslb : sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))) ≫ pullback.snd f₁ f₁ =
      pullback.snd f₁ (𝟙 _) ≫ (L₁.one (𝟙 _)).1 := by
    rw [sliceAt, pullback.lift_snd]
  have hbcs1 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hbcs2 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ s := by
    simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
  have hpb₁ : pullback.fst f₁ (𝟙 (Spec (CommRingCat.of T'))) ≫ f₁ = pullback.snd f₁ (𝟙 _) := by
    rw [pullback.condition, Category.comp_id]

  have hone : pullback.snd f₁ (𝟙 (Spec (CommRingCat.of T'))) ≫ (L₁.one (𝟙 _)).1 ≫ g₁ = θ ≫ (L.one (prodStr f f)).1 := by
    rw [hone₁, Ws23RC.comp_one_coe, Ws23RC.comp_one_coe]
    exact Ws23RC.one_coe_congr L (by rw [Category.id_comp, hθc])
  have hθ₁ : sliceAt f₁ (L₁.one (𝟙 _)) ≫ e.hom ≫ baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) =
      θ ≫ face₂ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₁, ← Category.assoc, hsla, hF2a, hθa]
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₂, ← Category.assoc, hslb, Category.assoc, hone, hF2b]
    · simp only [Category.assoc]
      rw [hbcs2, reassoc_of% he₂, ← Category.assoc, hsla, hF2c, hθb]
  have hθ₂ : sliceAt f₁ (L₁.one (𝟙 _)) ≫ (pullbackSymmetry f₁ f₁).hom ≫ e.hom ≫
        baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) = θ ≫ face₁ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₁, pullbackSymmetry_hom_comp_fst_assoc, ← Category.assoc, hslb, Category.assoc, hone, hF1a]
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₂, pullbackSymmetry_hom_comp_snd_assoc, ← Category.assoc, hsla, hF1b, hθa]
    · simp only [Category.assoc]
      rw [hbcs2, reassoc_of% he₂, pullbackSymmetry_hom_comp_fst_assoc, ← Category.assoc, hslb, Category.assoc,
        reassoc_of% hone₁f, hF1c, hθb, reassoc_of% hpb₁]

  have glob : ∀ (F : pullback f f ⟶ pullback (prodStr f f) f),
      LocIsoOnBase (prodStr f f) ((Scheme.Modules.pullback F).obj M.L) (𝟙_ _) →
      Nonempty ((Scheme.Modules.pullback (θ ≫ F)).obj M.L ≅ 𝟙_ _) := by
    intro F hF
    have hloc := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f₁ (𝟙 (Spec (CommRingCat.of T')))) θ σ hθc hF
    obtain ⟨i⟩ := (locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).1 hloc
    exact ⟨((Scheme.Modules.pullbackComp θ F).app M.L).symm ≪≫ i ≪≫ Scheme.Modules.pullbackUnitIso θ⟩
  have h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj M₈ ≅ 𝟙_ _) := by
    obtain ⟨i⟩ := glob face₂ h₂
    exact ⟨Ws23RC.pullbackComp₃ _ _ _ M.L ≪≫ (Scheme.Modules.pullbackCongr hθ₁).app M.L ≪≫ i⟩
  have h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f₁ f₁).hom).obj M₈) ≅ 𝟙_ _) := by
    obtain ⟨i⟩ := glob face₁ h₁
    exact ⟨(Scheme.Modules.pullback _).mapIso (Ws23RC.pullbackComp₃ _ _ _ M.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hθ₂).app M.L ≪≫ i⟩
  have h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      (𝟙_ (pullback f₁ f₁).Modules) ≅ 𝟙_ _) := ⟨Scheme.Modules.pullbackUnitIso _⟩
  have h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f₁ f₁).hom).obj (𝟙_ (pullback f₁ f₁).Modules)) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _) ≪≫ Scheme.Modules.pullbackUnitIso _⟩

  obtain ⟨i₈⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
    hp hK hKm L₁ hA₁ L₀ g hg
    (fun t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul π L₁ t' P Q))
    M₈ (𝟙_ _) hM₈ (Scheme.Modules.isInvertible_unit _) h0 h1 h2 h1' h2'

  exact ⟨(Ws23RC.pullbackInvHomIso e N).symm ≪≫ (Scheme.Modules.pullback e.inv).mapIso i₈ ≪≫ Scheme.Modules.pullbackUnitIso e.inv⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.SmallExtension

namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.CubeTrivial

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

open IsLocalRing

theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f).L) := by
  classical
  haveI : Smooth f := hA.smooth

  obtain ⟨Z, ι, hcl, hZ⟩ := ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.rigidified_closed_locus (L.prod L) (GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing hA hA) f M
  haveI := hcl
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : LocallyOfFinitePresentation ι := inferInstance

  have hopen : IsOpenImmersion ι := by
    refine AlgebraicGeometry.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian ι (fun T' T _ _ _ _ _ p hp hsmall s m hm => ?_)
    have hT : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom p) ≫ s, rfl⟩ : SchemeHomOver ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) f)).L ≅
          (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) _).L) :=
      (hZ _ _).mpr ⟨m, hm⟩
    obtain ⟨m', hm'⟩ := (hZ _ _).mp (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.SmallExtension.solution L hA M h₁ h₂ T' T p hp hsmall s hT)
    refine ⟨m', hm', ?_⟩
    rw [← cancel_mono ι, Category.assoc, hm', hm]
  haveI := hopen

  have hiso : IsIso ι :=
    ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.ClopenIso.solution f hA.connectedFibres (L.one (𝟙 _)).1 (L.one (𝟙 _)).2 ι ((hZ _ (L.one (𝟙 _))).mp (ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.cube_identity_face L hA M h₃))

  obtain ⟨eI⟩ := (hZ f ⟨𝟙 A, Category.id_comp f⟩).mpr ⟨inv ι, IsIso.inv_hom_id ι⟩
  exact ⟨((Scheme.Modules.pullbackCongr (baseChangeSnd_id (prodStr f f) f)).app M.L ≪≫
      (Scheme.Modules.pullbackId _).app M.L).symm ≪≫ eI⟩
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255.CubeCompletion.CubeTrivial

end

noncomputable section
namespace ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra ArithmeticThetaLegendreAtlasR0176
open CubeGeometry.CubePBS
set_option backward.isDefEq.respectTransparency false

theorem actualPrimitiveCube {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : EllipticFamily R) : ActualPrimitiveCube E := by
  letI := E.law.grpObjOverMk
  apply actualCube_of_N_trivial E
  exact CubeCompletion.CubeTrivial.solution E.law
    (ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180.geometry E)
    (Nrig E.projection E.law (primitiveThetaLine E) (primitiveThetaLine_invertible E))
    (locIsoOnBase_of_nonempty _ (slice_trivial E.projection (primitiveThetaLine E)
      (eG E.projection E.law) (primitiveThetaLine_invertible E)
      (σ₁ E.projection E.law) (pcls_σ₁ E.projection E.law (primitiveThetaLine E))))
    (locIsoOnBase_of_nonempty _ (slice_trivial E.projection (primitiveThetaLine E)
      (eG E.projection E.law) (primitiveThetaLine_invertible E)
      (σ₂ E.projection E.law) (pcls_σ₂ E.projection E.law (primitiveThetaLine E))))
    (locIsoOnBase_of_nonempty _ (slice_trivial E.projection (primitiveThetaLine E)
      (eG E.projection E.law) (primitiveThetaLine_invertible E)
      (σ₃ E.projection E.law) (pcls_σ₃ E.projection E.law (primitiveThetaLine E))))

#print axioms actualPrimitiveCube
end ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255

namespace ArithmeticThetaRelativeThetaLiftsR0255
/-- The global doubled-torsion theta lift over the full relative elliptic family. -/
theorem relative_doubled_torsion_theta_lift :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R),
    ∀ m : ℕ, 0 < m → Even m →
    ∀ (P : ArithmeticThetaRelativeThetaLiftsR0255.point E),
      CategoryTheory.CategoryStruct.comp P.val (E.law.schemeNsmul (2*m)) =
        ArithmeticThetaRelativeThetaLiftsR0255.zero E →
      Nonempty (ArithmeticThetaRelativeThetaLiftsR0255.Lift E m
        (ArithmeticThetaRelativeThetaLiftsR0255.translation E P)) := by
  intro R _ _ _ E m hm _ P hP
  exact RelativeDoubledTorsionThetaLiftR0255.lift_of_actualPrimitiveCube E
    (RelativeDoubledTorsionThetaLiftR0255.actualPrimitiveCube E) m hm P hP
#print axioms relative_doubled_torsion_theta_lift
end ArithmeticThetaRelativeThetaLiftsR0255
end
