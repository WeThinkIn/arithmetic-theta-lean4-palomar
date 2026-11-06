import FormalOpenRestrictionsR0210

open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverR0210
namespace FormalCoverAlgebraization

variable (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))

abbrev res (n : ℕ) (U : X.Opens) : Γ(stage k X f n, ⊤) →+* StageSections k X f U n :=
  ((stage k X f n).presheaf.map (homOfLE le_top).op).hom

lemma stage_cover (C : Cover k X f) (n : ℕ) :
    (⊤ : (stage k X f n).Opens) ≤ ⨆ i, inclusion k X f n ⁻¹ᵁ C.opens i := by
  intro x _
  have hx : (inclusion k X f n) x ∈ (ideal k X f ^ n).support := by
    change (inclusion k X f n) x ∈ ((ideal k X f ^ n).support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  cases n with
  | zero => exact False.elim hx
  | succ n =>
    have hx' : (inclusion k X f (n+1)) x ∈
        Set.range (inclusion k X f 1) := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    obtain ⟨i, hi⟩ := C.covers y
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨i, by change (inclusion k X f (n+1)) x ∈ C.opens i; rw [← hy]; exact hi⟩

lemma stage_ext (C : Cover k X f) (n : ℕ) (a b : Γ(stage k X f n, ⊤))
    (h : ∀ i, res k X f n (C.opens i) a = res k X f n (C.opens i) b) : a = b :=
  (stage k X f n).sheaf.eq_of_locally_eq'
    (fun i => inclusion k X f n ⁻¹ᵁ C.opens i) ⊤ (fun _ => homOfLE le_top)
    (stage_cover k X f C n) a b h

lemma stage_glue (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, FormalRing k X f (C.opens i)) (hz : Compatible k X f ρ C z) (n : ℕ) :
    ∃! s : Γ(stage k X f n, ⊤), ∀ i, res k X f n (C.opens i) s = (z i).val n := by
  apply (stage k X f n).sheaf.existsUnique_gluing'
    (fun i => inclusion k X f n ⁻¹ᵁ C.opens i) ⊤ (fun _ => homOfLE le_top)
    (stage_cover k X f C n)
  intro i j
  have h := congrArg (fun a : FormalRing k X f (C.opens i ⊓ C.opens j) => a.val n) (hz i j)
  rw [ρ.component, ρ.component] at h
  exact h

lemma transition_res (U : X.Opens) (m n : ℕ) (h : ideal k X f ^ n ≤ ideal k X f ^ m)
    (a : Γ(stage k X f n, ⊤)) :
    transition k X f U m n h (res k X f n U a) =
      res k X f m U ((Scheme.IdealSheafData.inclusion h).appTop a) := by
  change (((stage k X f n).presheaf.map _ ≫
    (Scheme.IdealSheafData.inclusion h).appLE _ _ _) a) =
    (((Scheme.IdealSheafData.inclusion h).appTop ≫
      (stage k X f m).presheaf.map _) a)
  simp only [Scheme.Hom.appTop]
  rw [Scheme.Hom.app_eq_appLE (Scheme.IdealSheafData.inclusion h)]
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

lemma global_component (U : X.Opens) (a : Γ(X, ⊤)) (n : ℕ) :
    (globalRestriction k X f U a).val n =
      res k X f n U ((inclusion k X f n).appTop a) :=
  ArithmeticThetaGeometricPrerequisites.FormalBridge.app_resTop (inclusion k X f n) U a

end FormalCoverAlgebraization

open FormalCoverAlgebraization in
/-- Compatible actual formal sections over an arbitrary closed-fiber cover
algebraize uniquely on the proper model. -/
theorem formal_cover_algebraization (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) [IsProper f]
    (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, FormalRing k X f (C.opens i)) (hz : Compatible k X f ρ C z) :
    ∃! a : X.presheaf.obj (op ⊤), ∀ i, globalRestriction k X f (C.opens i) a = z i := by
  choose s hs using fun n => (stage_glue k X f ρ C z hz n).exists
  have hcompat : ArithmeticThetaGeometricPrerequisites.CompatibleFormalFunctions X
      (ideal k X f) s := by
    intro m n h
    apply stage_ext k X f C m
    intro i
    rw [← transition_res, hs, hs]
    exact (z i).property m n h
  obtain ⟨a, ha, huniq⟩ := ArithmeticThetaGeometricPrerequisites.proper_formal_functions_h0
    (PowerSeries k) PowerSeries.X X f s hcompat
  refine ⟨a, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext n
    rw [global_component, ha, hs]
  · intro b hb
    apply huniq b
    intro n
    apply stage_ext k X f C n
    intro i
    rw [← global_component, hb, hs]

end ArithmeticThetaFormalCoverR0210

#print axioms ArithmeticThetaFormalCoverR0210.formal_cover_algebraization
