module

public import SectionOrderInvariance
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
universe u v w
noncomputable section
namespace ArithmeticThetaDegreeAssembly

/-- Evaluate a genuine sheaf isomorphism as a linear equivalence on each open. -/
def lineIsoSectionsLinearEquiv {X : Scheme.{u}} {H J : X.Modules} (e : H ≅ J) (U : X.Opens) :
    Γ(H,U) ≃ₗ[Γ(X,U)] Γ(J,U) := by
  let f : Γ(H,U) →ₗ[Γ(X,U)] Γ(J,U) :=
    { toFun := e.hom.app U, map_add' := map_add _, map_smul' := by intro r x; exact Scheme.Modules.Hom.app_smul e.hom r x }
  let g : Γ(J,U) →ₗ[Γ(X,U)] Γ(H,U) :=
    { toFun := e.inv.app U, map_add' := map_add _, map_smul' := by intro r x; exact Scheme.Modules.Hom.app_smul e.inv r x }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    have hh := congrArg (fun q => q.app U) e.hom_inv_id
    have hh' := ConcreteCategory.congr_hom hh
    have hleft : g (f x) = x := by
      convert hh' x using 1 <;> rfl
    have hleft' : g (f y) = y := by
      convert hh' y using 1 <;> rfl
    rw [← hleft, ← hleft', hxy]
  · intro y
    refine ⟨g y, ?_⟩
    have hh := congrArg (fun q => q.app U) e.inv_hom_id
    have hh' := ConcreteCategory.congr_hom hh
    convert hh' y using 1 <;> rfl

/-- Transport a target frame through the actual inverse sheaf isomorphism. -/
def inverseImageFrame {X : Scheme.{u}} {H J : X.Modules} (e : H ≅ J)
    {U : X.Opens} (F : LocalFrame X J U) : LocalFrame X H U where
  equiv V hVU := F.equiv V hVU |>.trans (lineIsoSectionsLinearEquiv e V).symm
  naturality V W hWV hVU a := by
    apply (lineIsoSectionsLinearEquiv e W).injective
    simp only [LinearEquiv.trans_apply]
    have hn := PresheafOfModules.naturality_apply e.hom.val (homOfLE hWV).op
      ((lineIsoSectionsLinearEquiv e V).symm (F.equiv V hVU a))
    change (e.hom.val.app (op W)) ((H.val.map (homOfLE hWV).op)
      ((lineIsoSectionsLinearEquiv e V).symm (F.equiv V hVU a))) = _
    rw [hn]
    have he := (lineIsoSectionsLinearEquiv e V).apply_symm_apply (F.equiv V hVU a)
    change (e.hom.val.app (op V)) ((lineIsoSectionsLinearEquiv e V).symm (F.equiv V hVU a)) = _ at he
    rw [he]
    rw [(lineIsoSectionsLinearEquiv e W).apply_symm_apply]
    exact F.naturality V W hWV hVU a

open ArithmeticThetaSectionOrder
/-- Naturality identifies inverse-image frame coordinates with image coordinates. -/
lemma sectionCoordinate_inverseImageFrame {X : Scheme.{u}} {H J : X.Modules} (e : H ≅ J)
    {U : X.Opens} (F : LocalFrame X J U) (s : Γ(H, ⊤)) :
    sectionCoordinate X H U (inverseImageFrame e F) s =
      sectionCoordinate X J U F (e.hom.app ⊤ s) := by
  unfold sectionCoordinate inverseImageFrame
  have hn := PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (le_top : U ≤ ⊤)).op s
  dsimp [inverseImageFrame]
  apply congrArg (F.equiv U le_rfl).symm
  exact hn


/-- The source cover together with the target frames transported through the inverse map. -/
def isomorphismComparisonCover (X : Scheme.{u}) [IsIntegral X] (H J : X.Modules)
    {ι : Type v} {κ : Type w} (C : NormalFrameCover X H ι)
    (E : NormalFrameCover X J κ) (e : H ≅ J) : NormalFrameCover X H (ι ⊕ κ) where
  opens := Sum.elim C.opens E.opens
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.covers hx)
    exact Opens.mem_iSup.mpr ⟨Sum.inl i, hi⟩
  nonempty := by intro a; cases a with | inl i => exact C.nonempty i | inr j => exact E.nonempty j
  affine := by intro a; cases a with | inl i => exact C.affine i | inr j => exact E.affine j
  normal := by intro a; cases a with | inl i => exact C.normal i | inr j => exact E.normal j
  frame := by intro a; cases a with | inl i => exact C.frame i | inr j => exact inverseImageFrame e (E.frame j)

/-- A genuine globally invertible line map preserves every local order and the section divisor. -/
theorem line_isomorphism_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H J : X.Modules) (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    (ι : Type v) (κ : Type w) (C : NormalFrameCover X H ι)
    (E : NormalFrameCover X J κ) (e : H ≅ J) (s : Γ(H, ⊤)) (D : X →₀ ℤ) :
    s ≠ 0 → MatchesSectionOrder X H C s D →
      e.hom.app ⊤ s ≠ 0 ∧ MatchesSectionOrder X J E (e.hom.app ⊤ s) D := by
  intro hs hD
  constructor
  · intro hz
    exact hs ((lineIsoSectionsLinearEquiv e ⊤).map_eq_zero_iff.mp hz)
  · intro j x hxj
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers (show x ∈ (⊤ : X.Opens) by trivial))
    rw [hD i x hxi]
    have h := local_order_frame_invariant X H (ι ⊕ κ) (isomorphismComparisonCover X H J C E e)
      s (Sum.inl i) (Sum.inr j) x hxi hxj
    change localOrder X H C s i x = Scheme.ord
      (sectionCoefficient X H (E.opens j) (inverseImageFrame e (E.frame j)) s) x at h
    simpa only [localOrder, sectionCoefficient, sectionCoordinate_inverseImageFrame] using h

end ArithmeticThetaDegreeAssembly

#print axioms ArithmeticThetaDegreeAssembly.line_isomorphism_divisor
