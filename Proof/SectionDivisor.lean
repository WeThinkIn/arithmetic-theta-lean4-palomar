module

public import SectionOrderInvariance
public import PrincipalDivisor
public import FinitePrincipalSupport

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaCurveDegree

universe u v
noncomputable section

namespace ArithmeticThetaSectionOrder

private lemma finite_normal_frame_subcover
    (X : Scheme.{u}) (H : X.Modules) (ι : Type v) (C : NormalFrameCover X H ι)
    [CompactSpace X] : ∃ t : Finset ι, (Set.univ : Set X) ⊆ ⋃ i ∈ t, (C.opens i : Set X) := by
  have hcover : (Set.univ : Set X) ⊆ ⋃ i, (C.opens i : Set X) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨Classical.choose (Opens.mem_iSup.mp (C.covers (by trivial))),
      (Classical.choose_spec (Opens.mem_iSup.mp (C.covers (by trivial))))⟩
  exact isCompact_univ.elim_finite_subcover (fun i : ι => (C.opens i : Set X))
    (fun i => (C.opens i).isOpen) hcover

set_option maxRecDepth 100000 in
theorem exists_section_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (H : X.Modules) (ι : Type v)
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (hs : s ≠ 0) :
    ∃ D : X →₀ ℤ, MatchesSectionOrder X H C s D := by
  classical
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  obtain ⟨t, ht⟩ := finite_normal_frame_subcover X H ι C
  have hfinite (i : ι) (hi : i ∈ t) :
      Set.Finite {x : X | Scheme.ord (sectionCoefficient X H (C.opens i)
        (C.frame i) s) x ≠ 0} := by
    by_cases hz : sectionCoefficient X H (C.opens i) (C.frame i) s = 0
    · simp [hz]
    · exact finite_principal_support X k f hcurve _ hz
  let S : Set X := ⋃ i ∈ t, {x : X | Scheme.ord (sectionCoefficient X H (C.opens i)
      (C.frame i) s) x ≠ 0}
  have hS : S.Finite := by
    apply Set.Finite.biUnion t.finite_toSet
    intro i hi
    apply hfinite i hi
  let iOf : ∀ x : X, ι := fun x => Classical.choose (Opens.mem_iSup.mp
    (C.covers (show x ∈ (⊤ : X.Opens) by trivial)))
  have hiOf (x : X) : x ∈ C.opens (iOf x) :=
    (Classical.choose_spec (Opens.mem_iSup.mp
      (C.covers (show x ∈ (⊤ : X.Opens) by trivial))))
  have hzero (x : X) (hx : x ∉ S) : localOrder X H C s (iOf x) x = 0 := by
    have hxcover : x ∈ ⋃ i ∈ t, (C.opens i : Set X) := ht (by trivial)
    obtain ⟨i, hxcover⟩ := Set.mem_iUnion.1 hxcover
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.1 hxcover
    have hnot : Scheme.ord (sectionCoefficient X H (C.opens i)
        (C.frame i) s) x = 0 := by
      by_contra hne
      exact hx (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hne⟩⟩)
    rw [local_order_frame_invariant X H ι C s (iOf x) i x (hiOf x) hxi]
    exact hnot
  let D : X →₀ ℤ := Finsupp.onFinset hS.toFinset
    (fun x => localOrder X H C s (iOf x) x)
    (by
      intro x hx
      by_contra hxm
      have hxs : x ∉ S := by
        intro hxs
        exact hxm (hS.mem_toFinset.mpr hxs)
      exact hx (hzero x hxs))
  refine ⟨D, ?_⟩
  intro i x hxi
  simp only [D, Finsupp.onFinset_apply]
  exact local_order_frame_invariant X H ι C s (iOf x) i x (hiOf x) hxi

theorem section_divisor_support_coheight_one
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (ι : Type v) (C : NormalFrameCover X H ι)
    (s : Γ(H, ⊤)) (D : X →₀ ℤ) (hD : MatchesSectionOrder X H C s D) :
    ∀ x ∈ D.support, Order.coheight x = 1 := by
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers (show x ∈ (⊤ : X.Opens) by trivial))
  have hdx : D x = localOrder X H C s i x := hD i x hxi
  by_contra hco
  have hz : localOrder X H C s i x = 0 := by
    unfold localOrder
    exact Scheme.ord_eq_zero_of_coheight_neq_one hco _
  exact (Finsupp.mem_support_iff.mp hx) (hdx.trans hz)

end ArithmeticThetaSectionOrder

#print axioms ArithmeticThetaSectionOrder.exists_section_divisor
#print axioms ArithmeticThetaSectionOrder.section_divisor_support_coheight_one
