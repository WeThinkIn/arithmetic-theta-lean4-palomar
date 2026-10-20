module

public import LevelCompactificationDefinitionsR0179
public import ResidueDegrees
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
public import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLevelCompactificationR0179
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace BoundaryGeometry

theorem boundary_isClosed (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) : IsClosed (boundary k L D X) := by
  letI := X.openImmersion
  exact X.inclusion.isOpenEmbedding.isOpen_range.isClosed_compl

theorem finiteResidue_of_closed (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : IsClosed ({x} : Set X.space)) :
    FiniteResidue k L D X x := by
  letI := X.proper
  exact ArithmeticThetaCurveDegree.baseToResidue_finite_of_closed X.space k X.projection x hx

/-- Dimension one and density force every irreducible closed subset of the
complement to be minimal, without requiring the ambient scheme to be integral. -/
theorem boundary_irreducible_min (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (C : IrreducibleCloseds X.space)
    (hC : (C : Set X.space) ⊆ boundary k L D X) : IsMin C := by
  letI := X.proper
  letI := X.smooth
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  haveI : CompactSpace X.space := QuasiCompact.compactSpace_of_compactSpace X.projection
  haveI : IsNoetherian X.space := {}
  rcases Order.krullDim_le_one_iff.mp
    (SmoothOfRelativeDimension.topologicalKrullDim_le X.projection 1) C with hm | hm
  · exact hm
  · exfalso
    have hc : (C : Set X.space) ∈ irreducibleComponents X.space := by
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨C.isClosed, C.isIrreducible⟩, ?_⟩
      intro S hS hCS
      exact hm (b := ⟨S, hS.2, hS.1⟩) hCS
    obtain ⟨U, hU, hUne, hUC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
    obtain ⟨x, hxU, hxrange⟩ := X.dense.inter_open_nonempty U hU hUne
    exact hC (hUC hxU) hxrange

theorem boundary_point_closed (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X) :
    IsClosed ({x} : Set X.space) := by
  let C : IrreducibleCloseds X.space :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hm : IsMin C := boundary_irreducible_min k L D X C
    ((boundary_isClosed k L D X).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx))
  apply isClosed_of_closure_subset
  intro y hy
  let E : IrreducibleCloseds X.space :=
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hEC : E ≤ C := isClosed_closure.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr hy)
  have heq : closure ({x} : Set X.space) = closure {y} := SetLike.ext'_iff.mp
    (le_antisymm (hm hEC) hEC : C = E)
  exact Set.mem_singleton_iff.mpr ((isGenericPoint_closure (x := x)).eq (show IsGenericPoint y (closure {x}) by rw [heq]; exact isGenericPoint_closure)).symm

theorem boundary_finite (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) : (boundary k L D X).Finite := by
  letI := X.proper
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  haveI : CompactSpace X.space := QuasiCompact.compactSpace_of_compactSpace X.projection
  haveI : IsNoetherian X.space := {}
  obtain ⟨S, hSf, hSc, hSi, heq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (boundary_isClosed k L D X)
  rw [heq]
  apply hSf.sUnion
  intro C hC
  obtain ⟨x, hx⟩ := (hSi C hC).nonempty
  have hCB : C ⊆ boundary k L D X := by
    rw [heq]
    exact Set.subset_sUnion_of_mem hC
  have hm := boundary_irreducible_min k L D X ⟨C, (hSi C hC), (hSc C hC)⟩ hCB
  let E : IrreducibleCloseds X.space :=
    ⟨{x}, isIrreducible_singleton, boundary_point_closed k L D X x (hCB hx)⟩
  exact (Set.finite_singleton x).subset (hm (b := E) (Set.singleton_subset_iff.mpr hx))

/-- The standard smooth local chart proves the DVR assertion on each connected
component; no integral structure on the whole compactification is selected. -/
theorem dvr_of_closed {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
    (x : Y) (hx : IsClosed ({x} : Set Y)) :
    ∃ hdom : IsDomain (Y.presheaf.stalk x),
      @IsDiscreteValuationRing (Y.presheaf.stalk x) inferInstance hdom := by
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hfxU : f.base x ∈ U := hle hxV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (f.base x)]; exact hfxU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(Y, V) := (f.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra k Γ(Y, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(Y, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨hdom, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  letI := hdom
  letI := hdvr
  letI : Algebra Γ(Y, V) (Y.presheaf.stalk x) := (Y.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  let e' := (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) (Y.presheaf.stalk x)).toRingEquiv
  letI : IsDomain (Y.presheaf.stalk x) := e'.symm.toMulEquiv.isDomain
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e'⟩

theorem boundary_nonempty (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) :
    (boundary k L D X).Nonempty := by
  classical
  letI := X.openImmersion
  letI := X.proper
  letI := (ArithmeticThetaLegendreAtlasR0176.legendre_family_geometry k).1
  letI := D.cover.surjective
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
    (ArithmeticThetaLegendreAtlasR0176.LegendreRing k))) := inferInstance
  obtain ⟨c, hc⟩ := (D.cover.inclusion ≫ D.atlas.level.projection).surjective z
  letI : Nonempty (OpenBase k L D) := ⟨D.quotient.quotient.q c⟩
  by_contra hempty
  have hsurj : Surjective X.inclusion := ⟨by
    intro x
    by_contra hx
    exact hempty ⟨x, hx⟩⟩
  letI := hsurj
  letI : IsIso X.inclusion :=
    (isIso_iff_isOpenImmersion_and_surjective X.inclusion).mpr ⟨inferInstance, inferInstance⟩
  letI : IsProper (openStructure k L D) := X.over_eq ▸ inferInstance
  letI : IsAffineHom (openStructure k L D) := isAffineHom_of_isAffine _
  letI : IsFinite (openStructure k L D) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set (OpenBase k L D)).Finite := by
    simpa using (openStructure k L D).finite_preimage (Set.toFinite Set.univ)
  letI : Finite (OpenBase k L D) := Set.finite_univ_iff.mp hfin
  letI : JacobsonSpace (OpenBase k L D) :=
    LocallyOfFiniteType.jacobsonSpace (openStructure k L D)
  letI : SmoothOfRelativeDimension 1 (openStructure k L D) := D.quotient.quotient.smooth
  have hdim := SmoothOfRelativeDimension.le_topologicalKrullDim (openStructure k L D) 1
  have hz := topologicalKrullDim_zero_of_discreteTopology (OpenBase k L D)
  exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) (hdim.trans hz)

end BoundaryGeometry
theorem level_boundary_geometry :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (D : LevelData k L) (X : Compactification k L D),
      Set.Finite (boundary k L D X) ∧ Set.Nonempty (boundary k L D X) ∧
      ∀ x ∈ boundary k L D X, IsClosed ({x} : Set X.space) ∧
      ∃ hdom : IsDomain (X.space.presheaf.stalk x),
        @IsDiscreteValuationRing (X.space.presheaf.stalk x) inferInstance hdom ∧
        FiniteResidue k L D X x := by
  intro k _ _ L hL heven D X
  refine ⟨BoundaryGeometry.boundary_finite k L D X,
    BoundaryGeometry.boundary_nonempty k L D X, ?_⟩
  intro x hx
  have hc := BoundaryGeometry.boundary_point_closed k L D X x hx
  letI := X.smooth
  obtain ⟨hd, hv⟩ := BoundaryGeometry.dvr_of_closed X.projection x hc
  exact ⟨hc, hd, hv, BoundaryGeometry.finiteResidue_of_closed k L D X x hc⟩

end ArithmeticThetaLevelCompactificationR0179
