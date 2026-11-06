module

public import InfinitesimalPolygonDefinitionsR0129
public import IndexedAdjacentCoordinatesR0058

@[expose] public section

/-! Unique descent of the specified adjacent coordinate equivalence to every
nilpotent stage. The parameter preservation proof uses the accepted scalar
equation and the algebra structure of the actual node equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaInfinitesimalPolygonR0129

open ArithmeticThetaIndexedOverlapsR0058

variable (k : Type u) [Field k] [CharZero k]

private lemma rawAdjacent_parameter :
    rawAdjacent k (openParameter k false) = openParameter k true := by
  change (adjacent k 1 0) (openParameter k false) = openParameter k true
  have h := (indexed_adjacent_coordinates k 1 0 (by decide) (by decide)).1
  have hn : nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X) =
      ArithmeticThetaNodeCharts.t k := by
    unfold nodeEquiv ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase
      ArithmeticThetaNodeCharts.t ArithmeticThetaNodeCharts.parameter
    exact AlgEquiv.commutes _ _
  simpa [openBase, openMap, rawAdjacent, openParameter,
    hn] using
    congrArg (fun f => f (PowerSeries.X)) h

private lemma rawAdjacent_ideal_map :
    Ideal.map (rawAdjacent k).toRingHom
        (Ideal.span {openParameter k false}) = Ideal.span {openParameter k true} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {rawAdjacent k (openParameter k false)} =
    Ideal.span {openParameter k true}
  rw [rawAdjacent_parameter k]

private lemma rawAdjacent_pow_map (n : ℕ) :
    Ideal.map (rawAdjacent k).toRingHom ((Ideal.span {openParameter k false}) ^ (n + 1)) =
      (Ideal.span {openParameter k true}) ^ (n + 1) := by
  rw [Ideal.map_pow, rawAdjacent_ideal_map]

private def quotientAdjacent (n : ℕ) : B k n false ≃+* B k n true :=
  Ideal.quotientEquiv
    ((Ideal.span {openParameter k false}) ^ (n + 1))
    ((Ideal.span {openParameter k true}) ^ (n + 1))
    (rawAdjacent k) (rawAdjacent_pow_map k n).symm

private lemma quotientAdjacent_mk (n : ℕ) (x : RawOpen k false) :
    quotientAdjacent k n (trunc (RawOpen k false) (openParameter k false) n x) =
      trunc (RawOpen k true) (openParameter k true) n (rawAdjacent k x) := by
  rfl

theorem finite_stage_adjacent :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ n : ℕ,
      ∃! E : B k n false ≃+* B k n true, IsAdjacent k n E := by
  intro k _ _ n
  let E : B k n false ≃+* B k n true := quotientAdjacent k n
  have hE : IsAdjacent k n E := by
    apply RingHom.ext
    intro x
    change E (trunc (RawOpen k false) (openParameter k false) n x) =
      trunc (RawOpen k true) (openParameter k true) n (rawAdjacent k x)
    exact quotientAdjacent_mk k n x
  refine ⟨E, hE, ?_⟩
  intro F hF
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change F (trunc (RawOpen k false) (openParameter k false) n x) = _
  exact (congrArg (fun f => f x) hF).trans (congrArg (fun f => f x) hE).symm

end ArithmeticThetaInfinitesimalPolygonR0129
