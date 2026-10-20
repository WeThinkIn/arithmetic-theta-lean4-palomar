module

public import CompactModularityDefinitionsR0209

@[expose] public section

/-! The categorical interior of the original compact comparison cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaCompactModularityR0209
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

namespace CompactInteriorLevelR0209

private lemma clopen_rank_le_one {X : Scheme} (U : X.Opens)
    (hU : IsClosed (U : Set X)) (x : X) : U.ι.finrank x ≤ 1 := by
  classical
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  have hsup : U ⊔ V = ⊤ := by ext y; simp [V]
  have hinf : U ⊓ V = ⊥ := by ext y; simp [V]
  have h := ArithmeticThetaGlobalization.SelectedComponent.finrank_clopen_add
    (𝟙 X) U V hsup hinf x
  simp only [Category.comp_id, Scheme.Hom.finrank_eq_one_of_isIso, Pi.one_apply] at h
  omega

private lemma clopen_rank_zero {X : Scheme} (U : X.Opens)
    (hU : IsClosed (U : Set X)) (x : X) (hx : x ∉ U) : U.ι.finrank x = 0 := by
  classical
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  letI : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact U.isOpen.isClosed_compl)
  have hsup : U ⊔ V = ⊤ := by ext y; simp [V]
  have hinf : U ⊓ V = ⊥ := by ext y; simp [V]
  have h := ArithmeticThetaGlobalization.SelectedComponent.finrank_clopen_add
    (𝟙 X) U V hsup hinf x
  simp only [Category.comp_id, Scheme.Hom.finrank_eq_one_of_isIso, Pi.one_apply] at h
  have hpos : 1 ≤ V.ι.finrank x := Scheme.Hom.one_le_finrank_map V.ι ⟨x, hx⟩
  omega

/-- The actual projection has rank zero over every other compact component. -/
lemma interior_rank_zero_off_component
    (k : Type) [Field k] [CharZero k] (L b : ℕ) (K : CompactRoot k L b)
    (hK : Etale K.cover.map) (z : OpenBase k L K.data)
    (hz : K.compact.inclusion z ∉ componentOpen k L K.data K.compact K.point) :
    (interiorMap K).finrank z = 0 := by
  letI := K.cover.finite
  letI := K.cover.flat
  letI := hK
  have hc : IsClosed (componentOpen k L K.data K.compact K.point : Set K.compact.space) :=
    compactComponent_closed k L K.data K.compact K.point
  letI : IsClosedImmersion (inclusion k L K.data K.compact K.point) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hc)
  let y := _root_.genericPoint (Component k L K.data K.compact K.point)
  have hconst : ∀ w, K.cover.map.finrank w = K.cover.map.finrank y := fun w =>
    (Scheme.Hom.isLocallyConstant_finrank K.cover.map).apply_eq_of_isPreconnected
      PreconnectedSpace.isPreconnected_univ trivial trivial
  rw [Scheme.Hom.finrank_pullback_snd,
    Scheme.Hom.finrank_comp_of_finrank_eq_const K.cover.map
      (inclusion k L K.data K.compact K.point) (K.cover.map.finrank y) hconst,
    clopen_rank_zero _ hc _ hz, Nat.mul_zero]

end CompactInteriorLevelR0209

/-- Base change along the original full-level open immersion preserves the
finite étale cover, density, and the original upper bound on pointwise rank. -/
theorem compact_interior_level
    (k : Type) [Field k] [CharZero k] (L b : ℕ) (K : CompactRoot k L b)
    (hK : Etale K.cover.map) : InteriorGeometry K := by
  letI := K.compact.openImmersion
  letI := K.cover.finite
  letI := K.cover.flat
  letI := hK
  have hc : IsClosed (componentOpen k L K.data K.compact K.point : Set K.compact.space) :=
    compactComponent_closed k L K.data K.compact K.point
  letI : IsClosedImmersion (inclusion k L K.data K.compact K.point) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hc)
  letI : IsFinite (compactMap K) := inferInstance
  letI : Etale (compactMap K) := inferInstance
  refine ⟨inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · change Dense (Set.range (pullback.fst (compactMap K) K.compact.inclusion))
    rw [IsOpenImmersion.range_pullbackFst]
    exact K.compact.dense.preimage (compactMap K).isOpenMap
  · intro z
    rw [Scheme.Hom.finrank_pullback_snd]
    let y := _root_.genericPoint (Component k L K.data K.compact K.point)
    have hconst : ∀ w, K.cover.map.finrank w = K.cover.map.finrank y := fun w =>
      (Scheme.Hom.isLocallyConstant_finrank K.cover.map).apply_eq_of_isPreconnected
        PreconnectedSpace.isPreconnected_univ trivial trivial
    rw [Scheme.Hom.finrank_comp_of_finrank_eq_const K.cover.map
      (inclusion k L K.data K.compact K.point) (K.cover.map.finrank y) hconst]
    calc
      _ ≤ K.cover.map.finrank y * 1 := Nat.mul_le_mul_left _
        (CompactInteriorLevelR0209.clopen_rank_le_one _ hc _)
      _ ≤ b := by simpa using (K.cover.degree y).2

#print axioms compact_interior_level
#print axioms CompactInteriorLevelR0209.interior_rank_zero_off_component
end ArithmeticThetaCompactModularityR0209
