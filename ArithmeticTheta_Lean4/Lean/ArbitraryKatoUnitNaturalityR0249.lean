import ArbitraryKatoUnitExistenceR0249

/-! Naturality of the complete Kato unit through the specified pointed
Cartesian comparison, over arbitrary rational coefficient rings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryKatoUnitR0249
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaArbitraryDiscriminantR0243

namespace ArbitraryKatoUnitNaturality

/-- Keep the normal source and compose its actual scalar and scheme maps. -/
def composeModel {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {W : WeierstrassCurve R} {V : WeierstrassCurve S}
    (M : NormalModel R W) (ι : R →ₐ[ℚ] S)
    (C : Comparison R S W V ι.toRingHom) : NormalModel S V where
  ring := M.ring
  equation := M.equation
  law := M.law
  originLaw := M.originLaw
  scalar := ι.comp M.scalar
  comparison := NormalDiscriminantIndependence.comparisonCompose M.comparison C

end ArbitraryKatoUnitNaturality

/-- Universal normal-model normalization commutes with the actual sheaf
pullback. Neither coefficient map is required to be injective. -/
theorem arbitrary_kato_unit_naturality :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
      [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
      ∀ (S : Type u) [CommRing S] [Algebra ℚ S] (V : WeierstrassCurve S)
      [V.IsElliptic] (H : Law S V), IsOriginLaw S V H →
      ∀ (ι : R →ₐ[ℚ] S) (C : Comparison R S W V ι.toRingHom),
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∀ (v : UnitSection R W G c) (w : UnitSection S V H c),
      IsKatoUnit R W G c v → IsKatoUnit S V H c w →
      ∃ e : complement S V H c ≤
          (TopologicalSpace.Opens.map C.map.base).obj (complement R W G c),
        (w : (Curve S V).presheaf.obj (Opposite.op (complement S V H c))) =
          C.map.appLE _ _ e (v : _) := by
  intro R _ _ W _ G hG S _ _ V _ H hH ι C c hc hc6 v w hv hw
  obtain ⟨M⟩ := normal_discriminant_model R W
  let N := ArbitraryKatoUnitNaturality.composeModel M ι C
  have e : complement S V H c ≤ C.map ⁻¹ᵁ complement R W G c :=
    le_of_eq (NormalModelUnitSpecialization.complement_eq C G hG H hH c)
  let p := C.map.appLE (complement R W G c) (complement S V H c) e
  let u : UnitSection S V H c := Units.map p.hom v
  have hu : FromModel S V H N c u := by
    obtain ⟨hU, g, hg, a, ha, hfield, eM, hvM⟩ := hv M
    have eN : complement S V H c ≤
        N.comparison.map ⁻¹ᵁ complement N.ring N.equation N.law c :=
      e.trans ((TopologicalSpace.Opens.map C.map.base).map (homOfLE eM)).le
    refine ⟨hU, g, hg, a, ha, hfield, eN, ?_⟩
    change p (v : _) = _
    rw [hvM]
    have hh := Scheme.Hom.appLE_comp_appLE C.map M.comparison.map
      (complement M.ring M.equation M.law c) (complement R W G c)
      (complement S V H c) eM e
    exact congrArg (fun f : Γ(Curve M.ring M.equation,
      complement M.ring M.equation M.law c) ⟶ Γ(Curve S V, complement S V H c) =>
        f a) hh
  obtain ⟨z, hz, hz_unique⟩ := normal_model_unit_specialization S V H hH c hc hc6 N
  have hwu : w = u := (hz_unique w (hw N)).trans (hz_unique u hu).symm
  refine ⟨e, ?_⟩
  rw [hwu]
  rfl

end ArithmeticThetaArbitraryKatoUnitR0249

#print axioms ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_naturality
