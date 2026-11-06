import RamifiedPeriodRecoveryDefinitionsR0155

/-! The actual ramified Laurent field map and its degree. -/
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155

open ArithmeticThetaRamifiedPeriodR0154

namespace RamifiedLaurentExtension

/-- Transport the rank of a specified ring map to its specified fraction-field map.
The two scalar towers are established from the commuting square. -/
private theorem degree_of_basis
    {R S K L : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (φ : R →+* S) (ell : K →+* L)
    (hc : ∀ x, ell (algebraMap R K x) = algebraMap S L (φ x))
    (d : ℕ) (hd : 0 < d)
    (b : @Module.Basis (Fin d) R S _ _ (@Algebra.toModule R S _ _ φ.toAlgebra)) :
    let := ell.toAlgebra
    FiniteDimensional K L ∧ Module.finrank K L = d := by
  let := φ.toAlgebra
  let := ell.toAlgebra
  let : Algebra R L := ((algebraMap S L).comp φ).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (hc x).symm)
  have hr : Module.finrank K L = d := by
    rw [IsFractionRing.finrank_eq R K S L]
    simpa using Module.finrank_eq_card_basis b
  exact ⟨Module.finite_of_finrank_pos (hr ▸ hd), hr⟩

private theorem baseMap_injective (k : Type u) [Field k] [CharZero k]
    (d : ℕ) (hd : 0 < d) : Function.Injective (baseMap k d hd) := by
  intro f g h
  ext n
  have he := congrArg (PowerSeries.coeff (d * n)) h
  simpa [baseMap] using he

end RamifiedLaurentExtension

/-- The unique ramified Laurent extension, with the scalar action induced by the map. -/
theorem ramified_laurent_extension :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d),
      ∃! ell : LaurentSeries k →+* LaurentSeries k,
        ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell ∧
          ArithmeticThetaRamifiedPeriodR0155.LaurentDegree k d ell := by
  intro k _ _ d hd
  let g := (algebraMap (PowerSeries k) (LaurentSeries k)).comp (baseMap k d hd)
  have hg : Function.Injective g :=
    (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
      (RamifiedLaurentExtension.baseMap_injective k d hd)
  let ell : LaurentSeries k →+* LaurentSeries k := IsFractionRing.lift hg
  have he : IsLaurentExtension k d hd ell := by
    intro b
    exact IsFractionRing.lift_algebraMap hg b
  obtain ⟨b, _⟩ := ArithmeticThetaArithmeticRamificationR0096.ramified_monomial_basis
    k d hd (PowerSeries.expand d (Nat.ne_of_gt hd)) (by
      rw [PowerSeries.expand_X, PowerSeries.order_X_pow])
  refine ⟨ell, ⟨he, ?_⟩, ?_⟩
  · exact RamifiedLaurentExtension.degree_of_basis (baseMap k d hd) ell he d hd b
  · intro other ho
    exact IsFractionRing.ringHom_ext (fun x => (ho.1 x).trans (he x).symm)

end ArithmeticThetaRamifiedPeriodR0155

#print axioms ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension
