module

public import RaisedSiegelTorsionFormulaR0159
public import UnsplitMarkedKatoValueR0159
public import LaurentGammaExistenceR0064

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaMarkedKatoValuesR0159

/-- The unique normalized Kato function has the exact raised Siegel value at
all nonidentity marked N-torsion points over the original coefficient field. -/
theorem actual_torsion_power_value :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (N : ℕ) (hN : 0 < N), ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G (1+12*N) g ∧ (∀ (j : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j a p), r ∣ N*j.val → (a : k)^N = 1 → (j.val ≠ 0 ∨ (a : k) ≠ 1) → ∀ (γ : LaurentSeries k), ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ → ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g (ArithmeticThetaMarkedKatoValuesR0159.siegelPower k r (1+12*N) j.val (a : k) γ)) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ N hN
  have hc : 1 < 1 + 12 * N := by omega
  have hc6 : Nat.Coprime (1 + 12 * N) 6 := by
    rw [show 12 * N = (2 * N) * 6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2 * N)).mpr (Nat.coprime_one_left 6)
  have hcN : Nat.Coprime (1 + 12 * N) N :=
    (Nat.coprime_add_mul_right_left 1 N 12).mpr (Nat.coprime_one_left N)
  obtain ⟨g, hg, hunique⟩ :=
    ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
      k r hr h3 T he M hM s hs G hG (1 + 12 * N) hc hc6
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro j a p hp hidx haN hne γ hγ
    obtain ⟨δ, hδ, _⟩ := ArithmeticThetaLaurentNormR0064.gamma_exists_unique
      k r ((1 + 12 * N) * j.val) ((a : k) ^ (1 + 12 * N)) hr
      (pow_ne_zero _ (Units.ne_zero a))
    have hv := unsplit_marked_kato_value k r hr h3 he T M hM s hs G hG
      (1 + 12 * N) hc hc6 j a p hp N hN hcN hidx haN hne g hg γ δ hγ hδ
    rw [raised_siegel_torsion_formula k r N j.val a γ δ hr hN j.isLt
      hidx haN hne hγ hδ] at hv
    exact hv
  · intro g' hg'
    exact hunique g' hg'.1

#print axioms actual_torsion_power_value
end ArithmeticThetaMarkedKatoValuesR0159
