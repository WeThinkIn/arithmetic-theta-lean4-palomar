import MarkedPointAdditionR0146

/-! Exact torsion of actual marked sections, detected on the special fiber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaPolygonCohomologyR0131

namespace MarkedExactTorsion
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (M : Model k T) (hM : IsModel k T M)
include hM

/-- Equality of actual generic marks forces equality of both labels. -/
lemma labels_eq {i j : Fin r} {a b : kˣ} (p q : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (hq : MarkedLift k M j b q)
    (h : pointOver k M (𝟙 _) p hp.1 = pointOver k M (𝟙 _) q hq.1) :
    i = j ∧ a = b := by
  have hg : genericPoint k M p hp.1 = genericPoint k M q hq.1 := by
    simpa only [pointOver, Category.id_comp] using congrArg Subtype.val h
  have hpq : p = q := by
    let : IsProper M.p := hM.1
    let : IsReduced (baseScheme k) := inferInstanceAs (IsReduced (Spec (CommRingCat.of (PowerSeries k))))
    let : IsSchemeTheoreticallyDominant (genericBase k) :=
      GenericDualLocalizationR0140.genericBase_schematic k
    apply ext_of_isDominant_of_isSeparated M.p (hp.1.trans hq.1.symm) (genericBase k)
    have hh := congrArg (fun f => f ≫ genericInclusion k M) hg
    simpa only [ArithmeticThetaGenericEvaluationR0140.genericPoint,
      genericInclusion, pullback.lift_fst] using hh
  have h0 := (hp.2 0).symm.trans
    ((congrArg (fun f => baseInclusion k 0 ≫ f) hpq).trans (hq.2 0))
  let : IsClosedImmersion (M.inclusion 0) :=
    AlgebraizedGeometricConnectednessR0135.stage_closed k M hM 0
  have hmarks := (cancel_mono (M.inclusion 0)).mp h0
  have hij : i = j := by
    by_contra hn
    let : Nontrivial (R k 0) := by
      apply Ideal.Quotient.nontrivial_iff.mpr
      apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)).ne_top
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.pow_le_self (by omega)
    obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum (R k 0)))
    exact Set.disjoint_left.mp
      (CompatibleMarkingsR0131.disjoint_markings k r 0 hr (T.atlas 0) i j hn a b)
      ⟨x, rfl⟩ ⟨x, congrArg (fun f : specR k 0 ⟶ (T.atlas 0).X => f x) hmarks.symm⟩
  subst j
  exact ⟨rfl, ActualScalarTranslation.markedLift_parameter_injective k M hM i p q hp hq hpq⟩

variable (h3 : 3 ≤ r) (he : Even r) (s : baseScheme k ⟶ M.X)
variable (hs : MarkedLift k M (zeroIndex r hr) 1 s)
variable (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
open MarkedPointAddition
include s hs hG

lemma point_one : point k h3 M hM (zeroIndex r hr) 1 = G.one (𝟙 _) := by
  rw [hG.1, point_eq k h3 M hM _ _ s hs]

include he in
lemma point_mul (i j : Fin r) (a b : kˣ) :
    G.mul (𝟙 _) (point k h3 M hM i a) (point k h3 M hM j b) =
      point k h3 M hM (sumIndex (hr := hr) i j) (a*b) := by
  exact marked_point_addition k r hr h3 T he M hM s hs G hG i j a b
    _ _ _ (sectionAt_spec k h3 M hM i a) (sectionAt_spec k h3 M hM j b)
    (sectionAt_spec k h3 M hM _ _)

include he in
/-- Multiplication by n retains the actual section and all modular carries. -/
lemma point_nsmul (i : Fin r) (a : kˣ) (n : ℕ) :
    G.nsmul (𝟙 _) n (point k h3 M hM i a) =
      point k h3 M hM ⟨(n*i.val)%r, Nat.mod_lt _ hr⟩ (a^n) := by
  induction n with
  | zero =>
    simpa only [WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, zero_mul,
      Nat.zero_mod, pow_zero, zeroIndex] using (point_one k M hM h3 s hs G hG).symm
  | succ n ih =>
    rw [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ, ih,
      point_mul k M hM h3 he s hs G hG, pow_succ]
    congr 1
    apply Fin.ext
    simp only [sumIndex, Nat.succ_mul, Nat.mod_add_mod]

lemma point_eq_one_iff (i : Fin r) (a : kˣ) :
    point k h3 M hM i a = G.one (𝟙 _) ↔ i = zeroIndex r hr ∧ a = 1 := by
  rw [← point_one k M hM h3 s hs G hG]
  constructor
  · intro hh
    exact labels_eq k M hM _ _ (sectionAt_spec k h3 M hM i a)
      (sectionAt_spec k h3 M hM _ _) hh
  · rintro ⟨rfl, rfl⟩
    rfl

end MarkedExactTorsion

/-- Exact torsion criterion for every natural multiplier, including zero. -/
theorem marked_exact_torsion :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
    ∀ (G : Law k M), IsOriginLaw k M s hs.1 G →
    ∀ (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (n : ℕ),
    G.nsmul (𝟙 (Spec (CommRingCat.of (LaurentSeries k)))) n
      (pointOver k M (𝟙 _) p hp.1) = G.one (𝟙 _) ↔ r ∣ n*i.val ∧ a^n = 1 := by
  intro k _ _ r hr h3 T he M hM s hs G hG i a p hp n
  rw [← MarkedPointAddition.point_eq k h3 M hM i a p hp,
    MarkedExactTorsion.point_nsmul k M hM h3 he s hs G hG,
    MarkedExactTorsion.point_eq_one_iff k M hM h3 s hs G hG]
  have hi : (⟨n*i.val%r, Nat.mod_lt _ hr⟩ : Fin r) = zeroIndex r hr ↔ r ∣ n*i.val := by
    rw [Fin.ext_iff]
    exact Nat.dvd_iff_mod_eq_zero.symm
  rw [hi]

#print axioms marked_exact_torsion
end ArithmeticThetaMarkedGroupLawR0146
