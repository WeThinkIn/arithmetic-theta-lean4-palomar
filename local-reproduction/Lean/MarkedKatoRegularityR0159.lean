import RationalValueTransportR0159

/-! Nonzero stalk values of Kato functions at marked torsion points. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedKatoValuesR0159
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

private lemma nonzero_value_of_order_zero (F : Type u) [Field F]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (π : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 π]
    [IsSeparated π] (p : Spec (CommRingCat.of F) ⟶ X) (hp : p ≫ π = 𝟙 _)
    (g : X.functionField) (hg : g ≠ 0)
    (ho : Scheme.ord g (p (IsLocalRing.closedPoint F)) = 0) :
    ∃ v : F, v ≠ 0 ∧ HasValue F X p g v := by
  let x := p (IsLocalRing.closedPoint F)
  letI : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id π p hp
  have hx : IsClosed ({x} : Set X) := by
    have he : Set.range p = {x} := Set.range_eq_singleton fun a =>
      congrArg p (Subsingleton.elim a (IsLocalRing.closedPoint F))
    rw [← he]
    exact p.isClosedEmbedding.isClosed_range
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed π x hx
  have hco : Order.coheight x = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hv : Ring.ordFrac (X.presheaf.stalk x) g = 1 :=
    (Scheme.ord_eq_iff hco hg).mp ho
  have hm : g ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk x)) := hv
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hm
  obtain ⟨b, hb, hbg⟩ := hm
  refine ⟨Scheme.stalkClosedPointTo p b, ?_, b, hbg, rfl⟩
  exact (hb.map (Scheme.stalkClosedPointTo p).hom).ne_zero

/-- Every nonidentity marked N-torsion point prime to c has a unique nonzero
value, obtained from a unit in its actual local ring. -/
theorem marked_kato_regularity :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (j : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j a p) (N : ℕ) (hN : 0 < N) (hcopN : Nat.Coprime c N) (hidx : r ∣ N*j.val) (haN : (a : k)^N = 1) (hne : j.val ≠ 0 ∨ (a : k) ≠ 1) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c g → ∃! v : LaurentSeries k, v ≠ 0 ∧ ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g (v) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ c hc hcop j a p hp N hN hcopN hidx haN hne g hg
  let P := pointOver k M (𝟙 _) p hp.1
  let x := genericPoint k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k))
  have htor (n : ℕ) : multiplication k M G n x = identityPoint k M s hs.1 ↔
      r ∣ n*j.val ∧ a^n = 1 := by
    have ht := ActualKatoDivisorPrincipal.field_point_torsion_iff G (𝟙 _) P n
    have ho : (G.one (𝟙 _)).val = genericPoint k M s hs.1 := by
      simpa only [pointOver, Category.id_comp] using congrArg Subtype.val (hG.1 (𝟙 _))
    rw [ho] at ht
    exact ht.symm.trans (marked_exact_torsion k r hr h3 T he M hM s hs G hG j a p hp n)
  have hx : x ≠ identityPoint k M s hs.1 := by
    intro hx
    have hx1 : multiplication k M G 1 x = identityPoint k M s hs.1 := by
      have hm : multiplication k M G 1 = 𝟙 _ := by
        unfold multiplication
        rw [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ,
          WeierstrassProjModel.RelativeGroupLaw.nsmul_zero, G.one_mul]
        rfl
      rw [hm]
      exact hx
    obtain ⟨hj, ha⟩ := (htor 1).mp hx1
    have hj0 : j.val = 0 := Nat.eq_zero_of_dvd_of_lt (by simpa using hj) j.isLt
    have ha1 : (a : k) = 1 := by simpa using congrArg Units.val ha
    exact hne.elim (fun h => h hj0) (fun h => h ha1)
  have hcx : multiplication k M G c x ≠ identityPoint k M s hs.1 := by
    intro hcx
    obtain ⟨hjc, hac⟩ := (htor c).mp hcx
    have hj : r ∣ j.val := by
      have hh := Nat.dvd_gcd hjc hidx
      simpa [Nat.gcd_mul_right, hcopN.gcd_eq_one] using hh
    have hj0 := Nat.eq_zero_of_dvd_of_lt hj j.isLt
    have haNu : a^N = 1 := by apply Units.ext; simpa using haN
    have hd : orderOf a ∣ Nat.gcd c N :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hac) (orderOf_dvd_of_pow_eq_one haNu)
    have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcopN.gcd_eq_one ▸ hd))
    exact hne.elim (fun h => h hj0) (fun h => h (congrArg Units.val ha1))
  have hord : Scheme.ord g x = 0 := by
    rw [hg.2 x]
    simp only [katoOrder, if_neg hx, if_neg hcx, sub_self]
  letI := generic_relative_one k h3 M hM s hs
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  obtain ⟨v, hv, hval⟩ := nonzero_value_of_order_zero (LaurentSeries k)
    (genericScheme k M) (genericStructure k M) (genericPoint k M p hp.1)
    (genericPoint_structure k M p hp.1) g hg.1 hord
  refine ⟨v, ⟨hv, hval⟩, ?_⟩
  intro w hw
  exact rational_value_transport.1 _ _ _ g w v hw.2 hval

#print axioms marked_kato_regularity
end ArithmeticThetaMarkedKatoValuesR0159
