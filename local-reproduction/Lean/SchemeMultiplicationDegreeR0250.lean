import SchemeTorsionCartesianR0250

/-! Finite étale multiplication and its degree on arbitrary elliptic families. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoUnitR0250
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence

namespace SchemeMultiplicationDegree

lemma affine_degree (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    (n : ℕ) (hn : 0 < n) :
    IsFinite (G.schemeNsmul n) ∧ Etale (G.schemeNsmul n) ∧
      Surjective (G.schemeNsmul n) ∧ ∀ x, (G.schemeNsmul n).finrank x = n ^ 2 := by
  obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model R W
  obtain ⟨hf, he, hs, hr, _⟩ :=
    ArithmeticThetaRelativeKatoR0169.relative_multiplication_degree
      M.ring M.equation M.law M.originLaw n hn
  letI := hf
  letI := he
  letI := hs
  have hp : IsPullback M.comparison.map
      (G.schemeNsmul n ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W)
      (M.law.schemeNsmul n ≫ ArithmeticThetaRelativeKatoR0169.structureMap M.ring M.equation)
      (Spec.map (CommRingCat.ofHom M.scalar.toRingHom)) := by
    simpa only [WeierstrassProjModel.RelativeGroupLaw.schemeNsmul_over] using
      M.comparison.cartesian
  have hb : IsPullback M.comparison.map (G.schemeNsmul n)
      (M.law.schemeNsmul n) M.comparison.map :=
    hp.of_bot (ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitSpecialization.comparison_nsmul
      M.comparison M.law M.originLaw G hG n).symm M.comparison.cartesian
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) hb hf,
    MorphismProperty.of_isPullback (P := @Etale) hb he,
    MorphismProperty.of_isPullback (P := @Surjective) hb hs, ?_⟩
  intro x
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hb x).trans (hr _)

lemma weierstrass_multiple (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W)) (n : ℕ) :
    multiple (weierstrassFamily R W G hG) t n x = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih => change G.mul _ (multiple (weierstrassFamily R W G hG) t n x) x = G.mul _ (G.nsmul _ n x) x; rw [ih]

lemma weierstrass_multiplication (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) :
    multiplication (weierstrassFamily R W G hG) n = G.schemeNsmul n := by
  exact congrArg Subtype.val (weierstrass_multiple R W G hG _ _ n)

attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic LocalPresentation.openImmersion

variable {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
  (σ : S ⟶ Base k) (E : Family S)

lemma chart_square (P : LocalPresentation k S σ E) (n : ℕ) :
    IsPullback P.comparison (P.law.schemeNsmul n) (multiplication E n) P.comparison := by
  have h := (scheme_torsion_cartesian k S σ E (Base P.ring)
    (Spec.map (CommRingCat.ofHom (algebraMap k P.ring)))
    (chartFamily P) P.base P.base_eq (chartComparison P) n).1
  simpa only [chartComparison, chartFamily, weierstrass_multiplication] using h

lemma chart_covers (x : E.curve) :
    ∃ P : LocalPresentation k S σ E, x ∈ Set.range P.comparison := by
  obtain ⟨P, y, hy⟩ := scheme_local_weierstrass k S σ E (E.p x)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback P.cartesian x y hy.symm
  exact ⟨P, z, hz⟩

lemma chart_open (P : LocalPresentation k S σ E) : IsOpenImmersion P.comparison :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) P.cartesian.flip inferInstance

lemma descend (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (n : ℕ) (h : ∀ P : LocalPresentation k S σ E, Q (P.law.schemeNsmul n)) :
    Q (multiplication E n) := by
  classical
  choose P hx using chart_covers σ E
  letI (x : E.curve) : IsOpenImmersion (P x).comparison := chart_open σ E (P x)
  let cov : E.curve.OpenCover :=
    { I₀ := E.curve
      X := fun x => ArithmeticThetaRelativeKatoR0169.Curve (P x).ring (P x).equation
      f := fun x => (P x).comparison
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x, hx x⟩, fun x => inferInstance⟩ }
  apply IsZariskiLocalAtTarget.of_openCover (P := Q) cov
  intro x
  have hb := chart_square σ E (P x) n
  change Q (pullback.snd (multiplication E n) (P x).comparison)
  rw [← hb.isoPullback_inv_snd]
  exact (Q.cancel_left_of_respectsIso _ _).mpr (h (P x))

lemma chart_degree (P : LocalPresentation k S σ E) (n : ℕ) (hn : 0 < n) :
    IsFinite (P.law.schemeNsmul n) ∧ Etale (P.law.schemeNsmul n) ∧
      Surjective (P.law.schemeNsmul n) ∧
      ∀ x, (P.law.schemeNsmul n).finrank x = n ^ 2 := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  exact affine_degree P.ring P.equation P.law P.originLaw n hn

end SchemeMultiplicationDegree

/-- Positive multiplication on every characteristic-zero elliptic scheme family
is finite étale surjective, with degree n² at every target point. -/
theorem scheme_multiplication_degree :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S), ∀ n : ℕ, 0 < n →
      IsFinite (multiplication E n) ∧ Etale (multiplication E n) ∧
      Surjective (multiplication E n) ∧
      ∀ x : E.curve, (multiplication E n).finrank x = n ^ 2 := by
  intro k _ _ S σ E n hn
  have hd := SchemeMultiplicationDegree.chart_degree σ E
  letI : IsFinite (multiplication E n) :=
    SchemeMultiplicationDegree.descend σ E (@IsFinite) n (fun P => (hd P n hn).1)
  letI : Etale (multiplication E n) :=
    SchemeMultiplicationDegree.descend σ E (@Etale) n (fun P => (hd P n hn).2.1)
  letI : Surjective (multiplication E n) :=
    SchemeMultiplicationDegree.descend σ E (@Surjective) n (fun P => (hd P n hn).2.2.1)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro x
  obtain ⟨P, y, hy⟩ := SchemeMultiplicationDegree.chart_covers σ E x
  rw [← hy, ← Scheme.Hom.finrank_of_isPullback _ _ _ _
    (SchemeMultiplicationDegree.chart_square σ E P n) y]
  exact (hd P n hn).2.2.2 y

#print axioms scheme_multiplication_degree
end ArithmeticThetaSchemeKatoUnitR0250
