module

public import ActualMultiplicationFieldNormR0150
public import GeometricNormOrdersR0150

@[expose] public section

-- Keep the original elaborated instance paths after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaGeometricNormR0150.CoprimeTorsion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

variable {F : Type u} [Field F] {X : Scheme.{u}}
variable {p : X ⟶ Spec (.of F)} (G : WeierstrassProjModel.RelativeGroupLaw F p)

lemma nsmul_pow {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (n : ℕ)
    (z : SchemeHomOver t p) :
    letI := G.pointGroup t
    G.nsmul t n z = z ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl

lemma nsmul_mul {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (a b : ℕ)
    (z : SchemeHomOver t p) : G.nsmul t a (G.nsmul t b z) = G.nsmul t (b*a) z := by
  letI := G.pointGroup t
  simpa only [nsmul_pow] using (pow_mul z b a).symm

lemma nsmul_inverse {V : Scheme.{u}} (t : V ⟶ Spec (.of F))
    (c d a : ℕ) (ha : d*a % c = 1) (z : SchemeHomOver t p)
    (hz : G.nsmul t c z = G.one t) : G.nsmul t a (G.nsmul t d z) = z := by
  letI := G.pointGroup t
  have hz' : z^c = 1 := (nsmul_pow G t c z).symm.trans hz
  rw [nsmul_mul, nsmul_pow]
  have H : z^(d*a) = z^(d*a % c) := by
    conv_lhs => rw [← Nat.mod_add_div (d*a) c]
    rw [pow_add, pow_mul, hz', one_pow, mul_one]
  rw [H, ha, pow_one]

lemma nsmul_preserves {V : Scheme.{u}} (t : V ⟶ Spec (.of F))
    (c d : ℕ) (z : SchemeHomOver t p) (hz : G.nsmul t c z = G.one t) :
    G.nsmul t c (G.nsmul t d z) = G.one t := by
  rw [nsmul_mul, Nat.mul_comm d c, ← nsmul_mul, hz, G.nsmul_unit]

lemma section_one (t : X ⟶ Spec (.of F)) :
    (G.one t).val = t ≫ (G.one (𝟙 _)).val := by
  exact (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id _))).symm

lemma one_mul_map (n : ℕ) :
    (G.one (𝟙 _)).val ≫ G.schemeNsmul n = (G.one (𝟙 _)).val := by
  rw [comp_schemeNsmul, G.nsmul_unit]

lemma residue_torsion (c : ℕ) (x : X)
    (hx : G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    G.nsmul (X.fromSpecResidueField x ≫ p) c
      (⟨X.fromSpecResidueField x, rfl⟩ : SchemeHomOver _ p) =
      G.one (X.fromSpecResidueField x ≫ p) := by
  let e := (G.one (𝟙 _)).val
  have he : e ≫ p = 𝟙 _ := (G.one (𝟙 _)).property
  letI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id p e he
  apply Subtype.ext
  rw [← comp_schemeNsmul]
  have h := field_point_eq_section (p := p)
    (X.fromSpecResidueField x ≫ G.schemeNsmul c) (X.fromSpecResidueField x ≫ p) e
    (by rw [Category.assoc, G.schemeNsmul_over]) he
    (IsLocalRing.closedPoint (X.residueField x)) (IsLocalRing.closedPoint F)
    (by change G.schemeNsmul c (X.fromSpecResidueField x _) = _
        rw [Scheme.fromSpecResidueField_apply]; exact hx)
  exact h.trans (congrArg Subtype.val
    (G.one_natural (𝟙 _) (X.fromSpecResidueField x ≫ p)
      (X.fromSpecResidueField x ≫ p) (Category.comp_id _)))

lemma residue_return (c d a : ℕ) (ha : d*a % c = 1) (x : X)
    (hx : G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    X.fromSpecResidueField x ≫ G.schemeNsmul d ≫ G.schemeNsmul a =
      X.fromSpecResidueField x := by
  rw [← Category.assoc, comp_schemeNsmul G _ ⟨X.fromSpecResidueField x, rfl⟩,
    comp_schemeNsmul, nsmul_inverse G _ c d a ha _ (residue_torsion G c x hx)]

lemma point_return (c d a : ℕ) (ha : d*a % c = 1) (x : X)
    (hx : G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    G.schemeNsmul a (G.schemeNsmul d x) = x := by
  have h := congrArg (fun f : Spec (X.residueField x) ⟶ X =>
    f (IsLocalRing.closedPoint (X.residueField x))) (residue_return G c d a ha x hx)
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h

lemma point_preserves (c d : ℕ) (x : X)
    (hx : G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    G.schemeNsmul c (G.schemeNsmul d x) =
      (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) := by
  have H : X.fromSpecResidueField x ≫ G.schemeNsmul d ≫ G.schemeNsmul c =
      (G.one (X.fromSpecResidueField x ≫ p)).val := by
    rw [← Category.assoc, comp_schemeNsmul G _ ⟨X.fromSpecResidueField x, rfl⟩,
      comp_schemeNsmul, nsmul_preserves G _ c d _ (residue_torsion G c x hx)]
  have hone := congrArg Subtype.val (G.one_natural (𝟙 _) (X.fromSpecResidueField x ≫ p)
    (X.fromSpecResidueField x ≫ p) (Category.comp_id _))
  rw [← hone] at H
  have h := congrArg (fun f : Spec (X.residueField x) ⟶ X =>
    f (IsLocalRing.closedPoint (X.residueField x))) H
  simpa only [WeierstrassProjModel.schemeHomOverComp_coe, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply, Subsingleton.elim (p x) (IsLocalRing.closedPoint F)] using h

omit G in
lemma residue_degree_lift {Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (v : Spec (Y.residueField y) ⟶ X) (hv : v ≫ f = Y.fromSpecResidueField y) :
    f.residueDegree (v (IsLocalRing.closedPoint (Y.residueField y))) = 1 := by
  let x := v (IsLocalRing.closedPoint (Y.residueField y))
  haveI : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo v)) :=
    Scheme.isLocalHom_stalkClosedPointTo v
  let b : X.residueField x ⟶ Y.residueField y :=
    @Scheme.descResidueField (Y.residueField y) _ X x (Scheme.stalkClosedPointTo v) inferInstance
  have hb : Spec.map b ≫ X.fromSpecResidueField x = v :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ v
  have e : f x = y := by
    have h := congrArg (fun q : Spec (Y.residueField y) ⟶ Y =>
      q (IsLocalRing.closedPoint (Y.residueField y))) hv
    exact h.trans (Scheme.fromSpecResidueField_apply _ _)
  have hcomp : f.residueFieldMap x ≫ b = (Y.residueFieldCongr e).hom := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecResidueField (f x))).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, hb, hv, Scheme.residueFieldCongr_fromSpecResidueField]
  have bij : Function.Bijective (f.residueFieldMap x) := by
    have H : Function.Bijective (f.residueFieldMap x ≫ b) := by
      rw [hcomp]; exact ConcreteCategory.bijective_of_isIso _
    refine ⟨(f.residueFieldMap x).hom.injective, fun z => ?_⟩
    obtain ⟨w, hw⟩ := H.2 (b z)
    exact ⟨w, b.hom.injective hw⟩
  letI := (f.residueFieldMap x).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr bij

lemma torsion_residue_degree (c d a : ℕ) (ha : d*a % c = 1) (x : X)
    (hx : G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    (G.schemeNsmul d).residueDegree x = 1 := by
  have hy := point_preserves G c d x hx
  have had : a*d % c = 1 := by simpa only [Nat.mul_comm] using ha
  have h := residue_degree_lift (G.schemeNsmul d) (G.schemeNsmul d x)
    (X.fromSpecResidueField (G.schemeNsmul d x) ≫ G.schemeNsmul a)
    (by rw [Category.assoc]; exact residue_return G c a d had _ hy)
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
    point_return G c d a ha x hx] using h

omit G in
lemma indicator_sum {A B : Type*} (f : A → B) (w : A → ℤ)
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q]
    (hw : ∀ x, P x → w x = 1)
    (hmap : ∀ x, P x → Q (f x))
    (hunique : ∀ y, Q y → ∃! x, f x = y ∧ P x)
    (y : B) [Fintype {x : A // f x = y}] (b : ℤ) :
    (∑ x : {x : A // f x = y}, w x.val * (if P x.val then b else 0)) =
      if Q y then b else 0 := by
  classical
  by_cases hy : Q y
  · obtain ⟨x, ⟨hxy, hx⟩, huniq⟩ := hunique y hy
    rw [if_pos hy, Finset.sum_eq_single (⟨x, hxy⟩ : {x : A // f x = y})]
    · rw [if_pos hx, hw x hx, one_mul]
    · intro z _ hz
      have hzP : ¬ P z.val := fun hp => hz (Subtype.ext (huniq z.val ⟨z.property, hp⟩))
      simp [hzP]
    · simp
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro x _
    have hx : ¬ P x.val := fun h => hy (x.property ▸ hmap x.val h)
    simp [hx]

lemma torsion_unique (c d a : ℕ) (ha : d*a % c = 1) (y : X)
    (hy : G.schemeNsmul c y = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)) :
    ∃! x, G.schemeNsmul d x = y ∧
      G.schemeNsmul c x = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) := by
  have had : a*d % c = 1 := by simpa only [Nat.mul_comm] using ha
  refine ⟨G.schemeNsmul a y, ⟨point_return G c a d had y hy,
    point_preserves G c a y hy⟩, ?_⟩
  intro x hx
  exact (point_return G c d a ha x hx.2).symm.trans (congrArg (G.schemeNsmul a) hx.1)

local instance : DecidableEq X := Classical.decEq _

lemma push_kato (c d a : ℕ) (ha : d*a % c = 1)
    [IsFinite (G.schemeNsmul d)] (y : X) :
    (∑ᶠ x : {x : X // G.schemeNsmul d x = y},
      ((G.schemeNsmul d).residueDegree x.val : ℤ) *
        ((if x.val = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) then (c : ℤ)^2 else 0) -
         (if G.schemeNsmul c x.val = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) then 1 else 0))) =
      ((if y = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) then (c : ℤ)^2 else 0) -
       (if G.schemeNsmul c y = (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) then 1 else 0)) := by
  classical
  let e := (G.one (𝟙 _)).val (IsLocalRing.closedPoint F)
  have he (n : ℕ) : G.schemeNsmul n e = e :=
    congrArg (fun f : Spec (.of F) ⟶ X => f (IsLocalRing.closedPoint F)) (one_mul_map G n)
  letI : Finite {x : X // G.schemeNsmul d x = y} :=
    ((G.schemeNsmul d).finite_preimage_singleton y).to_subtype
  letI : Fintype {x : X // G.schemeNsmul d x = y} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply indicator_sum (G.schemeNsmul d) (fun x => ((G.schemeNsmul d).residueDegree x : ℤ))
      (fun x => x = e) (fun y => y = e)
    · intro x hx
      subst x
      exact_mod_cast torsion_residue_degree G c d a ha e (he c)
    · intro x hx
      subst x
      exact he d
    · intro z hz
      subst z
      exact ⟨e, ⟨he d, rfl⟩, fun x hx => hx.2⟩
  · apply indicator_sum (G.schemeNsmul d) (fun x => ((G.schemeNsmul d).residueDegree x : ℤ))
      (fun x => G.schemeNsmul c x = e) (fun y => G.schemeNsmul c y = e)
    · intro x hx
      exact_mod_cast torsion_residue_degree G c d a ha x hx
    · exact point_preserves G c d
    · exact torsion_unique G c d a ha

end ArithmeticThetaGeometricNormR0150.CoprimeTorsion

namespace ArithmeticThetaGeometricNormR0150
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147

private lemma norm_nonzero {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y.functionField →+* X.functionField) (hfin : FiniteFieldMap φ)
    (g : X.functionField) (hg : g ≠ 0) : fieldNorm φ g ≠ 0 := by
  letI := φ.toAlgebra
  letI : FiniteDimensional Y.functionField X.functionField := hfin
  exact Algebra.norm_ne_zero_iff.mpr hg

/-- Coprime multiplication preserves the actual Kato divisor, including residue degrees. -/
theorem coprime_torsion_divisor_norm :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d → ∀ (φ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) φ → ∀ (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), g ≠ 0 → (∀ x : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M), AlgebraicGeometry.Scheme.ord g x = ArithmeticThetaGeometricNormR0150.katoOrder k M s hs.1 G c x) → (ArithmeticThetaGeometricNormR0150.fieldNorm φ g ≠ 0 ∧ ∀ x : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M), AlgebraicGeometry.Scheme.ord (ArithmeticThetaGeometricNormR0150.fieldNorm φ g) x = ArithmeticThetaGeometricNormR0150.katoOrder k M s hs.1 G c x) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _ c d hc hd hcd φ hφ g hg hdiv
  classical
  obtain ⟨hfinite, hetale, hsurj, _⟩ :=
    multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG d hd
  letI := hfinite
  letI := hetale
  letI := hsurj
  obtain ⟨ψ, hψ, hfin, _, _, huniq⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG d hd
  have heq : φ = ψ := huniq φ hφ
  have hfinφ : FiniteFieldMap φ := heq ▸ hfin
  have hnorm : fieldNorm φ g ≠ 0 := norm_nonzero φ hfinφ g hg
  refine ⟨hnorm, ?_⟩
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one
    k h3 M hM s hs
  obtain ⟨a, _, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcd.symm hc
  have he : (G.one (𝟙 _)).val (IsLocalRing.closedPoint (LaurentSeries k)) =
      identityPoint k M s hs.1 := by
    rw [hG.1]
    rfl
  intro x
  rw [geometric_norm_orders (LaurentSeries k) (genericScheme k M) (genericScheme k M) (genericStructure k M)
    (genericStructure k M) (multiplication k M G d)
    (MultiplicationDifferential.multiplication_over k M G d) φ hφ g hg x]
  unfold pushOrder
  simp_rw [hdiv, katoOrder]
  letI : IsFinite (G.schemeNsmul d) := hfinite
  have h := CoprimeTorsion.push_kato G c d a ha x
  rw [he] at h
  exact h

end ArithmeticThetaGeometricNormR0150
#print axioms ArithmeticThetaGeometricNormR0150.coprime_torsion_divisor_norm
