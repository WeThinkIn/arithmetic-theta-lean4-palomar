import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import MultiplicationDifferentialR0148
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open WeierstrassProjModel
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- The two library presentations carry exactly the same natural group operations. -/
def toGRJ {F : Type u} [CommRing F] {C : Scheme.{u}} {p : C ⟶ Spec (.of F)}
    (G : WeierstrassProjModel.RelativeGroupLaw F p) : GoodReductionJacobian.RelativeGroupLaw F p :=
  ⟨G.mul, G.one, G.inv, G.mul_assoc, G.one_mul, G.mul_one, G.inv_mul_cancel, G.mul_natural⟩

lemma toGRJ_nsmul {F : Type u} [CommRing F] {C : Scheme.{u}} {p : C ⟶ Spec (.of F)}
    (G : WeierstrassProjModel.RelativeGroupLaw F p) {V : Scheme.{u}}
    (t : V ⟶ Spec (.of F)) (n : ℕ) (z : SchemeHomOver t p) :
    (toGRJ G).nsmul t n z = G.nsmul t n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_succ, ih]
    rfl

lemma toGRJ_schemeNsmul {F : Type u} [CommRing F] {C : Scheme.{u}} {p : C ⟶ Spec (.of F)}
    (G : WeierstrassProjModel.RelativeGroupLaw F p) (n : ℕ) :
    (toGRJ G).schemeNsmul n = G.schemeNsmul n :=
  congrArg Subtype.val (toGRJ_nsmul G p n _)

/-- In characteristic zero, the actual multiplication morphism on a smooth
commutative group is étale. -/
lemma etale_nsmul {F : Type u} [Field F] [CharZero F] {C : Scheme.{u}}
    {p : C ⟶ Spec (.of F)} (G : WeierstrassProjModel.RelativeGroupLaw F p)
    (hc : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x y : SchemeHomOver t p),
      G.mul t x y = G.mul t y x)
    [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : 0 < n) : Etale (G.schemeNsmul n) := by
  rw [← toGRJ_schemeNsmul]
  exact GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
    (toGRJ G) hc 1 n (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))

/-- A finite étale endomorphism has constant rank on a connected scheme;
the identity fiber computes that rank everywhere. -/
lemma rank_from_identity {F : Type u} [Field F] {C : Scheme.{u}}
    {p : C ⟶ Spec (.of F)} [PreconnectedSpace C]
    (G : WeierstrassProjModel.RelativeGroupLaw F p) (n d : ℕ)
    [IsFinite (G.schemeNsmul n)] [Etale (G.schemeNsmul n)]
    (hr : ∀ z, (G.schemeKerStr n).finrank z = d) :
    ∀ x, (G.schemeNsmul n).finrank x = d := by
  let z : Spec (.of F) := Classical.choice inferInstance
  intro x
  calc
    (G.schemeNsmul n).finrank x =
        (G.schemeNsmul n).finrank ((G.one (𝟙 _)).val z) :=
      (G.schemeNsmul n).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = (G.schemeKerStr n).finrank z := (Scheme.Hom.finrank_pullback_snd _ _ z).symm
    _ = d := hr z

/-- Transport of the natural law conjugates its multiplication morphisms. -/
lemma transport_multiplication {F : Type u} [CommRing F] {C D : Scheme.{u}}
    {p : C ⟶ Spec (.of F)} {q : D ⟶ Spec (.of F)}
    (E : C ≅ D) (hE : E.hom ≫ q = p) (hi : E.inv ≫ p = q)
    (G : WeierstrassProjModel.RelativeGroupLaw F p) (n : ℕ) :
    G.schemeNsmul n ≫ E.hom = E.hom ≫ (transport E.symm hi G).schemeNsmul n := by
  let z : SchemeHomOver p p := ⟨𝟙 _, Category.id_comp _⟩
  have h := congrArg Subtype.val (transport_symm_nsmul E hE hi G p z n)
  have H := comp_schemeNsmul (transport E.symm hi G) p (pointsEquiv E hE p z) n
  exact h.symm.trans H.symm

/-- Points of the scheme kernel are exactly points killed by multiplication,
with the structural map retained in both directions. -/
def kernelPointsEquiv {F : Type u} [CommRing F] {C : Scheme.{u}}
    {p : C ⟶ Spec (.of F)} (G : WeierstrassProjModel.RelativeGroupLaw F p)
    {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (n : ℕ) :
    SchemeHomOver t (G.schemeKerStr n) ≃
      {z : SchemeHomOver t p // G.nsmul t n z = G.one t} := by
  have hone : (G.one t).val = t ≫ (G.one (𝟙 _)).val := by
    have h := G.one_natural (𝟙 _) t t (Category.comp_id _)
    exact (congrArg Subtype.val h).symm
  have hfst : pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).val ≫ p = G.schemeKerStr n := by
    have h := congrArg (fun f => f ≫ p) (pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 _)).val))
    simpa only [Category.assoc, G.schemeNsmul_over, (G.one (𝟙 _)).property, Category.comp_id] using h
  refine
    { toFun := fun w => ⟨⟨w.val ≫ pullback.fst _ _, ?_⟩, ?_⟩
      invFun := fun z => ⟨pullback.lift z.val.val t ?_, pullback.lift_snd _ _ _⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Category.assoc, hfst]
    exact w.property
  · apply Subtype.ext
    rw [← comp_schemeNsmul, Category.assoc, pullback.condition,
      ← Category.assoc, w.property, ← hone]
  · rw [comp_schemeNsmul, z.property, hone]
  · intro w
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans w.property.symm
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

open ArithmeticThetaCompactifiedDifferentialR0145 ArithmeticThetaMarkedGroupLawR0146

/-- The accepted coordinate equivalence identifies the kernel points with
actual Weierstrass torsion, including the identity. -/
def kernelTorsionEquiv (k : Type u) [Field k] [CharZero k] (r : ℕ)
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F] (n : ℕ) :
    SchemeHomOver (extensionBase k F) (G.schemeKerStr n) ≃
      Submodule.torsionBy ℤ ((curve k r).toProjective.baseChange F).toAffine.Point (n : ℤ) := by
  refine (kernelPointsEquiv G (extensionBase k F) n).trans
    (Equiv.subtypeEquiv (ev F) ?_)
  intro z
  rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  rw [← evaluation_nsmul k r G ev hev F z n, ← evaluation_one k r G ev hev F]
  exact (ev F).injective.eq_iff.symm

/-- The identity fiber has rank n², obtained by étale geometric-point counting. -/
lemma kernel_rank (k : Type u) [Field k] [CharZero k] (r : ℕ)
    (h3 : 3 ≤ r) (he : Even r)
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (n : ℕ) (hn : 0 < n) [IsFinite (G.schemeNsmul n)] [Etale (G.schemeNsmul n)] :
    ∀ z, (G.schemeKerStr n).finrank z = n^2 := by
  classical
  let F := AlgebraicClosure (LaurentSeries k)
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : CharZero F := Algebra.charZero_of_charZero (LaurentSeries k) F
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  letI : ((curve k r).toProjective.baseChange F).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange (curve k r)
  intro z
  have hz : z = (extensionBase k F) (IsLocalRing.closedPoint F) := Subsingleton.elim _ _
  have hcount := finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    (G.schemeKerStr n) F (algebraMap (LaurentSeries k) F)
  apply (congrArg (G.schemeKerStr n).finrank hz).trans
  apply hcount.trans
  exact (Nat.card_congr (kernelTorsionEquiv k r G ev hev F n)).trans
    (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      ((curve k r).toProjective.baseChange F).toAffine
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num))

#print axioms kernelPointsEquiv
#print axioms kernelTorsionEquiv
#print axioms kernel_rank
#print axioms etale_nsmul
#print axioms rank_from_identity
#print axioms transport_multiplication
end ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open MultiplicationFiniteEtaleDegree

/-- Multiplication by every positive integer on the actual algebraized generic
curve is finite étale and surjective, of rank exactly the square of that integer. -/
theorem multiplication_finite_etale_degree :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (n : ℕ), 0 < n → AlgebraicGeometry.IsFinite (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) ∧ AlgebraicGeometry.Etale (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) ∧ AlgebraicGeometry.Surjective (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) ∧ ∀ z : ArithmeticThetaGenericEvaluationR0140.genericScheme k M, AlgebraicGeometry.Scheme.Hom.finrank (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) z = n^2 := by
  intro k _ _ r hr h3 T he M hM s hs G hG n hn
  classical
  obtain ⟨X,hX,_⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y,hY,_⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a,ha,_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c,hc,_⟩ := projective_cubic_chart k r
  obtain ⟨E,hE,_⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  have hi : E.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hE.1, E.inv_hom_id_assoc]
  let H := transport E.symm hi G
  have hHo : (H.one (𝟙 _)).val = origin k r := by
    change (G.one (𝟙 _)).val ≫ E.hom = _
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hE.2.2
  have hHc : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of (LaurentSeries k)))
      (x y : SchemeHomOver t (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r)), H.mul t x y = H.mul t y x := by
    intro V t x y
    change (pointsEquiv E.symm hi t).symm (G.mul t _ _) =
      (pointsEquiv E.symm hi t).symm (G.mul t _ _)
    rw [hG.2]
  obtain ⟨ev,hev⟩ := projective_points_evaluation k r h3 he H hHo
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := CompactifiedCoordinateIsomorphism.projective_relative_one k h3 he
  letI := CompactifiedCoordinateIsomorphism.projective_proper k (r := r)
  letI := CompactifiedCoordinateIsomorphism.projective_integral k (r := r)
  letI : Etale (H.schemeNsmul n) := etale_nsmul H hHc n hn
  letI : IsProper (H.schemeNsmul n) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (H.schemeNsmul n) (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r) inferInstance
      (by rw [H.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (H.schemeNsmul n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  letI : IsFinite (H.schemeNsmul n) := .of_isProper_of_locallyQuasiFinite _
  have hrank : ∀ z, (H.schemeNsmul n).finrank z = n^2 :=
    rank_from_identity H n (n^2) (kernel_rank k r h3 he H ev hev n hn)
  have hconj : multiplication k M G n ≫ E.hom = E.hom ≫ H.schemeNsmul n :=
    transport_multiplication E hE.1 hi G n
  have hpb : IsPullback E.hom (multiplication k M G n) (H.schemeNsmul n) E.hom :=
    IsPullback.of_horiz_isIso ⟨hconj.symm⟩
  letI : IsFinite (multiplication k M G n) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  letI : Etale (multiplication k M G n) :=
    MorphismProperty.of_isPullback (P := @Etale) hpb inferInstance
  have hactual : ∀ z, (multiplication k M G n).finrank z = n^2 := by
    intro z
    exact (Scheme.Hom.finrank_of_isPullback E.hom _ _ E.hom hpb z).trans (hrank (E.hom z))
  refine ⟨inferInstance, inferInstance, ?_, hactual⟩
  apply (multiplication k M G n).one_le_finrank_iff_surjective.mp
  intro z
  rw [hactual z]
  exact Nat.one_le_pow 2 n hn

#print axioms multiplication_finite_etale_degree
end ArithmeticThetaHodgeFourTorsionR0147
