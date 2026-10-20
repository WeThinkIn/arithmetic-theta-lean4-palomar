module

public import HodgeFourTorsionDefinitionsR0147

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaAlgebraicCoordinatesR0143
/-! Actual chart factorization and full Tate values for nonidentity marked points.
All implementation helpers belong to this module's namespace. -/
namespace MarkedCoordinateChart
open CategoryTheory.Limits
/-- A closed field-valued section is determined, among sections of the same
structure map, by its underlying point. The nonempty pullback is a surjective
closed immersion into a reduced field spectrum, hence an isomorphism. -/
lemma field_section_ext {K : Type u} [Field K] {Z : Scheme.{u}}
    (f g : Spec (CommRingCat.of K) ⟶ Z) (t : Z ⟶ Spec (CommRingCat.of K))
    [IsClosedImmersion g] (hf : f ≫ t = 𝟙 _) (hg : g ≫ t = 𝟙 _)
    (x : Spec (CommRingCat.of K)) (h : f x = g x) : f = g := by
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x x h
  letI : Surjective (pullback.fst f g) := ⟨fun y => ⟨z, hz.trans (Subsingleton.elim x y)⟩⟩
  letI : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  have hp : pullback.fst f g = pullback.snd f g := by
    have hh := congrArg (fun a => a ≫ t) (pullback.condition (f := f) (g := g))
    simpa only [Category.assoc, hf, hg, Category.comp_id] using hh
  apply (cancel_epi (pullback.fst f g)).mp
  rw [pullback.condition, hp]
open MonoidalCategory
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
local instance pulled_isIso {C D : Scheme.{u}} (f : D ⟶ C) {L : C.Modules}
    (j : L ⟶ (𝟙_ C.Modules)) [IsIso j] : IsIso (pulledInclusion f j) := by
  letI := unitPullback_isIso f
  unfold pulledInclusion
  infer_instance
/-- Regular evaluation commutes with the actual pullback comparison for a
commuting square, with the ideal inclusions providing the trivializations. -/
lemma square_regularValue {A B C D : Scheme.{u}} (f : A ⟶ B) (a : C ⟶ A)
    (b : D ⟶ B) (g : C ⟶ D) (h : a ≫ f = g ≫ b)
    {L : B.Modules} (j q : L ⟶ (𝟙_ B.Modules))
    [IsIso (pulledInclusion f j)] [IsIso (pulledInclusion b j)] :
    a.appTop (regularValue (pulledInclusion f j) (pulledInclusion f q)) =
    g.appTop (regularValue (pulledInclusion b j) (pulledInclusion b q)) := by
  have hj := squareIso_inclusion f a b g h L j
  have hq := squareIso_inclusion f a b g h L q
  have hv := regularValue_precomp (squareIso f a b g h L)
    (pulledInclusion a (pulledInclusion f j)) (pulledInclusion a (pulledInclusion f q))
  simp only [hj, hq] at hv
  simpa only [regularValue_pull] using hv.symm
end MarkedCoordinateChart

open MarkedCoordinateChart
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

/-- Every nonidentity actual mark factors through the specified affine chart,
where the coordinate ring homomorphism evaluates to the complete Tate series. -/
theorem marked_coordinate_chart :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
      (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
      ∀ (X : Dual k M s 2) (Y : Dual k M s 3), RealizesCoordinate k false M s X →
      RealizesCoordinate k true M s Y → ∀ (a : complementScheme k M s ≅ cubicScheme k r),
      IsCoordinateIso k M s X Y a → ∀ (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))),
      IsChartIso k r c → ∀ (e : genericScheme k M ≅ projectiveCurve k r),
      IsCompactificationIso k M s hs.1 a c e → ∀ (i : Fin r) (b : kˣ)
      (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i b p),
      (i.val ≠ 0 ∨ (b : k) ≠ 1) →
      HasCoordinates k M e (pointOver k M (𝟙 _) p hp.1)
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val (b : k)))
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val (b : k))) := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY a ha c hc e hec i b p hp hne
  have hna : i.val = 0 → (b : k) ≠ 1 := fun hi => hne.resolve_left (not_not_intro hi)
  have hmem : ∀ x, genericPoint k M p hp.1 x ∈ complement k M s := by
    intro x hn
    change genericPoint k M p hp.1 x ∈ (s.ker.comap (genericInclusion k M)).support at hn
    have hn := (GenericAffineCubicIsomorphismR0144.generic_identity_support_singleton k M hM s hs.1 x).le hn
    have hcl := GenericAffineCubicIsomorphismR0144.genericPoint_closed k M hM s hs.1
    letI := hcl
    have heq := MarkedCoordinateChart.field_section_ext (genericPoint k M p hp.1)
      (genericPoint k M s hs.1) (genericStructure k M)
      (by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericStructure]) (by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericStructure]) x hn
    have hl := MarkedExactTorsion.labels_eq k M hM p s hp hs
      (show pointOver k M (𝟙 _) p hp.1 = pointOver k M (𝟙 _) s hs.1 by
        apply Subtype.ext
        simpa only [pointOver, Category.id_comp] using heq)
    exact hna (congrArg Fin.val hl.1) (by simpa [hl.2])
  let l : Spec (CommRingCat.of (LaurentSeries k)) ⟶ complementScheme k M s :=
    IsOpenImmersion.lift (complement k M s).ι (genericPoint k M p hp.1) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨_, hmem x⟩, rfl⟩)
  have hl : l ≫ (complement k M s).ι = genericPoint k M p hp.1 :=
    IsOpenImmersion.lift_fac _ _ _
  have hlm : l ≫ complementInclusion k M s = genericBase k ≫ p := by
    rw [complementInclusion, ← Category.assoc, hl, genericPoint_inclusion]
  let χ : ChartRing k r →+* LaurentSeries k := (Spec.preimage (l ≫ a.hom ≫ c.hom)).hom
  have hχ : Spec.map (CommRingCat.ofHom χ) = l ≫ a.hom ≫ c.hom := Spec.map_preimage _
  have hv (odd : Bool) :
      χ (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
         else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (if odd then ArithmeticThetaTateSeries.tateY r i.val (b : k)
         else ArithmeticThetaTateSeries.tateX r i.val (b : k)) := by
    let φ : Dual k M s (degree odd) := match odd with | true => Y | false => X
    have hφ : RealizesCoordinate k odd M s φ := by cases odd <;> assumption
    have hev := coordinate_marked_evaluation k r hr h3 T M hM s hs odd φ hφ i b hna p hp
    letI : IsIso (pulledInclusion p (idealInclusion (s.ker ^ degree odd))) := hev.1
    letI : IsIso (pulledInclusion (complementInclusion k M s)
      (idealInclusion (s.ker ^ degree odd))) := (ha.2 odd).1
    have hcval : regularValue
        (pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker ^ degree odd)))
        (pulledInclusion (complementInclusion k M s) φ) =
        a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
          (cubicCoordinate k r odd)) := by
      have hh := (ha.2 odd).2 ⊤
        ((inv (pulledInclusion (complementInclusion k M s)
          (idealInclusion (s.ker ^ degree odd)))).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))
      change regularValue (pulledInclusion (complementInclusion k M s)
        (idealInclusion (s.ker ^ degree odd))) (pulledInclusion (complementInclusion k M s) φ) =
        _ * (show Γ(complementScheme k M s, ⊤) from
          (pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker ^ degree odd))).app ⊤
            ((inv (pulledInclusion (complementInclusion k M s)
              (idealInclusion (s.ker ^ degree odd)))).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))) at hh
      rw [inverse_inclusion_one, mul_one] at hh
      simpa using hh
    have hpval : regularValue (pulledInclusion p (idealInclusion (s.ker ^ degree odd)))
        (pulledInclusion p φ) = (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv
          (if odd then ArithmeticThetaTateSeries.tateY r i.val (b : k)
           else ArithmeticThetaTateSeries.tateX r i.val (b : k)) := by
      have hh := hev.2 ⊤ ((inv (pulledInclusion p
        (idealInclusion (s.ker ^ degree odd)))).app ⊤ (1 : Γ(baseScheme k, ⊤)))
      change regularValue (pulledInclusion p (idealInclusion (s.ker ^ degree odd)))
        (pulledInclusion p φ) = _ * (show Γ(baseScheme k, ⊤) from
          (pulledInclusion p (idealInclusion (s.ker ^ degree odd))).app ⊤
            ((inv (pulledInclusion p (idealInclusion (s.ker ^ degree odd)))).app ⊤
              (1 : Γ(baseScheme k, ⊤)))) at hh
      rw [inverse_inclusion_one, mul_one] at hh
      simpa [baseScalar] using hh
    have hsquare := square_regularValue (complementInclusion k M s) l p (genericBase k)
      hlm (idealInclusion (s.ker ^ degree odd)) φ
    rw [hcval, hpval] at hsquare
    apply (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom.injective
    have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom χ))
      (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
       else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)
    rw [hχ] at hnat
    have hbval := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))))
      (if odd then ArithmeticThetaTateSeries.tateY r i.val (b : k)
       else ArithmeticThetaTateSeries.tateX r i.val (b : k))
    calc
      _ = (l ≫ a.hom ≫ c.hom).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv _) := hnat
      _ = l.appTop (a.hom.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv (cubicCoordinate k r odd))) := by
        simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hc.2 odd]
      _ = _ := hsquare
      _ = _ := hbval.symm
  refine ⟨χ, ?_, hv false, hv true⟩
  change (𝟙 _ ≫ genericPoint k M p hp.1) ≫ e.hom = _
  rw [Category.id_comp, hχ, ← hl]
  simp only [Category.assoc, hec.2.1]

end ArithmeticThetaHodgeFourTorsionR0147

#print axioms ArithmeticThetaHodgeFourTorsionR0147.marked_coordinate_chart
