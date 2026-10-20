module

public import RelativeCyclicQuotientExistenceR0173
public import AlgebraizedMarkedIdealSpecializationR0136

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeIsogenyHodgeR0172 ArithmeticThetaRelativeKatoNaturalityR0170
namespace CyclicQuotientArbitraryBaseChangeR0173

lemma pointed_ext {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    {f g : PointedMap R W V} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

lemma cyclic_ext {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    {G : Law R W} {n : ℕ} {P Q : CyclicSection R W G n}
    (h : P.point = Q.point) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

lemma section_pullback {X Y B C : Scheme.{u}}
    {b : X ⟶ Y} {p : X ⟶ B} {q : Y ⟶ C} {a : B ⟶ C}
    (hb : IsPullback b p q a) (s : C ⟶ Y) (t : B ⟶ X)
    (hs : s ≫ q = 𝟙 _) (ht : t ≫ p = 𝟙 _) (he : t ≫ b = a ≫ s) :
    IsPullback t a b s := by
  have outer : IsPullback (t ≫ p) a a (s ≫ q) := by
    rw [ht, hs]
    exact IsPullback.id_horiz a
  exact outer.of_right he hb.flip

lemma section_closed {X B : Scheme.{u}} (p : X ⟶ B) [IsSeparated p]
    (s : B ⟶ X) (hs : s ≫ p = 𝟙 _) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ p) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s p

lemma union_kernel_pullback {X Y B C : Scheme.{u}} {n : ℕ}
    {b : X ⟶ Y} {p : X ⟶ B} {q : Y ⟶ C} {a : B ⟶ C}
    [IsSeparated q] (hb : IsPullback b p q a)
    (s : Fin n → (C ⟶ Y)) (t : Fin n → (B ⟶ X))
    (hs : ∀ i, s i ≫ q = 𝟙 _) (ht : ∀ i, t i ≫ p = 𝟙 _)
    (he : ∀ i, t i ≫ b = a ≫ s i)
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (s i)) (Set.range (s j))) :
    (⨅ i, (s i).ker).comap b = ⨅ i, (t i).ker := by
  have (i : Fin n) : IsClosedImmersion (s i) := section_closed q (s i) (hs i)
  have : IsClosedImmersion (Sigma.desc s) :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s hd
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : Fin n => C))
  have hp := hu.isPullback_of_isColimit_left s (Sigma.desc s) b t (fun _ => a)
    (fun i => section_pullback hb (s i) (t i) (hs i) (ht i) (he i))
    (coproductIsCoproduct (fun _ : Fin n => B))
  have heq : Cofan.IsColimit.desc
      (coproductIsCoproduct (fun _ : Fin n => B)) t = Sigma.desc t := by
    apply Sigma.hom_ext
    intro i
    exact (Cofan.IsColimit.fac _ _ i).trans (Sigma.ι_desc t i).symm
  rw [heq] at hp
  have : IsClosedImmersion (Sigma.desc t) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  simpa only [ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136.ker_sigma]
    using ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange hp

end CyclicQuotientArbitraryBaseChangeR0173
open CyclicQuotientArbitraryBaseChangeR0173
attribute [local irreducible] origin structureMap

/-- The marked generator and the quotient morphism commute uniquely with every
specified pointed Cartesian base change, including noninjective specialization. -/
theorem cyclic_quotient_arbitrary_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G n) (V : WeierstrassCurve R) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (hf : ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient R W G P f) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Vs : WeierstrassCurve S) [Vs.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (Hs : ArithmeticThetaRelativeKatoR0169.Law S Vs) (hHs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Vs Hs) (ι : R →+* S) (bW : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hbW : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι bW) (bV : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Vs) (ArithmeticThetaRelativeKatoR0169.Curve R V)) (hbV : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R V H S Vs Hs ι bV), ∃! Ps : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection S Ws Gs n, CategoryTheory.CategoryStruct.comp Ps.point bW = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) P.point ∧ ∃! fs : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap S Ws Vs, ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient S Ws Gs Ps fs ∧ CategoryTheory.CategoryStruct.comp fs.map bV = CategoryTheory.CategoryStruct.comp bW f.map := by
  intro R _ _ _ _ _ W _ G hG n hn P V _ H hH f hf
    S _ _ _ _ _ Ws _ Vs _ Gs hGs Hs hHs ι bW hbW bV hbV
  obtain ⟨hw, how, hmw⟩ := hbW
  obtain ⟨hv, hov, hmv⟩ := hbV
  let a := baseMap R S ι
  have ow : origin S Ws ≫ structureMap S Ws = 𝟙 _ :=
    by
    simpa only [origin, structureMap] using (WeierstrassProjModel.kwZeroSect S Ws).property
  have ov : origin S Vs ≫ structureMap S Vs = 𝟙 _ :=
    by
    simpa only [origin, structureMap] using (WeierstrassProjModel.kwZeroSect S Vs).property
  obtain ⟨s, hs, hso⟩ := hw.exists_lift (a ≫ P.point) (𝟙 _) (by
    rw [Category.assoc, P.over_eq, Category.comp_id, Category.id_comp]
    rfl)
  have hsm (j : ℕ) : (s ≫ Gs.schemeNsmul j) ≫ bW =
      a ≫ (P.point ≫ G.schemeNsmul j) := by
    rw [Category.assoc, hmw, ← Category.assoc, hs, Category.assoc]
  let Ps : CyclicSection S Ws Gs n := {
    point := s
    over_eq := hso
    killed := hw.hom_ext (by rw [hsm, P.killed]; exact how.symm)
      (by rw [Category.assoc, Gs.schemeNsmul_over, hso, ow])
    disjoint := by
      intro i j hij
      apply Set.disjoint_iff_forall_ne.mpr
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
      apply Set.disjoint_iff_forall_ne.mp (P.disjoint i j hij)
        (Set.mem_range_self (a x)) (Set.mem_range_self (a y))
      have he := congrArg (fun z => bW z) heq
      change ((s ≫ Gs.schemeNsmul i.val) ≫ bW) x =
        ((s ≫ Gs.schemeNsmul j.val) ≫ bW) y at he
      simpa only [hsm, Scheme.Hom.comp_apply] using he }
  obtain ⟨g, hg, hgo⟩ := hv.exists_lift (bW ≫ f.map) (structureMap S Ws) (by
    rw [Category.assoc, f.over_eq]; exact hw.w)
  have hgp : origin S Ws ≫ g = origin S Vs := by
    apply hv.hom_ext
    · rw [Category.assoc, hg, ← Category.assoc, how, Category.assoc,
        f.origin_eq]
      exact hov.symm
    · rw [Category.assoc, hgo, ow, ov]
  let fs : PointedMap S Ws Vs := ⟨g, hgo, hgp⟩
  have hcart : IsPullback bW g f.map bV := by
    have hh : IsPullback bW (g ≫ structureMap S Vs)
        (f.map ≫ structureMap R V) a := by
      rw [hgo, f.over_eq]
      exact hw
    exact hh.of_bot hg.symm hv
  letI : IsFinite f.map := hf.1
  letI : Etale f.map := hf.2.1
  letI : Surjective f.map := hf.2.2.1
  letI : IsFinite g := MorphismProperty.of_isPullback hcart inferInstance
  letI : Etale g := MorphismProperty.of_isPullback hcart inferInstance
  letI : Surjective g := MorphismProperty.of_isPullback hcart inferInstance
  letI : IsProper (structureMap R W) :=
    by simpa only [structureMap] using WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsProper (structureMap R V) :=
    by simpa only [structureMap] using WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  have hv0 : origin R V ≫ structureMap R V = 𝟙 _ :=
    by
    simpa only [origin, structureMap] using (WeierstrassProjModel.kwZeroSect R V).property
  letI : IsClosedImmersion (origin R V) := section_closed _ _ hv0
  have hk0 : (origin R V).ker.comap bV = (origin S Vs).ker :=
    ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange
      (section_pullback hv _ _ hv0 ov hov)
  have hkm : (kernelIdeal R W G P).comap bW = kernelIdeal S Ws Gs Ps := by
    apply union_kernel_pullback hw (multiple R W G P) (multiple S Ws Gs Ps)
    · intro i
      simp only [multiple, Category.assoc, G.schemeNsmul_over, P.over_eq]
    · intro i
      simp only [multiple, Category.assoc, Gs.schemeNsmul_over, Ps.over_eq]
    · intro i
      exact hsm i.val
    · exact P.disjoint
  have hq : IsQuotient S Ws Gs Ps fs := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · intro y
      exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hcart y).trans (hf.2.2.2.1 _)
    · change (origin S Vs).ker.comap g = _
      rw [← hk0, ← Scheme.IdealSheafData.comap_comp, hg,
        Scheme.IdealSheafData.comap_comp, hf.2.2.2.2, hkm]
  refine ⟨Ps, ⟨hs, fs, ⟨hq, hg⟩, ?_⟩, ?_⟩
  · intro fs' hfs'
    have he : fs'.map = fs.map := hv.hom_ext (hfs'.2.trans hg.symm)
      (fs'.over_eq.trans fs.over_eq.symm)
    exact pointed_ext he
  · intro Ps' hPs'
    have he : Ps'.point = Ps.point := hw.hom_ext (hPs'.1.trans hs.symm)
      (Ps'.over_eq.trans Ps.over_eq.symm)
    exact cyclic_ext he

#print axioms cyclic_quotient_arbitrary_base_change
end ArithmeticThetaRelativeCyclicQuotientR0173
