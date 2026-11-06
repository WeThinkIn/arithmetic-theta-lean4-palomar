module

public import SchemeTorsionCartesianR0250
public import SchemeDiscriminantExistenceR0244
public import ArbitraryKatoUnitNaturalityR0249
public import ArbitraryKatoUnitExistenceR0249

@[expose] public section

/-! Descent of the complete affine Kato units on the actual torsion complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaSchemeKatoUnitR0250
namespace SchemeKatoUnitExistence
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence
open ArithmeticThetaRelativeKatoR0169
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic AffineNeighborhood.commRing

lemma weierstrass_multiplication (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (n : ℕ) :
    multiplication (weierstrassFamily R W G hG) n = G.schemeNsmul n := by
  have hn {T : Scheme.{u}} (t : T ⟶ Base R)
      (x : NeronModelInfra.SchemeHomOver t (structureMap R W)) :
      ArithmeticThetaSchemeLevelR0204.multiple (weierstrassFamily R W G hG) t n x =
        G.nsmul t n x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change G.mul t _ x = G.mul t _ x
      rw [ih]
      rfl
  exact congrArg Subtype.val (hn (structureMap R W) _)

lemma weierstrass_complement (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (n : ℕ) :
    complement (weierstrassFamily R W G hG) n =
      ArithmeticThetaArbitraryKatoUnitR0249.complement R W G n := by
  unfold complement torsionIdeal identityIdeal
  rw [weierstrass_zero, weierstrass_multiplication]
  rfl

lemma test_complement {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S)
    (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    {b : Base R ⟶ S} (C : Comparison E (weierstrassFamily R W G hG) b) (n : ℕ) :
    ArithmeticThetaArbitraryKatoUnitR0249.complement R W G n =
      C.map ⁻¹ᵁ complement E n := by
  rw [← weierstrass_complement R W G hG]
  exact (scheme_torsion_cartesian k S σ E _ (b ≫ σ) _ b rfl C n).2.2.2

lemma comparison_open {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) [IsOpenImmersion b] :
    IsOpenImmersion C.map := by
  exact MorphismProperty.of_isPullback C.cartesian.flip inferInstance

lemma comparison_range {S T : Scheme.{u}} {E : Family S} {F : Family T}
    {b : T ⟶ S} (C : Comparison E F b) :
    Set.range C.map = E.p ⁻¹' Set.range b := by
  have hs : Function.Surjective C.cartesian.isoPullback.hom :=
    (Scheme.Hom.homeomorph C.cartesian.isoPullback.hom).surjective
  rw [← C.cartesian.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hs.range_eq, Set.image_univ]
  exact Scheme.Pullback.range_fst E.p b

lemma sections_eq_local {X : Scheme.{u}} (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (_hx : x ∈ V) (e : V ≤ U),
      X.presheaf.map (homOfLE e).op s = X.presheaf.map (homOfLE e).op t) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx t
  obtain ⟨V, hv, e, he⟩ := h x hx
  have H := congrArg (X.presheaf.germ V x hv) he
  simpa only [TopCat.Presheaf.germ_res_apply] using H

lemma restriction_eq_of_appLE_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (h : f ''ᵁ V ≤ U) (s t : Γ(Y, U))
    (he : f.appLE U V e s = f.appLE U V e t) :
    Y.presheaf.map (homOfLE h).op s = Y.presheaf.map (homOfLE h).op t := by
  have H := congrArg ((f.appIso V).inv) he
  simpa only [← CommRingCat.comp_apply, Scheme.Hom.appLE_appIso_inv] using H


section Affine
variable (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)

def affineUnit : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection R W G c :=
  (ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_existence R W G hG c hc hc6).choose

lemma affineUnit_normalized : ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit
    R W G c (affineUnit R W G hG c hc hc6) :=
  (ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_existence R W G hG c hc hc6).choose_spec.1

end Affine

section Charts
variable {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    {σ : S ⟶ Base k} {E : Family S}
    (P : LocalPresentation k S σ E)

local instance chartMap_open : IsOpenImmersion P.comparison := by
  letI := P.openImmersion
  exact comparison_open (chartComparison P)

local instance chartRat : Algebra ℚ P.ring :=
  ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra

def curveChart (c : ℕ) : E.curve.Opens :=
  P.comparison ''ᵁ ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c

lemma curveChart_le (c : ℕ) : curveChart P c ≤ complement E c := by
  rintro _ ⟨x, hx, rfl⟩
  exact (le_of_eq (test_complement σ E P.ring P.equation P.law P.originLaw
    (chartComparison P) c)) hx

lemma curveChart_eq (c : ℕ) :
    curveChart P c = E.p ⁻¹ᵁ chartImage P ⊓ complement E c := by
  unfold curveChart
  rw [test_complement σ E P.ring P.equation P.law P.originLaw (chartComparison P) c,
    ]
  change P.comparison ''ᵁ P.comparison ⁻¹ᵁ complement E c = _
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  congr 1
  apply TopologicalSpace.Opens.ext
  exact comparison_range (chartComparison P)

variable (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)

def chartUnit : (Γ(E.curve, curveChart P c))ˣ :=
  Units.map (P.comparison.appIso _).inv.hom.toMonoidHom
    (affineUnit P.ring P.equation P.law P.originLaw c hc hc6)

lemma chartUnit_pull :
    P.comparison.appLE (curveChart P c) _ (Scheme.Hom.preimage_image_eq P.comparison _).ge
      (chartUnit P c hc hc6 : Γ(E.curve, curveChart P c)) =
    (↑(affineUnit P.ring P.equation P.law P.originLaw c hc hc6) : Γ(Curve P.ring P.equation, ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c)) := by
  change P.comparison.appLE _ _ _ ((P.comparison.appIso _).inv _) = _
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.congr_hom (P.comparison.appIso _).inv_hom_id _

lemma chartUnit_test (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    {b : Base R ⟶ S} (C : Comparison E (weierstrassFamily R W G hG) b)
    (ι : P.ring →+* R) (hι : Spec.map (CommRingCat.ofHom ι) ≫ P.base = b) :
    ∃ e : ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c ≤
        C.map ⁻¹ᵁ curveChart P c,
      (affineUnit R W G hG c hc hc6 : Γ(Curve R W,
        ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c)) =
        C.map.appLE _ _ e (↑(chartUnit P c hc hc6) : Γ(E.curve, curveChart P c)) := by
  obtain ⟨B, hB⟩ := comparison_refinement (chartComparison P) C
    (Spec.map (CommRingCat.ofHom ι)) hι
  let ι' : P.ring →ₐ[ℚ] R := { ι with commutes' := ι.map_rat_algebraMap }
  obtain ⟨eB, hnat⟩ := ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_naturality
    P.ring P.equation P.law P.originLaw R W G hG ι'
    (hodgeComparison P.law P.originLaw G hG ι B) c hc hc6
    _ _ (affineUnit_normalized P.ring P.equation P.law P.originLaw c hc hc6)
    (affineUnit_normalized R W G hG c hc hc6)
  have eP := (Scheme.Hom.preimage_image_eq P.comparison
    (ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c)).ge
  have e : ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c ≤
      C.map ⁻¹ᵁ curveChart P c := by
    intro x hx
    refine ⟨B.map x, eB hx, ?_⟩
    exact congrArg (fun f => f x) hB
  refine ⟨e, ?_⟩
  have hh := Scheme.Hom.appLE_comp_appLE B.map P.comparison
    (curveChart P c) _ _ eP eB
  change B.map ≫ P.comparison = C.map at hB
  simp only [hB] at hh
  calc
    _ = B.map.appLE _ _ eB (↑(affineUnit P.ring P.equation P.law P.originLaw c hc hc6) : Γ(Curve P.ring P.equation, ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c)) := hnat
    _ = B.map.appLE _ _ eB
        (P.comparison.appLE _ _ eP (↑(chartUnit P c hc hc6) : Γ(E.curve, curveChart P c))) :=
      congrArg (fun z => B.map.appLE _ _ eB z) (chartUnit_pull P c hc hc6).symm
    _ = _ := ConcreteCategory.congr_hom hh _


/-- Compare the two complete sections on an overlap using smaller affine bases. -/
lemma chartUnit_overlap (Q : LocalPresentation k S σ E) :
    E.curve.presheaf.map (homOfLE (inf_le_left : curveChart P c ⊓ curveChart Q c ≤
      curveChart P c)).op (chartUnit P c hc hc6 : Γ(E.curve, curveChart P c)) =
    E.curve.presheaf.map (homOfLE (inf_le_right : curveChart P c ⊓ curveChart Q c ≤
      curveChart Q c)).op (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)) := by
  apply sections_eq_local
  intro x hx
  have hxP := hx.1
  have hxQ := hx.2
  rw [curveChart_eq] at hxP hxQ
  obtain ⟨y, hy⟩ := hxP.1
  have hyU : y ∈ P.base ⁻¹ᵁ chartImage Q := by
    change P.base y ∈ chartImage Q
    rw [hy]
    exact hxQ.1
  let N := Classical.choice (affine_neighborhood (Base P.ring)
    (P.base ⁻¹ᵁ chartImage Q) y hyU)
  letI := N.openImmersion
  letI := P.openImmersion
  let ρ : P.ring →+* N.ring := (Spec.preimage N.base).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = N.base := Spec.map_preimage N.base
  letI : Algebra ℚ N.ring := (ρ.comp (algebraMap ℚ P.ring)).toAlgebra
  obtain ⟨H, hH, ⟨B⟩⟩ := weierstrass_comparison_base_change P.equation P.law P.originLaw ρ
  let Z := comparisonComp (chartComparison P) B
  let b := Spec.map (CommRingCat.ofHom ρ) ≫ P.base
  letI : IsOpenImmersion b := by dsimp [b]; rw [hρ]; infer_instance
  letI : IsOpenImmersion Z.map := comparison_open Z
  have hQ : Set.range b ⊆ chartImage Q := by
    rintro _ ⟨z, rfl⟩
    change P.base (Spec.map (CommRingCat.ofHom ρ) z) ∈ chartImage Q
    rw [hρ]
    exact N.inside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := factor_chart Q b hQ
  obtain ⟨eP, heP⟩ := chartUnit_test P c hc hc6 N.ring (P.equation.map ρ) H hH Z ρ rfl
  obtain ⟨eQ, heQ⟩ := chartUnit_test Q c hc hc6 N.ring (P.equation.map ρ) H hH Z τ hτ
  let V := ArithmeticThetaArbitraryKatoUnitR0249.complement N.ring (P.equation.map ρ) H c
  have e : V ≤ Z.map ⁻¹ᵁ (curveChart P c ⊓ curveChart Q c) :=
    fun z hz => ⟨eP hz, eQ hz⟩
  have himg : Z.map ''ᵁ V ≤ curveChart P c ⊓ curveChart Q c := by
    rintro _ ⟨z, hz, rfl⟩
    exact e hz
  have hxb : E.p x ∈ Set.range b := by
    obtain ⟨z, hz⟩ := N.contains
    refine ⟨z, ?_⟩
    change P.base (Spec.map (CommRingCat.ofHom ρ) z) = E.p x
    rw [hρ, hz, hy]
  obtain ⟨z, hz⟩ : x ∈ Set.range Z.map := by
    rw [comparison_range]
    exact hxb
  have hzV : z ∈ V := by
    have hcomp := test_complement σ E N.ring (P.equation.map ρ) H hH Z c
    apply hcomp.ge
    change Z.map z ∈ complement E c
    rw [hz]
    exact hxP.2
  refine ⟨Z.map ''ᵁ V, ⟨z, hzV, hz⟩, himg, ?_⟩
  apply restriction_eq_of_appLE_eq Z.map _ V e himg
  simpa only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using heP.symm.trans heQ

lemma glue_chart_units :
    ∃ v : UnitSection E c, ∀ Q : LocalPresentation k S σ E,
      E.curve.presheaf.map (homOfLE (curveChart_le Q c)).op (v : Γ(E.curve, complement E c)) =
        (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)) := by
  classical
  have hcover : complement E c ≤ ⨆ Q : LocalPresentation k S σ E, curveChart Q c := by
    intro x hx
    obtain ⟨Q, hQ⟩ := chart_cover (k := k) (σ := σ) (E := E) (E.p x)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨Q, (curveChart_eq Q c).symm ▸ (show x ∈ E.p ⁻¹ᵁ chartImage Q ⊓ complement E c from ⟨hQ, hx⟩)⟩
  obtain ⟨s, hs, _⟩ := E.curve.sheaf.existsUnique_gluing'
    (fun Q : LocalPresentation k S σ E => curveChart Q c) (complement E c)
    (fun Q => homOfLE (curveChart_le Q c)) hcover
    (fun Q => (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)))
    (fun Q Q' => chartUnit_overlap Q c hc hc6 Q')
  change ∀ Q, E.curve.presheaf.map (homOfLE (curveChart_le Q c)).op s =
    (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)) at hs
  have hu : IsUnit s := by
    apply E.curve.toRingedSpace.isUnit_of_isUnit_germ (complement E c) s
    intro x hx
    change IsUnit (E.curve.presheaf.germ (complement E c) x hx s)
    obtain ⟨Q, hQ⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hx)
    have H := (chartUnit Q c hc hc6).isUnit.map (E.curve.presheaf.germ (curveChart Q c) x hQ).hom
    rw [← hs Q] at H
    change IsUnit (E.curve.presheaf.germ (curveChart Q c) x hQ
      (E.curve.presheaf.map (homOfLE (curveChart_le Q c)).op s)) at H
    simpa only [TopCat.Presheaf.germ_res_apply] using H
  refine ⟨hu.unit, ?_⟩
  intro Q
  rw [hu.unit_spec]
  exact hs Q

end Charts


/-- Every affine test is checked on a covering refinement of its own base. -/
lemma glued_unit_test {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    {σ : S ⟶ Base k} {E : Family S}
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (v : UnitSection E c)
    (hv : ∀ Q : LocalPresentation k S σ E,
      E.curve.presheaf.map (homOfLE (curveChart_le Q c)).op (v : Γ(E.curve, complement E c)) =
        (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)))
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    {b : Base R ⟶ S} (C : Comparison E (weierstrassFamily R W G hG) b) :
    ∃ e : ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c ≤
        C.map ⁻¹ᵁ complement E c,
      (affineUnit R W G hG c hc hc6 : Γ(Curve R W,
        ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c)) =
        C.map.appLE _ _ e (v : Γ(E.curve, complement E c)) := by
  have eC := (test_complement σ E R W G hG C c).le
  refine ⟨eC, ?_⟩
  apply sections_eq_local
  intro x hx
  obtain ⟨Q, hQ⟩ := chart_cover (k := k) (σ := σ) (E := E) (b (structureMap R W x))
  let N := Classical.choice (affine_neighborhood (Base R) (b ⁻¹ᵁ chartImage Q)
    (structureMap R W x) hQ)
  letI := N.openImmersion
  let ρ : R →+* N.ring := (Spec.preimage N.base).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = N.base := Spec.map_preimage N.base
  letI : Algebra ℚ N.ring := (ρ.comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨H, hH, ⟨B⟩⟩ := weierstrass_comparison_base_change W G hG ρ
  let a := Spec.map (CommRingCat.ofHom ρ)
  let Z := comparisonComp C B
  letI : IsOpenImmersion a := by dsimp [a]; rw [hρ]; infer_instance
  letI : IsOpenImmersion B.map := comparison_open B
  have hQ' : Set.range (a ≫ b) ⊆ chartImage Q := by
    rintro _ ⟨z, rfl⟩
    change b (Spec.map (CommRingCat.ofHom ρ) z) ∈ chartImage Q
    rw [hρ]
    exact N.inside ⟨z, rfl⟩
  obtain ⟨τ, hτ⟩ := factor_chart Q (a ≫ b) hQ'
  obtain ⟨eQ, heQ⟩ := chartUnit_test Q c hc hc6 N.ring (W.map ρ) H hH Z τ hτ
  let ρ' : R →ₐ[ℚ] N.ring := { ρ with commutes' := ρ.map_rat_algebraMap }
  obtain ⟨eB, heB⟩ := ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_naturality
    R W G hG N.ring (W.map ρ) H hH ρ' (hodgeComparison G hG H hH ρ B) c hc hc6
    _ _ (affineUnit_normalized R W G hG c hc hc6)
    (affineUnit_normalized N.ring (W.map ρ) H hH c hc hc6)
  let V := ArithmeticThetaArbitraryKatoUnitR0249.complement N.ring (W.map ρ) H c
  have himg : B.map ''ᵁ V ≤ ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c := by
    rintro _ ⟨z, hz, rfl⟩
    exact eB hz
  have hxa : structureMap R W x ∈ Set.range a := by
    simpa only [a, hρ] using N.contains
  obtain ⟨z, hz⟩ : x ∈ Set.range B.map := by
    rw [comparison_range]
    exact hxa
  have hzV : z ∈ V := by
    apply (ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitSpecialization.complement_eq
      (hodgeComparison G hG H hH ρ B) G hG H hH c).ge
    change B.map z ∈ ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c
    rw [hz]
    exact hx
  refine ⟨B.map ''ᵁ V, ⟨z, hzV, hz⟩, himg, ?_⟩
  apply restriction_eq_of_appLE_eq B.map _ V eB himg
  have hres := congrArg (fun s => Z.map.appLE _ _ eQ s) (hv Q)
  have hres' : Z.map.appLE (complement E c) V
      (eQ.trans (fun z hz => curveChart_le Q c hz)) (v : Γ(E.curve, complement E c)) =
      Z.map.appLE (curveChart Q c) V eQ
        (chartUnit Q c hc hc6 : Γ(E.curve, curveChart Q c)) := by
    simpa only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using hres
  have hcomp := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE B.map C.map (complement E c)
      (ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c) V eC eB)
    (v : Γ(E.curve, complement E c))
  exact heB.symm.trans (heQ.trans (hres'.symm.trans hcomp.symm))

end SchemeKatoUnitExistence

open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203

/-- Existence of the canonical full unit, normalized under every affine test. -/
theorem scheme_kato_unit_existence :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∃ v : UnitSection E c, IsKatoUnit E k σ c v := by
  intro k _ _ S σ E c hc hc6
  obtain ⟨v, hv⟩ := SchemeKatoUnitExistence.glue_chart_units (σ := σ) (E := E) c hc hc6
  refine ⟨v, ?_⟩
  intro R _ _ W _ G hG b _ C
  letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  exact ⟨SchemeKatoUnitExistence.affineUnit R W G hG c hc hc6,
    SchemeKatoUnitExistence.affineUnit_normalized R W G hG c hc hc6,
    SchemeKatoUnitExistence.glued_unit_test c hc hc6 v hv R W G hG C⟩

#print axioms scheme_kato_unit_existence
end ArithmeticThetaSchemeKatoUnitR0250
