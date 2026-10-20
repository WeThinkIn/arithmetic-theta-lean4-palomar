module

public import FullLevelCoverDefinitionsR0175

@[expose] public section

/-! Representability by the independent-pair locus in the actual torsion square. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
namespace Representability
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open WeierstrassProjModel
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
  (hG : IsOriginLaw R W G) (L : ℕ)

abbrev kernel : Scheme.{u} := equalizer (G.schemeNsmul L) (structureMap R W ≫ origin R W)
abbrev ki : kernel R W G L ⟶ Curve R W := equalizer.ι _ _
abbrev kp : kernel R W G L ⟶ Base R := ki R W G L ≫ structureMap R W

def kpoint : SchemeHomOver (kp R W G L) (structureMap R W) := ⟨ki R W G L, rfl⟩

include hG in
lemma kpoint_killed : G.nsmul (kp R W G L) L (kpoint R W G L) = G.one _ := by
  apply Subtype.ext
  rw [← comp_schemeNsmul, hG.1]
  exact (equalizer.condition _ _).trans (Category.assoc _ _ _).symm

abbrev pairs : Scheme.{u} := pullback (kp R W G L) (kp R W G L)
abbrev pp : pairs R W G L ⟶ Base R := pullback.fst _ _ ≫ kp R W G L

def px : SchemeHomOver (pp R W G L) (structureMap R W) :=
  WeierstrassProjModel.schemeHomOverComp (pullback.fst _ _) rfl (kpoint R W G L)
def py : SchemeHomOver (pp R W G L) (structureMap R W) :=
  WeierstrassProjModel.schemeHomOverComp (pullback.snd _ _) (pullback.condition.symm) (kpoint R W G L)

include hG in
lemma px_killed : G.nsmul (pp R W G L) L (px R W G L) = G.one _ :=
  G.isTorsionPoint_schemeHomOverComp _ _ _ rfl L (kpoint_killed R W G hG L)
include hG in
lemma py_killed : G.nsmul (pp R W G L) L (py R W G L) = G.one _ :=
  G.isTorsionPoint_schemeHomOverComp _ _ _ pullback.condition.symm L
    (kpoint_killed R W G hG L)

def klift {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (hx : G.nsmul t L x = G.one t) :
    T ⟶ kernel R W G L :=
  equalizer.lift x.val (by rw [comp_schemeNsmul, hx, hG.1, ← Category.assoc, x.property])

@[simp] lemma klift_ki {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (hx : G.nsmul t L x = G.one t) :
    klift R W G hG L t x hx ≫ ki R W G L = x.val := equalizer.lift_ι _ _
@[simp] lemma klift_kp {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (hx : G.nsmul t L x = G.one t) :
    klift R W G hG L t x hx ≫ kp R W G L = t := by
  rw [kp, ← Category.assoc, klift_ki, x.property]

def pairLift {T : Scheme.{u}} (t : T ⟶ Base R) (A : FullLevel R W G L t) :
    T ⟶ pairs R W G L :=
  pullback.lift (klift R W G hG L t A.x A.killed_x)
    (klift R W G hG L t A.y A.killed_y) (by simp)

@[simp] lemma pairLift_x {T : Scheme.{u}} (t : T ⟶ Base R) (A : FullLevel R W G L t) :
    pairLift R W G hG L t A ≫ (px R W G L).val = A.x.val := by
  simp [pairLift, px, WeierstrassProjModel.schemeHomOverComp, kpoint, ← Category.assoc]
@[simp] lemma pairLift_y {T : Scheme.{u}} (t : T ⟶ Base R) (A : FullLevel R W G L t) :
    pairLift R W G hG L t A ≫ (py R W G L).val = A.y.val := by
  simp [pairLift, py, WeierstrassProjModel.schemeHomOverComp, kpoint, ← Category.assoc]
@[simp] lemma pairLift_p {T : Scheme.{u}} (t : T ⟶ Base R) (A : FullLevel R W G L t) :
    pairLift R W G hG L t A ≫ pp R W G L = t := by
  simp only [pairLift, pp, ← Category.assoc, pullback.lift_fst, klift_ki, A.x.property]

lemma pairs_ext {T : Scheme.{u}} (a b : T ⟶ pairs R W G L)
    (hx : a ≫ (px R W G L).val = b ≫ (px R W G L).val)
    (hy : a ≫ (py R W G L).val = b ≫ (py R W G L).val) : a = b := by
  apply pullback.hom_ext
  · apply equalizer.hom_ext
    exact (Category.assoc _ _ _).trans (hx.trans (Category.assoc _ _ _).symm)
  · apply equalizer.hom_ext
    exact (Category.assoc _ _ _).trans (hy.trans (Category.assoc _ _ _).symm)

/-- Naturality of each actual linear combination, as an equality of scheme maps. -/
lemma combination_natural {T S : Scheme.{u}} (t : T ⟶ Base R) (s : S ⟶ Base R)
    (q : S ⟶ T) (hq : q ≫ t = s) (x y : SchemeHomOver t (structureMap R W))
    (i j : ℕ) :
    q ≫ (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val =
      (G.mul s (G.nsmul s i (WeierstrassProjModel.schemeHomOverComp q hq x))
        (G.nsmul s j (WeierstrassProjModel.schemeHomOverComp q hq y))).val := by
  exact congrArg Subtype.val ((G.mul_natural t s q hq _ _).trans
    (by rw [G.nsmul_natural, G.nsmul_natural]))


lemma combination_comp {T S : Scheme.{u}} (t : T ⟶ Base R) (s : S ⟶ Base R)
    (q : S ⟶ T) (hq : q ≫ t = s) (x y : SchemeHomOver t (structureMap R W))
    (a b : SchemeHomOver s (structureMap R W))
    (hx : q ≫ x.val = a.val) (hy : q ≫ y.val = b.val) (i j : ℕ) :
    q ≫ (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val =
      (G.mul s (G.nsmul s i a) (G.nsmul s j b)).val := by
  rw [combination_natural R W G t s q hq x y i j]
  · have ex : WeierstrassProjModel.schemeHomOverComp q hq x = a := Subtype.ext hx
    have ey : WeierstrassProjModel.schemeHomOverComp q hq y = b := Subtype.ext hy
    rw [ex, ey]

lemma origin_closed : IsClosed (Set.range (origin R W)) := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
  letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
  exact (origin R W).isClosedEmbedding.isClosed_range

abbrev indices (L : ℕ) := {ij : Fin L × Fin L // ij.1.val ≠ 0 ∨ ij.2.val ≠ 0}

def combination (i j : ℕ) : pairs R W G L ⟶ Curve R W :=
  (G.mul (pp R W G L) (G.nsmul _ i (px R W G L)) (G.nsmul _ j (py R W G L))).val

/-- The complement of all nonzero residue combinations meeting the identity. -/
def independentOpen : (pairs R W G L).Opens :=
  ⟨{z | ∀ ij : indices L, combination R W G L ij.val.1.val ij.val.2.val z ∉
      Set.range (origin R W)}, by
    have H := isOpen_iInter_of_finite fun ij : indices L =>
      (origin_closed R W).isOpen_compl.preimage
        (Scheme.Hom.continuous (combination R W G L ij.val.1.val ij.val.2.val))
    simpa only [Set.preimage, Set.mem_compl_iff, Set.iInter_ofPred] using H⟩

def level : LevelScheme R W G L where
  space := (independentOpen R W G L).toScheme
  projection := (independentOpen R W G L).ι ≫ pp R W G L
  level := {
    x := WeierstrassProjModel.schemeHomOverComp (independentOpen R W G L).ι rfl (px R W G L)
    y := WeierstrassProjModel.schemeHomOverComp (independentOpen R W G L).ι rfl (py R W G L)
    killed_x := G.isTorsionPoint_schemeHomOverComp _ _ _ rfl L (px_killed R W G hG L)
    killed_y := G.isTorsionPoint_schemeHomOverComp _ _ _ rfl L (py_killed R W G hG L)
    avoids := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro _ ⟨z, rfl⟩ hz
      have h := z.property ⟨(i,j), hij⟩
      apply h
      have hc := combination_natural R W G (pp R W G L)
        ((independentOpen R W G L).ι ≫ pp R W G L)
        (independentOpen R W G L).ι rfl (px R W G L) (py R W G L) i.val j.val
      rw [← hc] at hz
      exact hz }

lemma pairLift_mem {T : Scheme.{u}} (t : T ⟶ Base R) (A : FullLevel R W G L t)
    (z : T) : pairLift R W G hG L t A z ∈ independentOpen R W G L := by
  intro ij hz
  have hc := combination_comp R W G (pp R W G L) t (pairLift R W G hG L t A)
    (pairLift_p R W G hG L t A) (px R W G L) (py R W G L) A.x A.y
    (pairLift_x R W G hG L t A) (pairLift_y R W G hG L t A) ij.val.1.val ij.val.2.val
  apply Set.disjoint_left.mp (A.avoids ij.val.1 ij.val.2 ij.property) (Set.mem_range_self z)
  change (pairLift R W G hG L t A ≫ combination R W G L ij.val.1.val ij.val.2.val) z ∈
    Set.range (origin R W) at hz
  rw [combination, hc] at hz
  exact hz

include hG in
lemma represents : Represents R W G (level R W G hG L) := by
  intro T t A
  let U := independentOpen R W G L
  let a := pairLift R W G hG L t A
  have ha : Set.range a ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact pairLift_mem R W G hG L t A z
  let q := IsOpenImmersion.lift U.ι a ha
  have hq : q ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hp : q ≫ (level R W G hG L).projection = t := by
    change q ≫ U.ι ≫ pp R W G L = t
    rw [← Category.assoc, hq]
    exact pairLift_p R W G hG L t A
  refine ⟨⟨q,hp⟩, ⟨?_, ?_⟩, ?_⟩
  · change q ≫ U.ι ≫ (px R W G L).val = A.x.val
    rw [← Category.assoc, hq]
    exact pairLift_x R W G hG L t A
  · change q ≫ U.ι ≫ (py R W G L).val = A.y.val
    rw [← Category.assoc, hq]
    exact pairLift_y R W G hG L t A
  · intro b hb
    apply Subtype.ext
    apply (cancel_mono U.ι).mp
    rw [hq]
    apply pairs_ext R W G L
    · exact (Category.assoc _ _ _).trans (hb.1.trans (pairLift_x R W G hG L t A).symm)
    · exact (Category.assoc _ _ _).trans (hb.2.trans (pairLift_y R W G hG L t A).symm)


/-- The equalizer used above is the scheme-theoretic fiber of multiplication at zero. -/
lemma kernel_cartesian : IsPullback (ki R W G L) (kp R W G L)
    (G.schemeNsmul L) (origin R W) := by
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  have hc : ki R W G L ≫ G.schemeNsmul L = kp R W G L ≫ origin R W :=
    (equalizer.condition _ _).trans (Category.assoc _ _ _).symm
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hc
    (fun s => equalizer.lift s.fst (by
      rw [s.condition, ← Category.assoc]
      congr 1
      have H := congrArg (fun a => a ≫ structureMap R W) s.condition
      simpa only [Category.assoc, G.schemeNsmul_over,
        ho, Category.comp_id] using H.symm))
    (fun s => equalizer.lift_ι _ _) (fun s => ?_) (fun s m hm _ => ?_))
  · rw [kp, ← Category.assoc, equalizer.lift_ι]
    have H := congrArg (fun a => a ≫ structureMap R W) s.condition
    simpa only [Category.assoc, G.schemeNsmul_over,
      ho, Category.comp_id] using H
  · apply equalizer.hom_ext
    exact hm.trans (equalizer.lift_ι _ _).symm

variable [IsNoetherianRing R] [Algebra ℚ R] [W.IsElliptic]

include hG in
lemma multiplication_finite_etale (hL : 0 < L) :
    IsFinite (G.schemeNsmul L) ∧ Etale (G.schemeNsmul L) := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsLocallyNoetherian (Curve R W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap R W)
  have hunit : IsUnit (L : R) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)) : IsUnit (L : ℚ)).map
        (algebraMap ℚ R)
  letI : Etale (G.schemeNsmul L) := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ_schemeNsmul]
    exact ArithmeticThetaRelativeKatoR0169.RelativeMultiplicationDegree.etale_nsmul_relative
      (ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G) hG.2 L hunit
  letI : IsProper (G.schemeNsmul L) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (G.schemeNsmul L) (structureMap R W) inferInstance
      (by rw [G.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (G.schemeNsmul L) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, inferInstance⟩

include hG in
lemma kernel_finite_etale (hL : 0 < L) : IsFinite (kp R W G L) ∧ Etale (kp R W G L) := by
  obtain ⟨hf, he⟩ := multiplication_finite_etale R W G hG L hL
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (kernel_cartesian R W G L) hf,
    MorphismProperty.of_isPullback (P := @Etale) (kernel_cartesian R W G L) he⟩

include hG in
/-- Every linear combination of the universal torsion pair remains killed. -/
lemma combination_killed (i j : ℕ) : G.nsmul (pp R W G L) L
    (G.mul _ (G.nsmul _ i (px R W G L)) (G.nsmul _ j (py R W G L))) = G.one _ := by
  let t := pp R W G L
  letI : CommGroup (SchemeHomOver t (structureMap R W)) :=
    { G.pointGroup t with mul_comm := hG.2 t }
  have hn (n : ℕ) (x : SchemeHomOver t (structureMap R W)) : G.nsmul t n x = x ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih]; rfl
  have hx : (px R W G L) ^ L = 1 := (hn L _).symm.trans (px_killed R W G hG L)
  have hy : (py R W G L) ^ L = 1 := (hn L _).symm.trans (py_killed R W G hG L)
  change G.nsmul t L (G.mul t (G.nsmul t i _) (G.nsmul t j _)) = G.one t
  rw [hn, hn, hn]
  change ((px R W G L) ^ i * (py R W G L) ^ j) ^ L = 1
  rw [mul_pow, ← pow_mul, Nat.mul_comm i L, pow_mul, hx,
    ← pow_mul, Nat.mul_comm j L, pow_mul, hy, one_pow, one_pow, one_mul]

/-- The zero section inside the finite étale torsion scheme. -/
def zeroInKernel : Base R ⟶ kernel R W G L :=
  klift R W G hG L (𝟙 _) (G.one _) (G.nsmul_unit _ L)

@[simp] lemma zeroInKernel_ki : zeroInKernel R W G hG L ≫ ki R W G L = origin R W := by
  rw [zeroInKernel, klift_ki, hG.1, Category.id_comp]
@[simp] lemma zeroInKernel_kp : zeroInKernel R W G hG L ≫ kp R W G L = 𝟙 _ :=
  klift_kp R W G hG L _ _ _

/-- A section of an étale morphism is an open immersion. -/
lemma section_open {X S : Scheme.{u}} (p : X ⟶ S) [Etale p]
    (e : S ⟶ X) (he : e ≫ p = 𝟙 S) : IsOpenImmersion e := by
  letI : MorphismProperty.HasOfPostcompProperty
      @IsOpenImmersion (@LocallyOfFiniteType ⊓ @FormallyUnramified) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr (by
      intro X Y f ⟨hf, hu⟩
      letI := hf
      letI := hu
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f)))
  apply MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) e p ⟨inferInstance, inferInstance⟩
  rw [he]
  infer_instance

include hG in
lemma zeroInKernel_open (hL : 0 < L) : IsOpenImmersion (zeroInKernel R W G hG L) := by
  letI : Etale (kp R W G L) := (kernel_finite_etale R W G hG L hL).2
  exact section_open (kp R W G L) (zeroInKernel R W G hG L) (zeroInKernel_kp R W G hG L)

include hG in
lemma independent_clopen (hL : 0 < L) : IsClopen (independentOpen R W G L : Set (pairs R W G L)) := by
  refine ⟨?_, (independentOpen R W G L).isOpen⟩
  have hh (i j : ℕ) : IsClosed {z : pairs R W G L |
      combination R W G L i j z ∉ Set.range (origin R W)} := by
    let a := G.mul (pp R W G L) (G.nsmul _ i (px R W G L)) (G.nsmul _ j (py R W G L))
    let c := klift R W G hG L (pp R W G L) a (combination_killed R W G hG L i j)
    let e := zeroInKernel R W G hG L
    letI : IsOpenImmersion e := zeroInKernel_open R W G hG L hL
    have hi : IsClosedImmersion (ki R W G L) := by
      letI : IsProper (structureMap R W) :=
        WeierstrassProjModel.projModelStrCR_isProper W.toProjective
      have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect R W).property
      letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
      letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
      exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (kernel_cartesian R W G L).flip inferInstance
    letI := hi
    have heq : {z : pairs R W G L | combination R W G L i j z ∉ Set.range (origin R W)} =
        c ⁻¹' (Set.range e)ᶜ := by
      ext z
      apply not_congr
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, (ki R W G L).isClosedEmbedding.injective ?_⟩
        change (e ≫ ki R W G L) b = (c ≫ ki R W G L) z
        rw [show e ≫ ki R W G L = origin R W from zeroInKernel_ki R W G hG L,
          show c ≫ ki R W G L = a.val from klift_ki R W G hG L _ _ _]
        exact hb
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        have H := congrArg (ki R W G L) hb
        change (e ≫ ki R W G L) b = (c ≫ ki R W G L) z at H
        rw [show e ≫ ki R W G L = origin R W from zeroInKernel_ki R W G hG L,
          show c ≫ ki R W G L = a.val from klift_ki R W G hG L _ _ _] at H
        exact H
    rw [heq]
    exact (IsOpenImmersion.isOpen_range e).isClosed_compl.preimage c.continuous
  have H := isClosed_iInter fun ij : indices L => hh ij.val.1.val ij.val.2.val
  change IsClosed {z | ∀ ij : indices L, combination R W G L ij.val.1.val ij.val.2.val z ∉ Set.range (origin R W)}
  simpa only [Set.iInter_ofPred] using H


include hG in
/-- The representing object is the clopen independent locus in the actual finite torsion square. -/
lemma constructed_locus (hL : 0 < L) :
    Represents R W G (level R W G hG L) ∧
    IsClopen (independentOpen R W G L : Set (pairs R W G L)) ∧
    IsFinite (kp R W G L) ∧ Etale (kp R W G L) :=
  ⟨represents R W G hG L, independent_clopen R W G hG L hL,
    kernel_finite_etale R W G hG L hL⟩

end Representability
open AlgebraicGeometry ArithmeticThetaRelativeKatoR0169

/-- The relative full GL level-marking functor is represented on all test schemes. -/
theorem full_level_representability :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
  (hG : IsOriginLaw R W G) (L : ℕ) (hL : 0 < L),
  ∃ Z : LevelScheme R W G L, Represents R W G Z := by
  intro R _ _ _ _ _ W _ G hG L hL
  exact ⟨Representability.level R W G hG L, (Representability.constructed_locus R W G hG L hL).1⟩

#print axioms full_level_representability
end ArithmeticThetaFullLevelCoverR0175
