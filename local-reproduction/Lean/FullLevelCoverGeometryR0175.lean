import FullLevelRepresentabilityR0175
import FullLevelTorsionSplittingR0175
import Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
namespace CoverGeometryR0175
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171

section BasisCounting
variable {H : Type u} [AddCommGroup H] (L : ℕ) [NeZero L]

def BasisPair := {xy : H × H // ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
  i.val • xy.1 + j.val • xy.2 ≠ 0}

variable (hk : ∀ x : H, L • x = 0)

def residueHom (x : H) : ZMod L →+ H :=
  ZMod.lift L ⟨zmultiplesHom H x, by simpa using hk x⟩

lemma residueHom_val (x : H) (a : ZMod L) : residueHom L hk x a = a.val • x := by
  have h := ZMod.lift_coe L
    (⟨zmultiplesHom H x, by simpa using hk x⟩ : {f : ℤ →+ H // f L = 0}) (a.val : ℤ)
  simpa only [residueHom, Int.cast_natCast, ZMod.natCast_zmod_val, zmultiplesHom_apply,
    Nat.cast_smul_eq_nsmul] using h

def pairHom (x y : H) : (ZMod L × ZMod L) →+ H :=
  (residueHom L hk x).comp (AddMonoidHom.fst _ _) +
    (residueHom L hk y).comp (AddMonoidHom.snd _ _)

lemma pairHom_val (x y : H) (a : ZMod L × ZMod L) :
    pairHom L hk x y a = a.1.val • x + a.2.val • y := by
  change residueHom L hk x a.1 + residueHom L hk y a.2 = _
  rw [residueHom_val, residueHom_val]

@[simp] lemma pairHom_fst (x y : H) : pairHom L hk x y (1,0) = x := by
  have hh (z : H) : residueHom L hk z 1 = z := by
    simpa only [residueHom, Int.cast_one, zmultiplesHom_apply, one_zsmul] using
      (ZMod.lift_coe L (⟨zmultiplesHom H z, by simpa using hk z⟩ :
        {f : ℤ →+ H // f L = 0}) 1)
  simp [pairHom, hh]

@[simp] lemma pairHom_snd (x y : H) : pairHom L hk x y (0,1) = y := by
  have hh (z : H) : residueHom L hk z 1 = z := by
    simpa only [residueHom, Int.cast_one, zmultiplesHom_apply, one_zsmul] using
      (ZMod.lift_coe L (⟨zmultiplesHom H z, by simpa using hk z⟩ :
        {f : ℤ →+ H // f L = 0}) 1)
  simp [pairHom, hh]

lemma hom_by_generators (f : (ZMod L × ZMod L) →+ H) :
    pairHom L hk (f (1,0)) (f (0,1)) = f := by
  ext a
  rw [pairHom_val]
  rw [← f.map_nsmul, ← f.map_nsmul, ← f.map_add]
  congr 1
  ext <;> simp

lemma pairHom_injective (A : BasisPair (H := H) L) :
    Function.Injective (pairHom L hk A.val.1 A.val.2) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hz : a.1.val = 0 ∧ a.2.val = 0 := by
    by_contra h
    push Not at h
    exact A.property ⟨a.1.val,ZMod.val_lt _⟩ ⟨a.2.val,ZMod.val_lt _⟩
      (by tauto) ((pairHom_val L hk _ _ a).symm.trans ha)
  exact Prod.ext ((ZMod.val_eq_zero _).mp hz.1) ((ZMod.val_eq_zero _).mp hz.2)

include hk in
def equivPair (e : (ZMod L × ZMod L) ≃+ H) : BasisPair (H := H) L :=
  ⟨(e (1,0),e (0,1)), by
    intro i j hij he
    have h : e ((i.val : ZMod L),(j.val : ZMod L)) = 0 := by
      change e.toAddMonoidHom _ = _
      rw [← hom_by_generators L hk e.toAddMonoidHom, pairHom_val]
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using he
    have hz := e.injective (h.trans e.map_zero.symm)
    have hi : i.val = 0 := by
      have hh := congrArg (fun z : ZMod L × ZMod L => z.1.val) hz
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] using hh
    have hj : j.val = 0 := by
      have hh := congrArg (fun z : ZMod L × ZMod L => z.2.val) hz
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt] using hh
    exact hij.elim (fun h => h hi) (fun h => h hj)⟩

def basisPairEquiv [Finite H] (hc : Nat.card H = L^2) :
    BasisPair (H := H) L ≃ ((ZMod L × ZMod L) ≃+ H) where
  toFun A := AddEquiv.ofBijective (pairHom L hk A.val.1 A.val.2)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨pairHom_injective L hk A, by simp [hc, pow_two]⟩)
  invFun := equivPair L hk
  left_inv A := by
    apply Subtype.ext
    exact Prod.ext (pairHom_fst L hk _ _) (pairHom_snd L hk _ _)
  right_inv e := by
    apply AddEquiv.toAddMonoidHom_injective
    exact hom_by_generators L hk e.toAddMonoidHom

include hk in
lemma card_basisPair [Finite H] (hc : Nat.card H = L^2)
    (e : (ZMod L × ZMod L) ≃+ H) :
    Nat.card (BasisPair (H := H) L) = levelDegree L := by
  rw [Nat.card_congr (basisPairEquiv L hk hc)]
  exact Nat.card_congr {
    toFun := fun f => f.trans e.symm
    invFun := fun f => f.trans e
    left_inv := fun f => by ext a; simp
    right_inv := fun f => by
      apply AddEquiv.ext
      intro a
      exact e.symm_apply_apply (f a) }

end BasisCounting

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {G : Law R W} {L : ℕ}

lemma marking_ext {T : Scheme.{u}} {t : T ⟶ Base R} (A B : FullLevel R W G L t)
    (hx : A.x.val = B.x.val) (hy : A.y.val = B.y.val) : A = B := by
  have hx' : A.x = B.x := Subtype.ext hx
  have hy' : A.y = B.y := Subtype.ext hy
  cases A
  cases B
  cases hx'
  cases hy'
  rfl

lemma representing_ext (Z : LevelScheme R W G L) (hZ : Represents R W G Z)
    {T : Scheme.{u}} {t : T ⟶ Base R} (A : FullLevel R W G L t)
    (a b : SchemeHomOver t Z.projection)
    (ha : a.val ≫ Z.level.x.val = A.x.val ∧ a.val ≫ Z.level.y.val = A.y.val)
    (hb : b.val ≫ Z.level.x.val = A.x.val ∧ b.val ≫ Z.level.y.val = A.y.val) : a = b := by
  obtain ⟨q, _, hu⟩ := hZ T t A
  exact (hu a ha).trans (hu b hb).symm

/-- Pulling back the actual sections preserves the full marking condition. -/
def pullMark {T S : Scheme.{u}} {t : T ⟶ Base R} {s : S ⟶ Base R}
    (q : S ⟶ T) (hq : q ≫ t = s) (A : FullLevel R W G L t) :
    FullLevel R W G L s where
  x := WeierstrassProjModel.schemeHomOverComp q hq A.x
  y := WeierstrassProjModel.schemeHomOverComp q hq A.y
  killed_x := G.isTorsionPoint_schemeHomOverComp _ _ _ hq L A.killed_x
  killed_y := G.isTorsionPoint_schemeHomOverComp _ _ _ hq L A.killed_y
  avoids := by
    intro i j hij
    rw [← Representability.combination_natural R W G t s q hq]
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,rfl⟩ hz
    exact Set.disjoint_left.mp (A.avoids i j hij) ⟨q z,rfl⟩ hz

/-- Representability identifies actual sections of the cover with markings. -/
def sectionsEquiv (Z : LevelScheme R W G L) (hZ : Represents R W G Z)
    {T : Scheme.{u}} (t : T ⟶ Base R) :
    SchemeHomOver t Z.projection ≃ FullLevel R W G L t where
  toFun q := pullMark q.val q.property Z.level
  invFun A := (hZ T t A).choose
  left_inv q := representing_ext Z hZ (pullMark q.val q.property Z.level)
    _ q (hZ T t _).choose_spec.1 ⟨rfl,rfl⟩
  right_inv A := marking_ext _ _ (hZ T t A).choose_spec.1.1 (hZ T t A).choose_spec.1.2

/-- A field point meets the origin precisely when it is the identity section.
The proof uses the actual closed immersion of the origin. -/
lemma field_avoids_iff (hG : IsOriginLaw R W G) {K : Type u} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) :
    Disjoint (Set.range x.val) (Set.range (origin R W)) ↔ x ≠ G.one t := by
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W) := by
    letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
    exact IsClosedImmersion.of_comp _ (structureMap R W)
  constructor
  · intro hd he
    have hx : x.val = t ≫ origin R W := (congrArg Subtype.val he).trans (hG.1 t)
    exact Set.disjoint_left.mp hd ⟨IsLocalRing.closedPoint K,rfl⟩
      ⟨t (IsLocalRing.closedPoint K), congrArg (fun f => f (IsLocalRing.closedPoint K)) hx.symm⟩
  · intro hn
    by_contra hd
    have hne : Nonempty ↥(pullback x.val (origin R W)) :=
      not_isEmpty_iff.mp (fun h => hd (Scheme.isEmpty_pullback_iff.mp h))
    let p := pullback.fst x.val (origin R W)
    let q := pullback.snd x.val (origin R W)
    letI := hne
    letI : Surjective p := ⟨Function.surjective_to_subsingleton p⟩
    letI : IsIso p := isIso_of_isClosedImmersion_of_surjective p
    have hc : p ≫ x.val = q ≫ origin R W := pullback.condition
    have ht : p ≫ t = q := by
      have hh := congrArg (fun f => f ≫ structureMap R W) hc
      simpa only [Category.assoc, x.property, ho, Category.comp_id] using hh
    apply hn
    apply Subtype.ext
    apply (cancel_epi p).mp
    rw [hG.1, ← Category.assoc, ht]
    exact hc

/-- Uniqueness over the original base, retaining both universal section maps. -/
lemma representing_iso (Z D : LevelScheme R W G L)
    (hZ : Represents R W G Z) (hD : Represents R W G D) :
    ∃ e : Z.space ≅ D.space, e.hom ≫ D.projection = Z.projection ∧
      e.hom ≫ D.level.x.val = Z.level.x.val ∧
      e.hom ≫ D.level.y.val = Z.level.y.val := by
  obtain ⟨a, ha, _⟩ := hD Z.space Z.projection Z.level
  obtain ⟨b, hb, _⟩ := hZ D.space D.projection D.level
  have hab : a.val ≫ b.val = 𝟙 Z.space := by
    have hp : (a.val ≫ b.val) ≫ Z.projection = Z.projection := by
      rw [Category.assoc, b.property, a.property]
    exact congrArg Subtype.val (representing_ext Z hZ Z.level ⟨_,hp⟩
      ⟨𝟙 _, Category.id_comp _⟩
      ⟨by dsimp; rw [Category.assoc, hb.1, ha.1],
        by dsimp; rw [Category.assoc, hb.2, ha.2]⟩
      ⟨Category.id_comp _, Category.id_comp _⟩)
  have hba : b.val ≫ a.val = 𝟙 D.space := by
    have hp : (b.val ≫ a.val) ≫ D.projection = D.projection := by
      rw [Category.assoc, a.property, b.property]
    exact congrArg Subtype.val (representing_ext D hD D.level ⟨_,hp⟩
      ⟨𝟙 _, Category.id_comp _⟩
      ⟨by dsimp; rw [Category.assoc, ha.1, hb.1],
        by dsimp; rw [Category.assoc, ha.2, hb.2]⟩
      ⟨Category.id_comp _, Category.id_comp _⟩)
  exact ⟨⟨a.val,b.val,hab,hba⟩, a.property, ha⟩

section FieldMarkings
variable (hG : IsOriginLaw R W G) {K : Type u} [Field K]
  (t : Spec (CommRingCat.of K) ⟶ Base R)
  {E : Type u} [AddCommGroup E]
  (ev : SchemeHomOver t (structureMap R W) ≃ E)
  (hm : ∀ x y, ev (G.mul t x y) = ev x + ev y)
  (hz : ev (G.one t) = 0)

include hm hz in
lemma eval_nsmul (x : SchemeHomOver t (structureMap R W)) (n : ℕ) :
    ev (G.nsmul t n x) = n • ev x := by
  induction n with
  | zero => simpa only [G.nsmul_zero, zero_smul] using hz
  | succ n ih => rw [G.nsmul_succ, hm, ih, succ_nsmul]

include hm hz in
lemma eval_torsion (x : SchemeHomOver t (structureMap R W)) :
    G.nsmul t L x = G.one t ↔ ev x ∈ Submodule.torsionBy ℤ E (L : ℤ) := by
  rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  constructor
  · intro h
    rw [← eval_nsmul t ev hm hz, h, hz]
  · intro h
    apply ev.injective
    rw [eval_nsmul t ev hm hz, h, hz]

include hG hm hz in
lemma eval_avoids (x y : SchemeHomOver t (structureMap R W)) (i j : ℕ) :
    Disjoint (Set.range (G.mul t (G.nsmul t i x) (G.nsmul t j y)).val)
      (Set.range (origin R W)) ↔ i • ev x + j • ev y ≠ 0 := by
  rw [field_avoids_iff hG]
  have hh : ev (G.mul t (G.nsmul t i x) (G.nsmul t j y)) = ev (G.one t) ↔
      G.mul t (G.nsmul t i x) (G.nsmul t j y) = G.one t := ev.injective.eq_iff
  simpa only [hm, eval_nsmul t ev hm hz, hz] using hh.not.symm

variable (L) [NeZero L]

def fieldMarkToPair (A : FullLevel R W G L t) :
    BasisPair (H := Submodule.torsionBy ℤ E (L : ℤ)) L :=
  ⟨(⟨ev A.x, (eval_torsion t ev hm hz _).mp A.killed_x⟩,
    ⟨ev A.y, (eval_torsion t ev hm hz _).mp A.killed_y⟩), by
    intro i j hij h
    have hc := congrArg (fun z : Submodule.torsionBy ℤ E (L : ℤ) => (z : E)) h
    exact (eval_avoids hG t ev hm hz A.x A.y i.val j.val).mp (A.avoids i j hij) hc⟩

def fieldPairToMark (A : BasisPair (H := Submodule.torsionBy ℤ E (L : ℤ)) L) :
    FullLevel R W G L t where
  x := ev.symm A.val.1.val
  y := ev.symm A.val.2.val
  killed_x := (eval_torsion t ev hm hz _).mpr (by simp)
  killed_y := (eval_torsion t ev hm hz _).mpr (by simp)
  avoids := by
    intro i j hij
    apply (eval_avoids hG t ev hm hz _ _ i.val j.val).mpr
    simp only [Equiv.apply_symm_apply]
    intro h
    exact A.property i j hij (Subtype.ext h)

def fieldMarkEquiv : FullLevel R W G L t ≃
    BasisPair (H := Submodule.torsionBy ℤ E (L : ℤ)) L where
  toFun := fieldMarkToPair (L := L) (hG := hG) (t := t) (ev := ev) (hm := hm) (hz := hz)
  invFun := fieldPairToMark (L := L) (hG := hG) (t := t) (ev := ev) (hm := hm) (hz := hz)
  left_inv A := by
    apply marking_ext <;> simp [fieldMarkToPair, fieldPairToMark]
  right_inv A := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp [fieldMarkToPair, fieldPairToMark]

end FieldMarkings

variable (R W G) [IsNoetherianRing R] [Algebra ℚ R] [W.IsElliptic]
  (hG : IsOriginLaw R W G) (L : ℕ) (hL : 0 < L)

include hL in
lemma constructed_finite_etale :
    IsFinite (Representability.level R W G hG L).projection ∧
    Etale (Representability.level R W G hG L).projection := by
  obtain ⟨hf,he⟩ := Representability.kernel_finite_etale R W G hG L hL
  letI := hf
  letI := he
  let U := Representability.independentOpen R W G L
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact (Representability.independent_clopen R W G hG L hL).1)
  change IsFinite (U.ι ≫ Representability.pp R W G L) ∧
    Etale (U.ι ≫ Representability.pp R W G L)
  have hf' : IsFinite (Representability.pp R W G L) := by
    dsimp [Representability.pp]; infer_instance
  have he' : Etale (Representability.pp R W G L) := by
    dsimp [Representability.pp]; infer_instance
  letI := hf'
  letI := he'
  exact ⟨inferInstance, inferInstance⟩

include hG hL in
lemma representing_finite_etale (Z : LevelScheme R W G L) (hZ : Represents R W G Z) :
    IsFinite Z.projection ∧ Etale Z.projection := by
  obtain ⟨e,hp,_,_⟩ := representing_iso Z (Representability.level R W G hG L)
    hZ (Representability.represents R W G hG L)
  obtain ⟨hf,he⟩ := constructed_finite_etale R W G hG L hL
  letI := hf
  letI := he
  rw [← hp]
  exact ⟨inferInstance, inferInstance⟩

variable [IsDomain R]

include hG hL in
/-- The basis condition labels every point of the actual torsion subscheme.
This is obtained from the accepted scheme-theoretic splitting, including its
component equations; no replacement abstract torsion carrier is introduced. -/
lemma torsion_support_eq_marked_union [IsIntegrallyClosed R]
    (A : FullLevel R W G L (𝟙 (Base R))) :
    (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G L).support =
      ⋃ i : Fin L, ⋃ j : Fin L, Set.range (coordinatePoint R W G A i j) := by
  obtain ⟨e, _, he⟩ := full_level_torsion_splitting R W G hG L hL A
  let I := ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G L
  rw [← I.range_subschemeι]
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨⟨⟨i,j⟩,b⟩,hb⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin L × Fin L => R)).surjective (e.hom a)
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, ⟨b, ?_⟩⟩⟩
    rw [← he i j]
    change I.subschemeι (e.inv (torsionComponent R L i j b)) = I.subschemeι a
    change torsionComponent R L i j b = e.hom a at hb
    rw [hb]
    have hh := congrArg (fun f : I.subscheme ⟶ I.subscheme => f a) e.hom_inv_id
    exact congrArg I.subschemeι hh
  · intro hz
    obtain ⟨i,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j,b,rfl⟩ := Set.mem_iUnion.mp hz
    refine ⟨e.inv (torsionComponent R L i j b), ?_⟩
    exact congrArg (fun f => f b) (he i j)

include hG hL in
lemma marking_card_generic :
    Nat.card (FullLevel R W G L
      (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure (FractionRing R)))))) =
      levelDegree L := by
  classical
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let K := AlgebraicClosure (FractionRing R)
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  letI : CharZero K := Algebra.charZero_of_charZero (FractionRing R) K
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  have ho : (G.one (𝟙 _)).val = (WeierstrassProjModel.kwZeroSect R W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G ho
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let E := (W.toProjective.baseChange K).toAffine.Point
  have hm (x y : SchemeHomOver t (structureMap R W)) :
      ev K (G.mul t x y) = ev K x + ev K y := hev.1 K x y
  have hz : ev K (G.one t) = 0 := by
    have hh := hm (G.one t) (G.one t)
    rw [G.one_mul] at hh
    exact (add_left_cancel (a := ev K (G.one t)) ((add_zero _).trans hh)).symm
  have hd (d : ℕ) (hdiv : d ∣ L) :
      Nat.card (Submodule.torsionBy ℤ E (d : ℤ)) = d ^ 2 := by
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.ne_of_gt hL) hdiv
    exact WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine (Nat.cast_ne_zero.mpr hd0) (by norm_num)
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (Nat.ne_of_gt hL) hd
  have hc := hd L dvd_rfl
  let H := Submodule.torsionBy ℤ E (L : ℤ)
  letI : Finite H := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 (Nat.ne_of_gt hL))
  have hk (x : H) : L • x = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (L : ℤ) x
  exact (Nat.card_congr (fieldMarkEquiv (L := L) (hG := hG) (t := t)
    (ev := ev K) (hm := hm) (hz := hz))).trans (card_basisPair L hk hc e)

include hG hL in
lemma representing_rank (Z : LevelScheme R W G L) (hZ : Represents R W G Z) :
    ∀ z, Z.projection.finrank z = levelDegree L := by
  obtain ⟨hf,he⟩ := representing_finite_etale R W G hG L hL Z hZ
  letI := hf
  letI := he
  let K := AlgebraicClosure (FractionRing R)
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  intro z
  calc
    Z.projection.finrank z = Z.projection.finrank (t (IsLocalRing.closedPoint K)) :=
      Z.projection.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = Nat.card (SchemeHomOver t Z.projection) :=
      finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed Z.projection K (algebraMap R K)
    _ = Nat.card (FullLevel R W G L t) := Nat.card_congr (sectionsEquiv Z hZ t)
    _ = levelDegree L := marking_card_generic R W G hG L hL

include hL in
lemma levelDegree_pos : 0 < levelDegree L := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  unfold levelDegree
  exact Nat.card_pos

end CoverGeometryR0175

open CoverGeometryR0175 AlgebraicGeometry ArithmeticThetaRelativeKatoR0169

/-- The full GL level cover is finite étale and surjective, with its actual rank. -/
theorem full_level_cover_geometry :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) (Z : ArithmeticThetaFullLevelCoverR0175.LevelScheme R W G L) (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z), AlgebraicGeometry.IsFinite Z.projection ∧ AlgebraicGeometry.Etale Z.projection ∧ AlgebraicGeometry.Surjective Z.projection ∧ ∀ z, Z.projection.finrank z = ArithmeticThetaFullLevelCoverR0175.levelDegree L := by
  intro R _ _ _ _ _ W _ G hG L hL Z hZ
  obtain ⟨hf,he⟩ := representing_finite_etale R W G hG L hL Z hZ
  letI := hf
  letI := he
  have hr := representing_rank R W G hG L hL Z hZ
  have hs : Surjective Z.projection := Z.projection.one_le_finrank_iff_surjective.mp
    (fun z => by rw [hr]; exact levelDegree_pos L hL)
  exact ⟨hf,he,hs,hr⟩

#print axioms CoverGeometryR0175.torsion_support_eq_marked_union
#print axioms full_level_cover_geometry
end ArithmeticThetaFullLevelCoverR0175
