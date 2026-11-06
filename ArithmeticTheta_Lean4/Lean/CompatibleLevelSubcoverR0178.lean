import CompatibleLevelDefinitionsR0178

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompatibleLevelR0178
namespace SubcoverR0178
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open Representability

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : LegendreAtlas k L) (B : TwoMarking k L A)

private lemma half_killed (heven : Even L)
    (z : SchemeHomOver A.level.projection (structureMap (LegendreRing k) (legendre k)))
    (hz : A.law.nsmul _ L z = A.law.one _) :
    A.law.nsmul _ 2 (A.law.nsmul _ (L / 2) z) = A.law.one _ := by
  letI := A.law.pointGroup A.level.projection
  have hn (n : ℕ) (x : SchemeHomOver A.level.projection
      (structureMap (LegendreRing k) (legendre k))) : A.law.nsmul _ n x = x ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [A.law.nsmul_succ, ih]; rfl
  rw [hn, hn, ← pow_mul, Nat.div_mul_cancel heven.two_dvd, ← hn]
  exact hz

abbrev twoPairs := pairs (LegendreRing k) (legendre k) A.law 2
abbrev twoProjection := pp (LegendreRing k) (legendre k) A.law 2

/-- The two actual half-multiples, mapped into the square of the two-torsion scheme. -/
def reduction (heven : Even L) : A.level.space ⟶ twoPairs k L A :=
  pullback.lift
    (klift _ _ A.law A.originLaw 2 A.level.projection
      (A.law.nsmul _ (L / 2) A.level.level.x)
      (half_killed k L A heven _ A.level.level.killed_x))
    (klift _ _ A.law A.originLaw 2 A.level.projection
      (A.law.nsmul _ (L / 2) A.level.level.y)
      (half_killed k L A heven _ A.level.level.killed_y)) (by simp)

@[simp] lemma reduction_x (heven : Even L) :
    reduction k L A heven ≫ (px _ _ A.law 2).val =
      (A.law.nsmul _ (L / 2) A.level.level.x).val := by
  simp [reduction, px, WeierstrassProjModel.schemeHomOverComp, kpoint, ← Category.assoc]

@[simp] lemma reduction_y (heven : Even L) :
    reduction k L A heven ≫ (py _ _ A.law 2).val =
      (A.law.nsmul _ (L / 2) A.level.level.y).val := by
  simp [reduction, py, WeierstrassProjModel.schemeHomOverComp, kpoint, ← Category.assoc]

@[simp] lemma reduction_projection (heven : Even L) :
    reduction k L A heven ≫ twoProjection k L A = A.level.projection := by
  simp only [reduction, twoProjection, pp, ← Category.assoc,
    pullback.lift_fst, klift_ki]
  exact (A.law.nsmul _ (L / 2) A.level.level.x).property

def canonicalPair : Base (LegendreRing k) ⟶ twoPairs k L A :=
  pairLift _ _ A.law A.originLaw 2 (𝟙 _) B

@[simp] lemma canonicalPair_x : canonicalPair k L A B ≫ (px _ _ A.law 2).val = B.x.val :=
  pairLift_x _ _ A.law A.originLaw 2 _ B
@[simp] lemma canonicalPair_y : canonicalPair k L A B ≫ (py _ _ A.law 2).val = B.y.val :=
  pairLift_y _ _ A.law A.originLaw 2 _ B
@[simp] lemma canonicalPair_projection :
    canonicalPair k L A B ≫ twoProjection k L A = 𝟙 _ :=
  pairLift_p _ _ A.law A.originLaw 2 _ B

abbrev locus (heven : Even L) := pullback (reduction k L A heven) (canonicalPair k L A B)
abbrev inclusion (heven : Even L) : locus k L A B heven ⟶ A.level.space :=
  pullback.fst _ _

lemma compatibility_iff (heven : Even L) {T : Scheme.{u}} (a : T ⟶ A.level.space) :
    CompatibleAt k L A B a ↔
      a ≫ reduction k L A heven = (a ≫ A.level.projection) ≫ canonicalPair k L A B := by
  constructor
  · intro h
    apply pairs_ext (LegendreRing k) (legendre k) A.law 2
    · simpa only [Category.assoc, reduction_x, canonicalPair_x] using h.1
    · simpa only [Category.assoc, reduction_y, canonicalPair_y] using h.2
  · intro h
    constructor
    · simpa only [Category.assoc, reduction_x, canonicalPair_x] using
        congrArg (fun f => f ≫ (px _ _ A.law 2).val) h
    · simpa only [Category.assoc, reduction_y, canonicalPair_y] using
        congrArg (fun f => f ≫ (py _ _ A.law 2).val) h

lemma inclusion_projection (heven : Even L) :
    inclusion k L A B heven ≫ A.level.projection =
      pullback.snd (reduction k L A heven) (canonicalPair k L A B) := by
  have h := congrArg (fun f => f ≫ twoProjection k L A)
    (pullback.condition (f := reduction k L A heven) (g := canonicalPair k L A B))
  simpa only [Category.assoc, reduction_projection, canonicalPair_projection,
    Category.comp_id] using h

lemma locus_compatible (heven : Even L) :
    CompatibleAt k L A B (inclusion k L A B heven) := by
  rw [compatibility_iff, inclusion_projection]
  exact pullback.condition

/-- Scheme-theoretic representability, without restrictions on the test scheme. -/
lemma locus_represents (heven : Even L) (T : Scheme.{u}) (a : T ⟶ A.level.space) :
    CompatibleAt k L A B a ↔ ∃! b : T ⟶ locus k L A B heven,
      b ≫ inclusion k L A B heven = a := by
  rw [compatibility_iff k L A B heven]
  constructor
  · intro h
    refine ⟨pullback.lift a (a ≫ A.level.projection) h, pullback.lift_fst _ _ _, ?_⟩
    intro b hb
    apply pullback.hom_ext
    · exact hb.trans (pullback.lift_fst _ _ _).symm
    · rw [pullback.lift_snd, ← inclusion_projection, ← Category.assoc, hb]
  · rintro ⟨b, hb, _⟩
    simpa only [← hb, Category.assoc, inclusion_projection] using
      congrArg (fun f => b ≫ f) (pullback.condition
        (f := reduction k L A heven) (g := canonicalPair k L A B))

lemma canonicalPair_immersions :
    IsOpenImmersion (canonicalPair k L A B) ∧ IsClosedImmersion (canonicalPair k L A B) := by
  obtain ⟨hd, hn, hi, he, _⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := he
  letI : Algebra ℚ (LegendreRing k) := ((algebraMap k (LegendreRing k)).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨hf, ht⟩ := kernel_finite_etale (LegendreRing k) (legendre k) A.law A.originLaw 2 (by decide)
  letI := hf
  letI := ht
  letI : Etale (twoProjection k L A) := by dsimp [twoProjection, pp]; infer_instance
  letI : IsSeparated (twoProjection k L A) := by dsimp [twoProjection, pp]; infer_instance
  refine ⟨section_open (twoProjection k L A) _ (canonicalPair_projection k L A B), ?_⟩
  letI : IsClosedImmersion (canonicalPair k L A B ≫ twoProjection k L A) := by
    rw [canonicalPair_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (canonicalPair k L A B) (twoProjection k L A)

lemma locus_immersions (heven : Even L) :
    IsOpenImmersion (inclusion k L A B heven) ∧
      IsClosedImmersion (inclusion k L A B heven) := by
  obtain ⟨ho, hc⟩ := canonicalPair_immersions k L A B
  letI := ho
  letI := hc
  exact ⟨inferInstance, inferInstance⟩

lemma locus_finite_etale (hL : 0 < L) (heven : Even L) :
    IsFinite (inclusion k L A B heven ≫ A.level.projection) ∧
      Etale (inclusion k L A B heven ≫ A.level.projection) := by
  obtain ⟨hd, hn, hi, he, _⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := he
  letI : Algebra ℚ (LegendreRing k) := ((algebraMap k (LegendreRing k)).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨hf, ht⟩ := CoverGeometryR0175.representing_finite_etale
    (LegendreRing k) (legendre k) A.law A.originLaw L hL A.level A.represents
  obtain ⟨ho, hc⟩ := locus_immersions k L A B heven
  letI := hf
  letI := ht
  letI := ho
  letI := hc
  exact ⟨inferInstance, inferInstance⟩

section Counting
open CoverGeometryR0175
variable {E : Type u} [AddCommGroup E]

private lemma torsion_killed (n : ℕ) (x : Submodule.torsionBy ℤ E (n : ℤ)) :
    n • x = 0 := by
  simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (n : ℤ) x

/-- Half multiplication lands in the actual two-torsion subgroup. -/
def halfPoint (heven : Even L) (x : Submodule.torsionBy ℤ E (L : ℤ)) :
    Submodule.torsionBy ℤ E (2 : ℤ) :=
  ⟨(L / 2) • x.val, by
    rw [Submodule.mem_torsionBy_iff, show (2 : ℤ) = (2 : ℕ) by rfl,
      Nat.cast_smul_eq_nsmul, smul_smul, Nat.mul_comm, Nat.div_mul_cancel heven.two_dvd]
    exact congrArg Subtype.val (torsion_killed L x)⟩

/-- Reduction of a full basis stays independent, also for even composite levels. -/
def reduceBasis (hL : 0 < L) (heven : Even L)
    (a : BasisPair (H := Submodule.torsionBy ℤ E (L : ℤ)) L) :
    BasisPair (H := Submodule.torsionBy ℤ E (2 : ℤ)) 2 :=
  ⟨(halfPoint L heven a.val.1, halfPoint L heven a.val.2), by
    intro i j hij hz
    have halfpos : 0 < L / 2 := by
      have h := Nat.div_mul_cancel heven.two_dvd
      omega
    have halflt : L / 2 < L := Nat.div_lt_self hL (by decide)
    have hi : i.val * (L / 2) < L := by
      have h := i.isLt
      interval_cases hival : i.val <;> simp_all
    have hj : j.val * (L / 2) < L := by
      have h := j.isLt
      interval_cases hjval : j.val <;> simp_all
    have hn : i.val * (L / 2) ≠ 0 ∨ j.val * (L / 2) ≠ 0 := by
      rcases hij with h | h
      · exact Or.inl (Nat.mul_ne_zero h (Nat.ne_of_gt halfpos))
      · exact Or.inr (Nat.mul_ne_zero h (Nat.ne_of_gt halfpos))
    apply a.property ⟨_, hi⟩ ⟨_, hj⟩ hn
    apply Subtype.ext
    have hh := congrArg Subtype.val hz
    simpa only [halfPoint, Submodule.coe_add, Submodule.coe_smul_of_tower,
      ZeroMemClass.coe_zero, smul_smul] using hh⟩

/-- Integral elementary change of basis; valid over every additive group. -/
def shear (H : Type u) [AddCommGroup H] : H × H ≃+ H × H where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> abel

def swap (H : Type u) [AddCommGroup H] : H × H ≃+ H × H where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := rfl
  right_inv p := rfl
  map_add' p q := rfl

/-- The six integral matrices which realize every invertible matrix modulo two. -/
def sixChanges (H : Type u) [AddCommGroup H] : Fin 6 → (H × H ≃+ H × H) :=
  ![AddEquiv.refl _, swap H, shear H, (shear H).trans (swap H),
    (swap H).trans (shear H), ((swap H).trans (shear H)).trans (swap H)]

lemma sixChanges_exhaust (e : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2)) :
    ∃ i : Fin 6, e = sixChanges (ZMod 2) i := by
  have hx : e (1,0) ≠ 0 := fun h => (by decide : ((1,0) : ZMod 2 × ZMod 2) ≠ (0,0))
    (e.injective (h.trans e.map_zero.symm))
  have hy : e (0,1) ≠ 0 := fun h => (by decide : ((0,1) : ZMod 2 × ZMod 2) ≠ (0,0))
    (e.injective (h.trans e.map_zero.symm))
  have hxy : e (1,0) ≠ e (0,1) := fun h => (by decide :
    ((1,0) : ZMod 2 × ZMod 2) ≠ (0,1)) (e.injective h)
  have extgen (a b : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2))
      (h1 : a (1,0) = b (1,0)) (h2 : a (0,1) = b (0,1)) : a = b := by
    apply AddEquiv.ext
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j
    · exact a.map_zero.trans b.map_zero.symm
    · exact h2
    · exact h1
    · change a ((1,0)+(0,1)) = b ((1,0)+(0,1))
      rw [map_add, map_add, h1, h2]
  generalize h1 : e (1,0) = x at hx hxy
  generalize h2 : e (0,1) = y at hy hxy
  rcases x with ⟨x1,x2⟩
  rcases y with ⟨y1,y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    first
    | exact False.elim (hx rfl)
    | exact False.elim (hy rfl)
    | exact False.elim (hxy rfl)
    | exact ⟨0, extgen _ _ h1 h2⟩
    | exact ⟨1, extgen _ _ h1 h2⟩
    | exact ⟨2, extgen _ _ h1 h2⟩
    | exact ⟨3, extgen _ _ h1 h2⟩
    | exact ⟨4, extgen _ _ h1 h2⟩
    | exact ⟨5, extgen _ _ h1 h2⟩

lemma sixChanges_injective : Function.Injective (sixChanges (ZMod 2)) := by
  intro i j h
  have hx := congrArg (fun e : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2) => e (1,0)) h
  have hy := congrArg (fun e : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2) => e (0,1)) h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hx (by decide) | exact absurd hy (by decide)

lemma levelDegree_two : levelDegree 2 = 6 := by
  have h : Function.Bijective (sixChanges (ZMod 2)) :=
    ⟨sixChanges_injective, fun e => by obtain ⟨i, hi⟩ := sixChanges_exhaust e; exact ⟨i, hi.symm⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ h)).symm.trans (Nat.card_fin 6)

variable {H : Type u} [AddCommGroup H] [Finite H]
  (n : ℕ) [NeZero n] (hk : ∀ x : H, n • x = 0) (hc : Nat.card H = n^2)

def precompose (s : (ZMod n × ZMod n) ≃+ (ZMod n × ZMod n)) :
    ((ZMod n × ZMod n) ≃+ H) ≃ ((ZMod n × ZMod n) ≃+ H) where
  toFun e := s.trans e
  invFun e := s.symm.trans e
  left_inv e := by ext x; simp
  right_inv e := by ext x; simp

def basisChange (s : (ZMod n × ZMod n) ≃+ (ZMod n × ZMod n)) :
    BasisPair (H := H) n ≃ BasisPair (H := H) n :=
  (basisPairEquiv n hk hc).trans ((precompose n s).trans (basisPairEquiv n hk hc).symm)

lemma basisChange_pair (i : Fin 6) (a : BasisPair (H := H) n) :
    (basisChange n hk hc (sixChanges (ZMod n) i) a).val =
      ![(a.val.1,a.val.2), (a.val.2,a.val.1), (a.val.1,a.val.1+a.val.2),
        (a.val.2,a.val.1+a.val.2), (a.val.1+a.val.2,a.val.1),
        (a.val.1+a.val.2,a.val.2)] i := by
  have diag (x y : H) : pairHom n hk x y (1,1) = x+y := by
    rw [show ((1,1) : ZMod n × ZMod n) = (1,0)+(0,1) by simp,
      map_add, pairHom_fst, pairHom_snd]
  fin_cases i <;>
    simp [basisChange, precompose, basisPairEquiv, equivPair, sixChanges, shear, swap,
      pairHom_fst, pairHom_snd, diag]


lemma changes_transitive_two {H : Type u} [AddCommGroup H] [Finite H]
    (hk : ∀ x : H, 2 • x = 0) (hc : Nat.card H = 2^2)
    (a b : BasisPair (H := H) 2) :
    ∃ i : Fin 6, basisChange 2 hk hc (sixChanges (ZMod 2) i) a = b := by
  let ea := basisPairEquiv 2 hk hc a
  let eb := basisPairEquiv 2 hk hc b
  obtain ⟨i, hi⟩ := sixChanges_exhaust (eb.trans ea.symm)
  refine ⟨i, (basisPairEquiv 2 hk hc).injective ?_⟩
  change basisPairEquiv 2 hk hc ((basisPairEquiv 2 hk hc).symm
    ((sixChanges (ZMod 2) i).trans ea)) = eb
  rw [Equiv.apply_symm_apply, ← hi]
  ext x
  exact ea.apply_symm_apply (eb x)

variable [NeZero L] [Finite (Submodule.torsionBy ℤ E (L : ℤ))]
  [Finite (Submodule.torsionBy ℤ E (2 : ℤ))]

lemma reduceBasis_change (hL : 0 < L) (heven : Even L)
    (hcL : Nat.card (Submodule.torsionBy ℤ E (L : ℤ)) = L^2)
    (hc2 : Nat.card (Submodule.torsionBy ℤ E (2 : ℤ)) = 2^2)
    (i : Fin 6) (a : BasisPair (H := Submodule.torsionBy ℤ E (L : ℤ)) L) :
    reduceBasis L hL heven
      (basisChange L (torsion_killed L) hcL (sixChanges (ZMod L) i) a) =
    basisChange 2 (torsion_killed 2) hc2 (sixChanges (ZMod 2) i) (reduceBasis L hL heven a) := by
  apply Subtype.ext
  change (halfPoint L heven (basisChange L (torsion_killed L) hcL
      (sixChanges (ZMod L) i) a).val.1,
    halfPoint L heven (basisChange L (torsion_killed L) hcL
      (sixChanges (ZMod L) i) a).val.2) = _
  rw [basisChange_pair, basisChange_pair]
  fin_cases i <;> apply Prod.ext <;> apply Subtype.ext <;>
    simp [halfPoint, reduceBasis]

/-- The fibers of reduction to ordered two-torsion bases all have the same size. -/
def reductionFiberEquiv (hL : 0 < L) (heven : Even L)
    (hcL : Nat.card (Submodule.torsionBy ℤ E (L : ℤ)) = L^2)
    (hc2 : Nat.card (Submodule.torsionBy ℤ E (2 : ℤ)) = 2^2)
    (a b : BasisPair (H := Submodule.torsionBy ℤ E (2 : ℤ)) 2) :
    {x // reduceBasis L hL heven x = a} ≃ {x // reduceBasis L hL heven x = b} := by
  let i := (changes_transitive_two (torsion_killed 2) hc2 a b).choose
  have hi := (changes_transitive_two (torsion_killed 2) hc2 a b).choose_spec
  apply (basisChange L (torsion_killed L) hcL (sixChanges (ZMod L) i)).subtypeEquiv
  intro x
  rw [reduceBasis_change L hL heven hcL hc2, ← hi]
  exact (basisChange 2 (torsion_killed 2) hc2 (sixChanges (ZMod 2) i)).injective.eq_iff.symm

lemma card_reduction_fiber (hL : 0 < L) (heven : Even L)
    (hcL : Nat.card (Submodule.torsionBy ℤ E (L : ℤ)) = L^2)
    (hc2 : Nat.card (Submodule.torsionBy ℤ E (2 : ℤ)) = 2^2)
    (eL : (ZMod L × ZMod L) ≃+ Submodule.torsionBy ℤ E (L : ℤ))
    (b : BasisPair (H := Submodule.torsionBy ℤ E (2 : ℤ)) 2) :
    Nat.card {x // reduceBasis L hL heven x = b} = levelDegree L / 6 ∧
      0 < Nat.card {x // reduceBasis L hL heven x = b} := by
  let f := reduceBasis (E := E) L hL heven
  have hc : Nat.card (BasisPair (H := Submodule.torsionBy ℤ E (2 : ℤ)) 2) = 6 := by
    rw [card_basisPair 2 (torsion_killed 2) hc2 (basisPairEquiv 2 (torsion_killed 2) hc2 b),
      levelDegree_two]
  let e := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight fun a => reductionFiberEquiv L hL heven hcL hc2 a b) |>.trans
      (Equiv.sigmaEquivProd _ _)
  have count : levelDegree L = 6 * Nat.card {x // f x = b} := by
    rw [← card_basisPair L (torsion_killed L) hcL eL, Nat.card_congr e, Nat.card_prod, hc]
  constructor
  · rw [count, Nat.mul_div_cancel_left _ (by decide : 0 < 6)]
  · have hp := CoverGeometryR0175.levelDegree_pos L hL
    rw [count] at hp
    change 0 < Nat.card {x // f x = b}
    omega

end Counting


open CoverGeometryR0175

/-- Sections of the constructed locus are exactly compatible sections of the full cover. -/
def locusSectionsEquiv (heven : Even L) {T : Scheme.{u}} (t : T ⟶ Base (LegendreRing k)) :
    SchemeHomOver t (inclusion k L A B heven ≫ A.level.projection) ≃
      {q : SchemeHomOver t A.level.projection // CompatibleAt k L A B q.val} where
  toFun b := ⟨⟨b.val ≫ inclusion k L A B heven, by rw [Category.assoc]; exact b.property⟩, by
    apply (compatibility_iff k L A B heven _).mpr
    have h := congrArg (fun f => b.val ≫ f)
      (pullback.condition (f := reduction k L A heven) (g := canonicalPair k L A B))
    simpa only [Category.assoc, inclusion_projection] using h⟩
  invFun q := ⟨pullback.lift q.val.val t (by
    simpa only [q.val.property] using (compatibility_iff k L A B heven _).mp q.property), by
    rw [← Category.assoc, pullback.lift_fst]
    exact q.val.property⟩
  left_inv b := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd, ← inclusion_projection, ← Category.assoc]
      exact b.property.symm
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

def MarkCompatible {T : Scheme.{u}} (t : T ⟶ Base (LegendreRing k))
    (M : FullLevel (LegendreRing k) (legendre k) A.law L t) : Prop :=
  (A.law.nsmul t (L / 2) M.x).val = t ≫ B.x.val ∧
  (A.law.nsmul t (L / 2) M.y).val = t ≫ B.y.val

lemma marking_compatibility {T : Scheme.{u}} (t : T ⟶ Base (LegendreRing k))
    (q : SchemeHomOver t A.level.projection) :
    CompatibleAt k L A B q.val ↔
      MarkCompatible k L A B t (sectionsEquiv A.level A.represents t q) := by
  have hn (x : SchemeHomOver A.level.projection (structureMap (LegendreRing k) (legendre k))) :
      q.val ≫ (A.law.nsmul A.level.projection (L / 2) x).val =
        (A.law.nsmul t (L / 2) (WeierstrassProjModel.schemeHomOverComp q.val q.property x)).val :=
    congrArg Subtype.val (A.law.nsmul_natural _ _ q.val q.property _ x)
  simp only [CompatibleAt, MarkCompatible, sectionsEquiv, pullMark, Equiv.coe_fn_mk,
    hn, q.property]

def locusMarkingsEquiv (heven : Even L) {T : Scheme.{u}} (t : T ⟶ Base (LegendreRing k)) :
    SchemeHomOver t (inclusion k L A B heven ≫ A.level.projection) ≃
      {M : FullLevel (LegendreRing k) (legendre k) A.law L t // MarkCompatible k L A B t M} :=
  (locusSectionsEquiv k L A B heven t).trans
    ((sectionsEquiv A.level A.represents t).subtypeEquiv (marking_compatibility k L A B t))

section FieldComparison
variable {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Base (LegendreRing k))
  {E : Type u} [AddCommGroup E]
  (ev : SchemeHomOver t (structureMap (LegendreRing k) (legendre k)) ≃ E)
  (hm : ∀ x y, ev (A.law.mul t x y) = ev x + ev y)
  (hz : ev (A.law.one t) = 0)
  [NeZero L]

lemma field_compatibility (hL : 0 < L) (heven : Even L)
    (M : FullLevel (LegendreRing k) (legendre k) A.law L t) :
    MarkCompatible k L A B t M ↔
    reduceBasis L hL heven
      (fieldMarkEquiv (L := L) (hG := A.originLaw) (t := t) (ev := ev) (hm := hm) (hz := hz) M) =
    fieldMarkEquiv (L := 2) (hG := A.originLaw) (t := t) (ev := ev) (hm := hm) (hz := hz)
      (pullMark t (Category.comp_id _) B) := by
  have hh (x : SchemeHomOver t (structureMap (LegendreRing k) (legendre k)))
      (y : SchemeHomOver (𝟙 (Base (LegendreRing k))) (structureMap (LegendreRing k) (legendre k))) :
      (A.law.nsmul t (L / 2) x).val = t ≫ y.val ↔
      (L / 2) • ev x = ev (WeierstrassProjModel.schemeHomOverComp t (Category.comp_id _) y) := by
    rw [← eval_nsmul t ev hm hz]
    constructor
    · intro h
      exact congrArg ev (Subtype.ext h)
    · intro h
      exact congrArg Subtype.val (ev.injective h)
  rw [MarkCompatible, hh, hh]
  constructor
  · rintro ⟨hx,hy⟩
    apply Subtype.ext
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  · intro h
    exact ⟨congrArg (fun a => a.val.1.val) h, congrArg (fun a => a.val.2.val) h⟩

def locusBasisEquiv (hL : 0 < L) (heven : Even L) :
    SchemeHomOver t (inclusion k L A B heven ≫ A.level.projection) ≃
      {a // reduceBasis L hL heven a =
        fieldMarkEquiv (L := 2) (hG := A.originLaw) (t := t) (ev := ev) (hm := hm) (hz := hz)
          (pullMark t (Category.comp_id _) B)} :=
  (locusMarkingsEquiv k L A B heven t).trans
    ((fieldMarkEquiv (L := L) (hG := A.originLaw) (t := t) (ev := ev) (hm := hm) (hz := hz)).subtypeEquiv
      (field_compatibility k L A B t ev hm hz hL heven))
end FieldComparison


/-- The positive generic fiber count determines the rank on the integral Legendre base. -/
lemma locus_rank (hL : 0 < L) (heven : Even L) :
    (∀ z, (inclusion k L A B heven ≫ A.level.projection).finrank z = levelDegree L / 6) ∧
      0 < levelDegree L / 6 := by
  classical
  obtain ⟨hd, hn, hi, he, _⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := hi
  letI := he
  let R := LegendreRing k
  let W := legendre k
  let G := A.law
  letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let K := AlgebraicClosure (FractionRing R)
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  letI : CharZero K := Algebra.charZero_of_charZero (FractionRing R) K
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  have ho : (G.one (𝟙 _)).val = (WeierstrassProjModel.kwZeroSect R W).val := by
    simpa only [Category.id_comp, origin] using A.originLaw.1 (𝟙 _)
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
  have hdcard (d : ℕ) (hd0 : d ≠ 0) :
      Nat.card (Submodule.torsionBy ℤ E (d : ℤ)) = d^2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine (Nat.cast_ne_zero.mpr hd0) (by norm_num)
  obtain ⟨eL⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (Nat.ne_of_gt hL) (fun d hdiv => hdcard d (ne_zero_of_dvd_ne_zero (Nat.ne_of_gt hL) hdiv))
  have hcL := hdcard L (Nat.ne_of_gt hL)
  have hc2 : Nat.card (Submodule.torsionBy ℤ E (2 : ℤ)) = 2^2 := by
    simpa only [Nat.cast_ofNat] using hdcard 2 (by decide)
  letI : Finite (Submodule.torsionBy ℤ E (L : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcL]; exact pow_ne_zero 2 (Nat.ne_of_gt hL))
  letI : Finite (Submodule.torsionBy ℤ E (2 : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hc2]; decide)
  let b := fieldMarkEquiv (L := 2) (hG := A.originLaw) (t := t)
    (ev := ev K) (hm := hm) (hz := hz) (pullMark t (Category.comp_id _) B)
  obtain ⟨hc, hp⟩ := card_reduction_fiber L hL heven hcL hc2 eL b
  refine ⟨?_, hc ▸ hp⟩
  obtain ⟨hf, ht⟩ := locus_finite_etale k L A B hL heven
  letI := hf
  letI := ht
  letI : LocallyOfFinitePresentation (inclusion k L A B heven ≫ A.level.projection) :=
    (Etale.iff_flat_and_formallyUnramified.mp ht).2.2
  letI : Flat (inclusion k L A B heven ≫ A.level.projection) :=
    (Etale.iff_flat_and_formallyUnramified.mp ht).1
  intro z
  calc
    (inclusion k L A B heven ≫ A.level.projection).finrank z =
        (inclusion k L A B heven ≫ A.level.projection).finrank (t (IsLocalRing.closedPoint K)) :=
      (inclusion k L A B heven ≫ A.level.projection).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = Nat.card (SchemeHomOver t (inclusion k L A B heven ≫ A.level.projection)) :=
      finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
        (inclusion k L A B heven ≫ A.level.projection) K (algebraMap R K)
    _ = Nat.card {a // reduceBasis L hL heven a = b} :=
      Nat.card_congr (locusBasisEquiv k L A B t (ev K) hm hz hL heven)
    _ = levelDegree L / 6 := hc

end SubcoverR0178
end ArithmeticThetaCompatibleLevelR0178

namespace ArithmeticThetaCompatibleLevelR0178
open CategoryTheory AlgebraicGeometry ArithmeticThetaLegendreAtlasR0176

/-- The simultaneous compatibility locus, including its universal property and exact degree. -/
theorem compatible_level_subcover :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : LegendreAtlas k L) (B : TwoMarking k L A),
      CanonicalTwo k L A B → Nonempty (CompatibleCover k L A B) := by
  intro k _ _ L hL heven A B _hcanonical
  have hpos : 0 < L := by omega
  obtain ⟨ho, hc⟩ := SubcoverR0178.locus_immersions k L A B heven
  obtain ⟨hf, ht⟩ := SubcoverR0178.locus_finite_etale k L A B hpos heven
  obtain ⟨hr, hp⟩ := SubcoverR0178.locus_rank k L A B hpos heven
  letI := hf
  letI := ht
  refine ⟨{
    space := SubcoverR0178.locus k L A B heven
    inclusion := SubcoverR0178.inclusion k L A B heven
    openImmersion := ho
    closedImmersion := hc
    compatible := SubcoverR0178.locus_compatible k L A B heven
    represents := SubcoverR0178.locus_represents k L A B heven
    finite := hf
    etale := ht
    surjective := ?_
    degree := hr }⟩
  exact (SubcoverR0178.inclusion k L A B heven ≫ A.level.projection).one_le_finrank_iff_surjective.mp
    (fun z => by rw [hr]; exact hp)

#print axioms compatible_level_subcover
end ArithmeticThetaCompatibleLevelR0178
