module

public import SchemeFourCoverGeometryR0216
public import SchemePhaseMarkingInvarianceR0215
public import SchemeFourMarkingActionR0215

@[expose] public section

/-! Scheme-local rigidity and comparison of full-four markings. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216.LocallyConstantMarkingComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215.SchemeFourMarkingActionR0215
open ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175
open SchemeFourCover
open ArithmeticThetaFourTorsion

variable {S : Scheme.{u}} (E : Family S)

def coordinate (M : FullLevel E 4) (a : Fin 4 × Fin 4) : S ⟶ E.curve :=
  (E.law.mul (𝟙 S) (multiple E (𝟙 S) a.1.val M.x)
    (multiple E (𝟙 S) a.2.val M.y)).val

lemma coordinate_over (M : FullLevel E 4) (a : Fin 4 × Fin 4) :
    coordinate E M a ≫ E.p = 𝟙 S :=
  (E.law.mul _ _ _).property

/-- Distinct residue combinations have disjoint images as scheme sections. -/
lemma coordinates_disjoint (M : FullLevel E 4) (a b : Fin 4 × Fin 4) (hab : a ≠ b) :
    Disjoint (Set.range (coordinate E M a)) (Set.range (coordinate E M b)) := by
  let s := coordinate E M a
  let s' := coordinate E M b
  let T := pullback s s'
  let p : T ⟶ S := pullback.fst s s'
  have hpq : p = pullback.snd s s' := by
    have h := congrArg (fun f => f ≫ E.p) (pullback.condition (f := s) (g := s'))
    simpa only [Category.assoc, coordinate_over, Category.comp_id, s, s'] using h
  have heq : p ≫ s = p ≫ s' := by
    have h := pullback.condition (f := s) (g := s')
    rw [← hpq] at h
    exact h
  let i : Fin 4 := ⟨(a.1.val + 4 - b.1.val) % 4, Nat.mod_lt _ (by decide)⟩
  let j : Fin 4 := ⟨(a.2.val + 4 - b.2.val) % 4, Nat.mod_lt _ (by decide)⟩
  have hij : i.val ≠ 0 ∨ j.val ≠ 0 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext (difference_nonzero (by decide) _ _ h.1)
      (difference_nonzero (by decide) _ _ h.2))
  let c (z : SchemeHomOver (𝟙 S) E.p) :=
    GoodReductionJacobian.schemeHomOverComp p (Category.comp_id p) z
  letI := pointGroup E p
  have cn (n : ℕ) (z : SchemeHomOver (𝟙 S) E.p) :
      c (multiple E _ n z) = multiple E p n (c z) := multiple_natural E _ _ _ _ _ _
  have cm (z z' : SchemeHomOver (𝟙 S) E.p) :
      c (E.law.mul _ z z') = E.law.mul p (c z) (c z') := E.law.mul_natural _ _ _ _ _ _
  have co : c (E.law.one (𝟙 S)) = E.law.one p := SchemeLocal.one_natural E.law _ _ _ _
  have hx : c M.x ^ 4 = 1 := by rw [← multiple_pow, ← cn, M.killed_x, co]; rfl
  have hy : c M.y ^ 4 = 1 := by rw [← multiple_pow, ← cn, M.killed_y, co]; rfl
  have he : c M.x ^ a.1.val * c M.y ^ a.2.val = c M.x ^ b.1.val * c M.y ^ b.2.val := by
    have h : c (E.law.mul _ (multiple E _ a.1.val M.x) (multiple E _ a.2.val M.y)) =
        c (E.law.mul _ (multiple E _ b.1.val M.x) (multiple E _ b.2.val M.y)) :=
      Subtype.ext heq
    rw [cm, cm, cn, cn, cn, cn] at h
    simp only [multiple_pow E] at h
    exact h
  have hz : c M.x ^ i.val * c M.y ^ j.val = 1 := by
    have hh : (c M.x ^ i.val * c M.y ^ j.val) * (c M.x ^ b.1.val * c M.y ^ b.2.val) =
        1 * (c M.x ^ b.1.val * c M.y ^ b.2.val) := by
      rw [one_mul, mul_mul_mul_comm]
      exact (congrArg₂ (· * ·) (difference_pow (c M.x) hx a.1 b.1)
        (difference_pow (c M.y) hy a.2 b.2)).trans he
    exact mul_right_cancel hh
  have hzero : p ≫ coordinate E M (i, j) = p ≫ E.zero := by
    have h : c (E.law.mul _ (multiple E _ i.val M.x) (multiple E _ j.val M.y)) =
        E.law.one p := by
      rw [cm, cn, cn, multiple_pow, multiple_pow]
      exact hz
    exact (congrArg Subtype.val h).trans (one_val E p)
  apply Scheme.isEmpty_pullback_iff.mp
  exact ⟨fun z => Set.disjoint_left.mp (M.avoids i j hij)
    ⟨p z, rfl⟩ ⟨p z, by exact (congrArg (fun f : T ⟶ E.curve => f z) hzero).symm⟩⟩

lemma coordinate_injective_at (M : FullLevel E 4) (s : S) :
    Function.Injective (fun a : Fin 4 × Fin 4 => coordinate E M a s) := by
  intro a b h
  by_contra hab
  exact Set.disjoint_left.mp (coordinates_disjoint E M a b hab)
    (Set.mem_range_self s) ⟨s, h.symm⟩

/-- The two columns of a matrix are recoverable at every base point. -/
lemma matrix_injective_at (M : FullLevel E 4) (s : S) (A B : Mat4)
    (hx : changedX E M A s = changedX E M B s)
    (hy : changedY E M A s = changedY E M B s) : A = B := by
  have hx' := coordinate_injective_at E M s
    (a₁ := (⟨(A 0 0).val, ZMod.val_lt _⟩, ⟨(A 1 0).val, ZMod.val_lt _⟩))
    (a₂ := (⟨(B 0 0).val, ZMod.val_lt _⟩, ⟨(B 1 0).val, ZMod.val_lt _⟩)) hx
  have hy' := coordinate_injective_at E M s
    (a₁ := (⟨(A 0 1).val, ZMod.val_lt _⟩, ⟨(A 1 1).val, ZMod.val_lt _⟩))
    (a₂ := (⟨(B 0 1).val, ZMod.val_lt _⟩, ⟨(B 1 1).val, ZMod.val_lt _⟩)) hy
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective 4 (congrArg (fun a => a.1.val) hx')
  · exact ZMod.val_injective 4 (congrArg (fun a => a.1.val) hy')
  · exact ZMod.val_injective 4 (congrArg (fun a => a.2.val) hx')
  · exact ZMod.val_injective 4 (congrArg (fun a => a.2.val) hy')

/-- Recover the columns from the actual local equalities in `LocalChange`. -/
lemma localChange_at (M N : FullLevel E 4) (g : LocallyConstant S EvenGroup)
    (h : LocalChange E M N g) (s : S) :
    N.x.val s = changedX E M (g s).val s ∧
      N.y.val s = changedY E M (g s).val s := by
  obtain ⟨U, hs, _, hx, hy⟩ := h s
  exact ⟨congrArg (fun f : U.toScheme ⟶ E.curve => f ⟨s, hs⟩) hx,
    congrArg (fun f : U.toScheme ⟶ E.curve => f ⟨s, hs⟩) hy⟩

lemma localChange_unique (M N : FullLevel E 4) (g h : LocallyConstant S EvenGroup)
    (hg : LocalChange E M N g) (hh : LocalChange E M N h) : g = h := by
  apply DFunLike.ext
  intro s
  apply Subtype.ext
  have eg := localChange_at E M N g hg s
  have eh := localChange_at E M N h hh s
  exact matrix_injective_at E M s _ _ (eg.1.symm.trans eh.1) (eg.2.symm.trans eh.2)

#print axioms coordinates_disjoint
#print axioms localChange_unique
/-- A single constant matrix is valid on an actual open neighbourhood. -/
def LocalWitness (M N : FullLevel E 4) (s : S) (A : EvenGroup) : Prop :=
  ∃ U : S.Opens, s ∈ U ∧
    U.ι ≫ N.x.val = U.ι ≫ changedX E M A.val ∧
    U.ι ≫ N.y.val = U.ι ≫ changedY E M A.val

lemma localWitness_at (M N : FullLevel E 4) (s : S) (A : EvenGroup)
    (h : LocalWitness E M N s A) :
    N.x.val s = changedX E M A.val s ∧ N.y.val s = changedY E M A.val s := by
  obtain ⟨U, hs, hx, hy⟩ := h
  exact ⟨congrArg (fun f : U.toScheme ⟶ E.curve => f ⟨s, hs⟩) hx,
    congrArg (fun f : U.toScheme ⟶ E.curve => f ⟨s, hs⟩) hy⟩

lemma localWitness_unique (M N : FullLevel E 4) (s : S) (A B : EvenGroup)
    (hA : LocalWitness E M N s A) (hB : LocalWitness E M N s B) : A = B := by
  apply Subtype.ext
  have ha := localWitness_at E M N s A hA
  have hb := localWitness_at E M N s B hB
  exact matrix_injective_at E M s A.val B.val (ha.1.symm.trans hb.1) (ha.2.symm.trans hb.2)

/-- Unique local matrices glue without assuming the base is connected or quasicompact. -/
lemma glue_localWitness (M N : FullLevel E 4)
    (h : ∀ s : S, ∃ A : EvenGroup, LocalWitness E M N s A) :
    ∃! g : LocallyConstant S EvenGroup, LocalChange E M N g := by
  classical
  let g : S → EvenGroup := fun s => Classical.choose (h s)
  have hg (s : S) : LocalWitness E M N s (g s) := Classical.choose_spec (h s)
  have hconst (s : S) : ∃ U : S.Opens, s ∈ U ∧
      (∀ t : S, t ∈ U → g t = g s) ∧
      U.ι ≫ N.x.val = U.ι ≫ changedX E M (g s).val ∧
      U.ι ≫ N.y.val = U.ι ≫ changedY E M (g s).val := by
    obtain ⟨U, hs, hx, hy⟩ := hg s
    refine ⟨U, hs, ?_, hx, hy⟩
    intro t ht
    exact localWitness_unique E M N t (g t) (g s) (hg t) ⟨U, ht, hx, hy⟩
  have hlc : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_exists_open g).mpr
    intro s
    obtain ⟨U, hs, hU, _, _⟩ := hconst s
    exact ⟨U, U.isOpen, hs, hU⟩
  let G : LocallyConstant S EvenGroup := ⟨g, hlc⟩
  have hG : LocalChange E M N G := hconst
  exact ⟨G, hG, fun G' hG' => localChange_unique E M N G' G hG' hG⟩

#print axioms glue_localWitness
/-- Equal points of two sections of an étale map give equality on an open neighbourhood.
The conclusion is equality of scheme morphisms, so it includes infinitesimal data. -/
lemma etale_sections_locally_equal {X B : Scheme.{u}} (p : X ⟶ B) [Etale p]
    (a b : B ⟶ X) (ha : a ≫ p = 𝟙 B) (hb : b ≫ p = 𝟙 B)
    (s : B) (he : a s = b s) :
    ∃ U : B.Opens, s ∈ U ∧ U.ι ≫ a = U.ι ≫ b := by
  letI : IsOpenImmersion a :=
    ArithmeticThetaFullLevelCoverR0175.Representability.section_open p a ha
  let U : B.Opens := b ⁻¹ᵁ a.opensRange
  have hU : Set.range (U.ι ≫ b) ⊆ Set.range a := by
    rintro _ ⟨t, rfl⟩
    exact t.property
  let l := IsOpenImmersion.lift a (U.ι ≫ b) hU
  have hl : l ≫ a = U.ι ≫ b := IsOpenImmersion.lift_fac a (U.ι ≫ b) hU
  have hl' : l = U.ι := by
    have h := congrArg (fun f => f ≫ p) hl
    simpa only [Category.assoc, ha, hb, Category.comp_id] using h
  exact ⟨U, ⟨s, he⟩, by simpa only [hl'] using hl⟩

section AffineRigidity
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaFullLevelCoverR0175.Representability

variable {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G)

include hG in
/-- Rigidity of actual torsion sections over an arbitrary rational base ring.
Étaleness is consumed from the geometry owner's arbitrary-base theorem. -/
lemma torsion_sections_locally_equal
    (x y : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hx : G.nsmul (𝟙 _) 4 x = G.one (𝟙 _))
    (hy : G.nsmul (𝟙 _) 4 y = G.one (𝟙 _))
    (s : Base R) (he : x.val s = y.val s) :
    ∃ U : (Base R).Opens, s ∈ U ∧ U.ι ≫ x.val = U.ι ≫ y.val := by
  letI : Etale (kp R W G 4) :=
    (SchemeFourCoverGeometry.kernel_finite_etale R W G hG 4 (by decide)).2
  let a := klift R W G hG 4 (𝟙 _) x hx
  let b := klift R W G hG 4 (𝟙 _) y hy
  have ha : a ≫ kp R W G 4 = 𝟙 _ := klift_kp R W G hG 4 _ _ _
  have hb : b ≫ kp R W G 4 = 𝟙 _ := klift_kp R W G hG 4 _ _ _
  have hai : a ≫ ki R W G 4 = x.val := klift_ki R W G hG 4 _ _ _
  have hbi : b ≫ ki R W G 4 = y.val := klift_ki R W G hG 4 _ _ _
  have he' : a s = b s := by
    apply (ki R W G 4).isClosedEmbedding.injective
    exact (congrArg (fun f : Base R ⟶ Curve R W => f s) hai).trans
      (he.trans (congrArg (fun f : Base R ⟶ Curve R W => f s) hbi).symm)
  obtain ⟨U, hs, hU⟩ := etale_sections_locally_equal (kp R W G 4) a b ha hb s he'
  refine ⟨U, hs, ?_⟩
  have h := congrArg (fun f => f ≫ ki R W G 4) hU
  simpa only [Category.assoc, hai, hbi] using h

end AffineRigidity
#print axioms torsion_sections_locally_equal
/-- In rank two the nonzero characteristic (2,2) singles out the even stabilizer. -/
lemma preservesEven_of_fixed_double : ∀ A : Mat4, A.det = 1 →
    A.mulVec (![2, 2] : Fin 2 → ZMod 4) = ![2, 2] → PreservesEven A := by
  decide

section GeometricComparison
open ArithmeticThetaMarkingR0115 ArithmeticThetaGeometricPairingR0118
variable {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (e : Fin 3 → F) (he : Function.Injective e)

include he in
/-- Pairing and even-point equality determine the required oriented stabilizer matrix
on an actual geometric elliptic curve. -/
lemma field_marking_comparison (b c : ArithmeticThetaMarkingR0115.Marking F e)
    (hb : IsBasis F e b) (hc : IsBasis F e c)
    (hz : phase F e b = phase F e c)
    (hp : 2 • b 0 + 2 • b 1 = 2 • c 0 + 2 • c 1) :
    ∃! A : EvenGroup, c = ArithmeticThetaMarkingR0115.act F e b A.val := by
  obtain ⟨v, hv⟩ := hb.2.2 (c 0) (hc.1 0)
  obtain ⟨w, hw⟩ := hb.2.2 (c 1) (hc.1 1)
  let A : Mat4 := fun i j => ![v i, w i] j
  have hact : c = ArithmeticThetaMarkingR0115.act F e b A := by
    funext j
    fin_cases j
    · exact hv.symm
    · exact hw.symm
  obtain ⟨D, _⟩ := geometric_four_character F e he
  have hprim : IsPrimitiveRoot (phase F e b) 4 :=
    (generator_s_miller_phase F e he b hb).2.1
  have hpow : phase F e b ^ A.det.val = phase F e b := by
    have h := pairing_coordinates F e he D b hb v w
    rw [hv, hw, marking_pairing_identification F e he D c hc,
      marking_pairing_identification F e he D b hb, ← hz] at h
    simpa only [A, Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm] using h.symm
  have hdet : A.det = 1 := by
    apply ZMod.val_injective 4
    exact hprim.pow_inj (ZMod.val_lt A.det) (by decide)
      (by change phase F e b ^ A.det.val = phase F e b ^ 1; simpa only [pow_one] using hpow)
  have hfix : A.mulVec (![2, 2] : Fin 2 → ZMod 4) = ![2, 2] := by
    apply hb.2.1
    rw [← coordinates_act b hb.1 A, ← hact]
    exact hp.symm
  have hA : PreservesEven A := preservesEven_of_fixed_double A hdet hfix
  refine ⟨⟨A, hA⟩, hact, ?_⟩
  intro B hB
  apply Subtype.ext
  funext i j
  have hcj := congrFun (hB.symm.trans hact) j
  have heq := hb.2.1 (a₁ := fun i => B.val i j) (a₂ := fun i => A i j) hcj
  exact congrFun heq i

end GeometricComparison
#print axioms field_marking_comparison
section FieldEvaluation
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaLegendreComparisonR0177
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
variable {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G)

include hG in
lemma field_evaluation :
    ∃ ev : SchemeHomOver (𝟙 (Base F)) (structureMap F W) ≃ W.toAffine.Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      (∀ n P, ev (G.nsmul (𝟙 _) n P) = n • ev P) ∧
      ∀ P x y, HasCoordinates F W P.val x y →
        ∃ h, ev P = WeierstrassCurve.Affine.Point.some x y h := by
  obtain ⟨ev, hev, _, hcoords⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by simpa only [Category.id_comp, origin] using hG.1 (𝟙 _))
  have ht : Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 (Base F) := by
    exact Spec.map_id (CommRingCat.of F)
  let castSec : SchemeHomOver (𝟙 (Base F)) (structureMap F W) ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F F))) (structureMap F W) :=
    { toFun := fun P => ⟨P.val, P.property.trans ht.symm⟩
      invFun := fun P => ⟨P.val, P.property.trans ht⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hW : W.toProjective.baseChange F = W := WeierstrassCurve.map_id W
  let cW := ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance.castPoint hW
  let e : SchemeHomOver (𝟙 (Base F)) (structureMap F W) ≃ W.toAffine.Point :=
    (castSec.trans (ev F)).trans cW.toEquiv
  have hm (P Q) : e (G.mul (𝟙 _) P Q) = e P + e Q := by
    have hc : castSec (G.mul (𝟙 _) P Q) =
        G.mul (Spec.map (CommRingCat.ofHom (algebraMap F F))) (castSec P) (castSec Q) := by
      apply Subtype.ext
      exact SchemeLocal.mul_val_congr
        { mul := G.mul, one := G.one, inv := G.inv
          mul_assoc := G.mul_assoc, one_mul := G.one_mul, mul_one := G.mul_one
          inv_mul_cancel := G.inv_mul_cancel, mul_comm := hG.2, mul_natural := G.mul_natural }
        ht.symm _ _ _ _ rfl rfl
    change cW (ev F (castSec (G.mul (𝟙 _) P Q))) = _
    rw [hc, hev.1, map_add]
    rfl
  have hz : e (G.one (𝟙 _)) = 0 := by
    have h := hm (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at h
    exact (add_left_cancel (a := e (G.one (𝟙 _))) ((add_zero _).trans h)).symm
  refine ⟨e, hm, ?_, ?_⟩
  · intro n P
    induction n with
    | zero => exact hz
    | succ n ih => rw [G.nsmul_succ, hm, ih, succ_nsmul, add_comm]
  · intro P x y hp
    obtain ⟨_, χ, hχ, hx, hy⟩ := hp
    obtain ⟨h, he⟩ := hcoords F (castSec P) χ hχ
    obtain ⟨h', hc'⟩ :=
      ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance.castPoint_some
        hW _ _ h
    refine ⟨by simpa only [hx, hy] using h', ?_⟩
    exact (congrArg cW he).trans (by simpa only [hx, hy] using hc')

end FieldEvaluation
#print axioms field_evaluation
lemma castPoint_trans {F : Type u} [Field F] [DecidableEq F]
    {V W Z : WeierstrassCurve F} (h : V = W) (h' : W = Z) (P : V.toAffine.Point) :
    ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance.castPoint h'
      (ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance.castPoint h P) =
    ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance.castPoint (h.trans h') P := by
  subst W
  subst Z
  rfl

section BasisTransport
open ArithmeticThetaMarkingR0115
variable {F : Type u} [Field F] [DecidableEq F]
lemma basis_transport {e d : Fin 3 → F}
    (q : (ArithmeticThetaMillerR0114.Curve F e).Point ≃+
      (ArithmeticThetaMillerR0114.Curve F d).Point)
    (b : ArithmeticThetaMarkingR0115.Marking F e) (hb : IsBasis F e b) :
    IsBasis F d (q ∘ b) := by
  have hcoord (v : Fin 2 → ZMod 4) :
      coordinates F d (q ∘ b) v = q (coordinates F e b v) := by
    simp only [coordinates, Function.comp_apply, map_add, map_nsmul]
  refine ⟨fun i => by rw [Function.comp_apply, ← map_nsmul, hb.1, map_zero], ?_, ?_⟩
  · intro v w h
    rw [hcoord, hcoord] at h
    exact hb.2.1 (q.injective h)
  · intro P hP
    have hk : 4 • q.symm P = 0 := by rw [← map_nsmul, hP, map_zero]
    obtain ⟨v, hv⟩ := hb.2.2 (q.symm P) hk
    exact ⟨v, by rw [hcoord, hv, q.apply_symm_apply]⟩
end BasisTransport

section FieldComparison
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaArbitraryFourCharacterR0214
open ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryPhaseMarkingInvariance
open ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance
open ArithmeticThetaMarkingR0115
variable {F : Type u} [Field F] [CharZero F] [DecidableEq F] [Algebra ℚ F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G)

include hG in
lemma affine_field_comparison
    (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel F W G 4 (𝟙 (Base F)))
    (z : F) (hM : MillerPhase F W G M z) (hN : MillerPhase F W G N z)
    (hp : G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) =
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 N.x) (G.nsmul (𝟙 _) 2 N.y)) :
    ∃ A : EvenGroup,
      ArithmeticThetaRelativeFourCharacterR0211.Changes F W G (𝟙 _) M N A.val := by
  obtain ⟨ev, hm, hn, hc⟩ := field_evaluation W G hG
  have hzM := (arbitrary_geometric_phase F W G hG M).2 z hM |>.1
  have hzN := (arbitrary_geometric_phase F W G hG N).2 z hN |>.1
  obtain ⟨heM, e, he, hV, hb⟩ :=
    ArbitraryPhaseMarkingInvariance.phase_comparison W G hG F (RingHom.id F) ev hc M z hzM
  obtain ⟨heN, d, _, hV', hb'⟩ :=
    ArbitraryPhaseMarkingInvariance.phase_comparison W G hG F (RingHom.id F) ev hc N z hzN
  let V := completeChange W • W
  let a := fun i : Fin 2 => completeMap W (ev (![M.x, M.y] i))
  let a' := fun i : Fin 2 => completeMap W (ev (![N.x, N.y] i))
  let b := castPoint hV ∘ a
  let c := castPoint hV ∘ a'
  have hbc : IsBasis F e c := by
    have h := basis_transport (castPoint (hV'.symm.trans hV)) (castPoint hV' ∘ a') hb'
    have eqc : (castPoint (hV'.symm.trans hV)) ∘ (castPoint hV' ∘ a') = c := by
      funext i
      change castPoint (hV'.symm.trans hV) (castPoint hV' (a' i)) = castPoint hV (a' i)
      exact castPoint_trans hV' (hV'.symm.trans hV) (a' i)
    rwa [eqc] at h
  have hphase : phase F e b = phase F e c := by
    rw [← phaseOn_split, ← phaseOn_split, phaseOn_cast, phaseOn_cast]
    exact heM.symm.trans heN
  have heven : 2 • b 0 + 2 • b 1 = 2 • c 0 + 2 • c 1 := by
    have h := congrArg (fun P => castPoint hV (completeMap W (ev P))) hp
    simpa only [hm, hn, map_add, map_nsmul, b, c, a, a', Function.comp_apply, ArithmeticThetaMarkingR0115.act, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  obtain ⟨A, hA, _⟩ := field_marking_comparison e he b c hb hbc hphase heven
  have hinj : Function.Injective (fun P => castPoint hV (completeMap W (ev P))) :=
    (castPoint hV).injective.comp
      ((WeierstrassCurve.Affine.Point.vcFun_rightInverse
        (C := completeChange W) (W := W.toAffine)).injective.comp ev.injective)
  constructor
  case w => exact A
  constructor
  · apply hinj
    have h := congrFun hA 0
    simpa only [hm, hn, map_add, map_nsmul, b, c, a, a', Function.comp_apply, ArithmeticThetaMarkingR0115.act, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  · apply hinj
    have h := congrFun hA 1
    simpa only [hm, hn, map_add, map_nsmul, b, c, a, a', Function.comp_apply, ArithmeticThetaMarkingR0115.act, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end FieldComparison
#print axioms affine_field_comparison
section AffineSpecialization
open ArithmeticThetaRelativeDiscriminantR0171 (baseMap)
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage
open ArithmeticThetaArbitraryFourCharacterR0214

variable {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
/-- Transport combinations through the specified coefficient square and its actual markings. -/
lemma combination_base_change {K : Type u} [CommRing K]
    (V : WeierstrassCurve K) [V.IsElliptic] (H : Law K V) (hH : IsOriginLaw K V H)
    (f : R →+* K) (c : Curve K V ⟶ Curve R W) (hb : IsBaseChange R W G K V H f c)
    (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (Base R)))
    (N : ArithmeticThetaFullLevelCoverR0175.FullLevel K V H 4 (𝟙 (Base K)))
    (hx : N.x.val ≫ c = baseMap R K f ≫ M.x.val)
    (hy : N.y.val ≫ c = baseMap R K f ≫ M.y.val) (i j : ℕ) :
    (H.mul (𝟙 _) (H.nsmul (𝟙 _) i N.x) (H.nsmul (𝟙 _) j N.y)).val ≫ c =
      baseMap R K f ≫ (G.mul (𝟙 _) (G.nsmul (𝟙 _) i M.x) (G.nsmul (𝟙 _) j M.y)).val := by
  have h := congrArg Subtype.val
    (MarkingTransport.point_combination hb hG hH (𝟙 _) N.x N.y i j)
  exact h.trans (Representability.combination_comp R W G (𝟙 _) _ (baseMap R K f)
    (by simp) M.x M.y (MarkingTransport.point hb (𝟙 _) N.x)
    (MarkingTransport.point hb (𝟙 _) N.y) hx.symm hy.symm i j).symm

include hG in
/-- Compare after any field-valued specialization of the original affine base. -/
lemma affine_specialization_comparison
    (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (Base R)))
    (z : R) (hM : MillerPhase R W G M z) (hN : MillerPhase R W G N z)
    (hp : G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) =
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 N.x) (G.nsmul (𝟙 _) 2 N.y))
    (K : Type u) [Field K] [Algebra ℚ K] (f : R →+* K) :
    ∃ A : EvenGroup,
      baseMap R K f ≫ N.x.val = baseMap R K f ≫
        (G.mul (𝟙 _) (G.nsmul (𝟙 _) (A.val 0 0).val M.x)
          (G.nsmul (𝟙 _) (A.val 1 0).val M.y)).val ∧
      baseMap R K f ≫ N.y.val = baseMap R K f ≫
        (G.mul (𝟙 _) (G.nsmul (𝟙 _) (A.val 0 1).val M.x)
          (G.nsmul (𝟙 _) (A.val 1 1).val M.y)).val := by
  classical
  letI : CharZero K := Algebra.charZero_of_charZero ℚ K
  let V := W.map f
  obtain ⟨c, _, hc, hco, _⟩ := NormalFormConstruction.coefficient_comparison W f
  obtain ⟨H, hm, ho⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      f (structureMap R W) (structureMap K V) c hc G
  have hH : IsOriginLaw K V H := by
    constructor
    · intro T t
      apply hc.hom_ext
      · simp only [ho, hG.1, Category.assoc]
        rw [hco]
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (H.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hc.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hb := pointed_base_change G H hG hH f c hc hco
  let up (B : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (Base R))) :
      ArithmeticThetaFullLevelCoverR0175.FullLevel K V H 4 (𝟙 (Base K)) :=
    MarkingTransport.up hb hG hH (BaseChange.restrict B (baseMap R K f) (by simp))
  have ux (B) : (up B).x.val ≫ c = baseMap R K f ≫ B.x.val :=
    MarkingTransport.up_x hb hG hH _
  have uy (B) : (up B).y.val ≫ c = baseMap R K f ≫ B.y.val :=
    MarkingTransport.up_y hb hG hH _
  have combos (B) (i j : ℕ) :=
    combination_base_change W G hG V H hH f c hb B (up B) (ux B) (uy B) i j
  have hphase (B) (hB : MillerPhase R W G B z) : MillerPhase K V H (up B) (f z) := by
    obtain ⟨w, hw, _⟩ := (arbitrary_geometric_phase K V H hH (up B)).1
    have he := arbitrary_phase_base_change R W G hG B K V H hH (up B) f c hb
      ⟨ux B, uy B⟩ z w hB hw
    rwa [he]
  have heven : H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 (up M).x) (H.nsmul (𝟙 _) 2 (up M).y) =
      H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 (up N).x) (H.nsmul (𝟙 _) 2 (up N).y) := by
    apply Subtype.ext
    apply hc.hom_ext
    · rw [combos, combos, hp]
    · exact (H.mul _ _ _).property.trans (H.mul _ _ _).property.symm
  obtain ⟨A, hA⟩ := affine_field_comparison V H hH (up M) (up N) (f z)
    (hphase M hM) (hphase N hN) heven
  refine ⟨A, ?_, ?_⟩
  · rw [← ux N, hA.1, combos]
  · rw [← uy N, hA.2, combos]

end AffineSpecialization
#print axioms affine_specialization_comparison
section AffineLocal
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171 (baseMap)
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaArbitraryFourCharacterR0214

variable {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
lemma affine_local_comparison
    (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (Base R)))
    (z : R) (hM : MillerPhase R W G M z) (hN : MillerPhase R W G N z)
    (hp : G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) =
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 N.x) (G.nsmul (𝟙 _) 2 N.y))
    (s : Base R) : ∃ (A : EvenGroup) (U : (Base R).Opens), s ∈ U ∧
      U.ι ≫ N.x.val = U.ι ≫
        (G.mul (𝟙 _) (G.nsmul (𝟙 _) (A.val 0 0).val M.x)
          (G.nsmul (𝟙 _) (A.val 1 0).val M.y)).val ∧
      U.ι ≫ N.y.val = U.ι ≫
        (G.mul (𝟙 _) (G.nsmul (𝟙 _) (A.val 0 1).val M.x)
          (G.nsmul (𝟙 _) (A.val 1 1).val M.y)).val := by
  let K := s.asIdeal.ResidueField
  let f : R →+* K := algebraMap R K
  letI : Algebra ℚ K := (f.comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨A, hAx, hAy⟩ := affine_specialization_comparison W G hG M N z hM hN hp K f
  obtain ⟨N', hN', _⟩ :=
    (ArithmeticThetaRelativeFourCharacterR0211.relative_marking_action
      R W G hG (Base R) (𝟙 _)).1 M A.val A.property.1
  have hf : baseMap R K f (IsLocalRing.closedPoint K) = s :=
    Set.mem_singleton_iff.mp (PrimeSpectrum.residueField_comap s ▸ Set.mem_range_self _)
  have hx : N.x.val s = N'.x.val s := by
    have h := congrArg (fun g : Base K ⟶ Curve R W => g (IsLocalRing.closedPoint K)) hAx
    change N.x.val (baseMap R K f _) = _ at h
    rw [hf, ← hN'.1] at h
    change N.x.val s = N'.x.val (baseMap R K f (IsLocalRing.closedPoint K)) at h
    rwa [hf] at h
  have hy : N.y.val s = N'.y.val s := by
    have h := congrArg (fun g : Base K ⟶ Curve R W => g (IsLocalRing.closedPoint K)) hAy
    change N.y.val (baseMap R K f _) = _ at h
    rw [hf, ← hN'.2] at h
    change N.y.val s = N'.y.val (baseMap R K f (IsLocalRing.closedPoint K)) at h
    rwa [hf] at h
  obtain ⟨U, hsU, hU⟩ := torsion_sections_locally_equal W G hG N.x N'.x N.killed_x N'.killed_x s hx
  obtain ⟨V, hsV, hV⟩ := torsion_sections_locally_equal W G hG N.y N'.y N.killed_y N'.killed_y s hy
  refine ⟨A, U ⊓ V, ⟨hsU, hsV⟩, ?_, ?_⟩
  · have h := congrArg (fun g => (Base R).homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ g) hU
    simpa only [← Category.assoc, Scheme.homOfLE_ι, hN'.1] using h
  · have h := congrArg (fun g => (Base R).homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ g) hV
    simpa only [← Category.assoc, Scheme.homOfLE_ι, hN'.2] using h
end AffineLocal

/-- Carry equations on an open chart back to an actual open of the original scheme. -/
lemma localWitness_of_open_chart {S T : Scheme.{u}} (E : Family S)
    (M N : FullLevel E 4) (b : T ⟶ S) [IsOpenImmersion b]
    (A : EvenGroup) (x : T)
    (hx : b ≫ N.x.val = b ≫ changedX E M A.val)
    (hy : b ≫ N.y.val = b ≫ changedY E M A.val) :
    LocalWitness E M N (b x) A := by
  refine ⟨b.opensRange, ⟨x, rfl⟩, ?_, ?_⟩
  · have h := congrArg (fun f => b.isoOpensRange.inv ≫ f) hx
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using h
  · have h := congrArg (fun f => b.isoOpensRange.inv ≫ f) hy
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using h

#print axioms affine_local_comparison
#print axioms localWitness_of_open_chart
section GlobalComparison
open ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaSchemeFourCharacterR0215.MarkedAffineTestComparison
open ArithmeticThetaSchemeFourCharacterR0215.SchemePhaseMarkingInvariance
open ArithmeticThetaRelativeKatoR0169
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

lemma test_combination (P : AffineTest E M) (N : FullLevel E 4)
    (L : ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law 4 (𝟙 (Base P.ring)))
    (hx : L.x.val ≫ P.comparison = P.base ≫ N.x.val)
    (hy : L.y.val ≫ P.comparison = P.base ≫ N.y.val) (i j : ℕ) :
    (P.law.mul (𝟙 _) (P.law.nsmul (𝟙 _) i L.x) (P.law.nsmul (𝟙 _) j L.y)).val ≫ P.comparison =
      P.base ≫ (E.law.mul (𝟙 _) (multiple E (𝟙 _) i N.x) (multiple E (𝟙 _) j N.y)).val := by
  have hz : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  have hn (x : SchemeHomOver (𝟙 (Base P.ring)) (family E M P).p)
      (y : SchemeHomOver (𝟙 S) E.p) (h : x.val ≫ P.comparison = P.base ≫ y.val) (n : ℕ) :
      (P.law.nsmul (𝟙 _) n x).val ≫ P.comparison = P.base ≫ (multiple E (𝟙 _) n y).val := by
    rw [← multiple_eq E M P]
    exact CartesianFullMarking.multiple_comp E (family E M P) P.base P.comparison hz P.mul_eq x y h n
  exact CartesianFullMarking.mul_comp E (family E M P) P.base P.comparison P.mul_eq
    _ _ _ _ (hn L.x N.x hx i) (hn L.y N.y hy j)

lemma localWitness_exists (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (N : FullLevel E 4) (z : Γ(S, ⊤)) (hM : MillerPhase E M z) (hN : MillerPhase E N z)
    (hp : ArithmeticThetaUniversalEvaluationR0213.evenPoint E M =
      ArithmeticThetaUniversalEvaluationR0213.evenPoint E N) (s : S) :
    ∃ A : EvenGroup, LocalWitness E M N s A := by
  obtain ⟨P, hP, sP, hsP⟩ := coverage E M k σ s
  letI := hP
  letI := P.elliptic
  have hz : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  let NN := CartesianFullMarking.up E (family E M P) P.base P.comparison P.cartesian hz P.mul_eq 4 N
  let L : ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law 4 (𝟙 (Base P.ring)) :=
    { x := NN.x, y := NN.y
      killed_x := by rw [← multiple_eq E M P]; exact NN.killed_x
      killed_y := by rw [← multiple_eq E M P]; exact NN.killed_y
      avoids := by
        intro i j hij
        have h := NN.avoids i j hij
        rw [multiple_eq, multiple_eq, family_zero] at h
        exact h }
  have hx : L.x.val ≫ P.comparison = P.base ≫ N.x.val :=
    CartesianFullMarking.lift_comp E (family E M P) P.base P.comparison P.cartesian N.x
  have hy : L.y.val ≫ P.comparison = P.base ≫ N.y.val :=
    CartesianFullMarking.lift_comp E (family E M P) P.base P.comparison P.cartesian N.y
  let Q : AffineTest E N :=
    { ring := P.ring, equation := P.equation, elliptic := P.elliptic, law := P.law
      originLaw := P.originLaw, base := P.base, comparison := P.comparison
      cartesian := P.cartesian, zero_eq := P.zero_eq, mul_eq := P.mul_eq
      level := L, x_eq := hx, y_eq := hy }
  have heven : P.law.mul (𝟙 _) (P.law.nsmul (𝟙 _) 2 P.level.x) (P.law.nsmul (𝟙 _) 2 P.level.y) =
      P.law.mul (𝟙 _) (P.law.nsmul (𝟙 _) 2 L.x) (P.law.nsmul (𝟙 _) 2 L.y) := by
    apply Subtype.ext
    apply P.cartesian.hom_ext
    · rw [test_combination E M P M P.level P.x_eq P.y_eq,
        test_combination E M P N L hx hy]
      exact congrArg (fun f => P.base ≫ f) hp
    · exact (P.law.mul _ _ _).property.trans (P.law.mul _ _ _).property.symm
  obtain ⟨A, U, hsU, hUx, hUy⟩ := affine_local_comparison P.equation P.law P.originLaw
    P.level L (affineScalar E M P z) (hM P) (hN Q) heven sP
  refine ⟨A, ?_⟩
  have hx' : (U.ι ≫ P.base) ≫ N.x.val = (U.ι ≫ P.base) ≫ changedX E M A.val := by
    have h := congrArg (fun f => f ≫ P.comparison) hUx
    rw [Category.assoc, hx, Category.assoc,
      test_combination E M P M P.level P.x_eq P.y_eq] at h
    exact h
  have hy' : (U.ι ≫ P.base) ≫ N.y.val = (U.ι ≫ P.base) ≫ changedY E M A.val := by
    have h := congrArg (fun f => f ≫ P.comparison) hUy
    rw [Category.assoc, hy, Category.assoc,
      test_combination E M P M P.level P.x_eq P.y_eq] at h
    exact h
  have h := localWitness_of_open_chart E M N (U.ι ≫ P.base) A ⟨sP, hsU⟩ hx' hy'
  change LocalWitness E M N (P.base sP) A at h
  rwa [hsP] at h

end GlobalComparison
#print axioms localWitness_exists
end ArithmeticThetaEvenMarkingTorsorR0216.LocallyConstantMarkingComparison

namespace ArithmeticThetaEvenMarkingTorsorR0216

/-- Two phase- and characteristic-compatible full markings differ by a unique locally constant even matrix. -/
theorem locally_constant_marking_comparison :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (M N : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (z : S.presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E N z → ArithmeticThetaUniversalEvaluationR0213.evenPoint E M = ArithmeticThetaUniversalEvaluationR0213.evenPoint E N → ∃! g : LocallyConstant S ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup, ArithmeticThetaEvenMarkingTorsorR0216.LocalChange E M N g := by
  intro k _ _ S σ E M N z hM hN hp
  exact LocallyConstantMarkingComparison.glue_localWitness E M N
    (LocallyConstantMarkingComparison.localWitness_exists E M k σ N z hM hN hp)

#print axioms locally_constant_marking_comparison
end ArithmeticThetaEvenMarkingTorsorR0216
