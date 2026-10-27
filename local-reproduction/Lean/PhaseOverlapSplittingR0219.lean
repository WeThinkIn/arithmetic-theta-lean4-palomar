import PhaseCoverR0218
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219
namespace PhaseOverlapProof
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaPhaseSwitchR0218

variable (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
local notation "P" => phaseSpace k S σ
local notation "p" => phaseProjection k S σ
local notation "w" => phaseValue k S σ

lemma field_sign {F : Type u} [Field F] (a b : Spec (.of F) ⟶ P)
    (hb : a ≫ p = b ≫ p) :
    a = b ∨ a.appTop w = -(b.appTop w) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of F)
  let av : F := e.hom (a.appTop w)
  let bv : F := e.hom (b.appTop w)
  have ha : av ^ 2 = -1 := by
    simpa only [av, map_pow, map_neg, map_one] using
      congrArg (fun z => e.hom (a.appTop z)) (PhaseCoverProof.value_sq k S σ)
  have hb' : bv ^ 2 = -1 := by
    simpa only [bv, map_pow, map_neg, map_one] using
      congrArg (fun z => e.hom (b.appTop z)) (PhaseCoverProof.value_sq k S σ)
  rcases eq_or_eq_neg_of_sq_eq_sq av bv (ha.trans hb'.symm) with h | h
  · left
    apply PhaseCoverProof.hom_ext k S σ hb
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective h
  · right
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    simpa only [map_neg] using h

lemma no_fixed {T : Scheme.{u}} [Nonempty T] (a : T ⟶ P)
    (τ : P ≅ P) (hv : τ.hom.appTop w = -w) : a ≫ τ.hom ≠ a := by
  intro he
  obtain ⟨t⟩ := ‹Nonempty T›
  let F := T.residueField t
  let q := T.fromSpecResidueField t ≫ a
  let e := Scheme.ΓSpecIso F
  let i : k →+* F := e.hom.hom.comp (PhaseCoverProof.coordinates (q ≫ p ≫ σ))
  letI : CharZero F := charZero_of_injective_ringHom i.injective
  let v : F := e.hom (q.appTop w)
  have hs : v^2 = -1 := by
    simpa only [v, map_pow, map_neg, map_one] using
      congrArg (fun z => e.hom (q.appTop z)) (PhaseCoverProof.value_sq k S σ)
  have hq : q ≫ τ.hom = q := by simp only [q, Category.assoc, he]
  have hn : -v = v := by
    have h := congrArg (fun f : Spec F ⟶ P => e.hom (f.appTop w)) hq
    change e.hom (q.appTop (τ.hom.appTop w)) = v at h
    simpa only [hv, map_neg, v] using h
  have h2 : (2 : F) * v = 0 := by linear_combination -hn
  have hz : v = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hz] at hs
  norm_num at hs

def diagonal : P ⟶ pullback p p := pullback.lift (𝟙 P) (𝟙 P) rfl

def graph (τ : P ≅ P) (hb : τ.hom ≫ p = p) : P ⟶ pullback p p :=
  pullback.lift (𝟙 P) τ.hom (by simpa only [Category.id_comp] using hb.symm)

@[simp] lemma diagonal_fst : diagonal k S σ ≫ pullback.fst p p = 𝟙 P :=
  pullback.lift_fst _ _ _
@[simp] lemma diagonal_snd : diagonal k S σ ≫ pullback.snd p p = 𝟙 P :=
  pullback.lift_snd _ _ _
@[simp] lemma graph_fst (τ : P ≅ P) (hb : τ.hom ≫ p = p) :
    graph k S σ τ hb ≫ pullback.fst p p = 𝟙 P := pullback.lift_fst _ _ _
@[simp] lemma graph_snd (τ : P ≅ P) (hb : τ.hom ≫ p = p) :
    graph k S σ τ hb ≫ pullback.snd p p = τ.hom := pullback.lift_snd _ _ _

lemma disjoint (τ : P ≅ P) (hb : τ.hom ≫ p = p) (hv : τ.hom.appTop w = -w) :
    Disjoint (Set.range (diagonal k S σ)) (Set.range (graph k S σ τ hb)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  constructor
  intro t
  let d := diagonal k S σ
  let g := graph k S σ τ hb
  let T := pullback d g
  letI : Nonempty T := ⟨t⟩
  let a : T ⟶ P := pullback.fst d g
  let b : T ⟶ P := pullback.snd d g
  have h := pullback.condition (f := d) (g := g)
  have hab : a = b := by
    simpa only [Category.assoc, d, g, diagonal_fst, graph_fst, Category.comp_id]
      using congrArg (fun f => f ≫ pullback.fst p p) h
  have habτ : a = b ≫ τ.hom := by
    simpa only [Category.assoc, d, g, diagonal_snd, graph_snd, Category.comp_id]
      using congrArg (fun f => f ≫ pullback.snd p p) h
  exact no_fixed k S σ b τ hv (habτ.symm.trans hab)

lemma splitting (τ : P ≅ P) (hb : τ.hom ≫ p = p) (hv : τ.hom.appTop w = -w) :
    IsIso (coprod.desc (diagonal k S σ) (graph k S σ τ hb)) := by
  let d := diagonal k S σ
  let g := graph k S σ τ hb
  let c := coprod.desc d g
  have he : Etale p := (phase_cover k S σ).2.1
  have hf : IsFinite p := (phase_cover k S σ).1
  letI := he
  letI := hf
  haveI : IsOpenImmersion d :=
    (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id (pullback.fst p p) d
      (diagonal_fst k S σ)).1
  haveI : IsOpenImmersion g :=
    (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id (pullback.fst p p) g
      (graph_fst k S σ τ hb)).1
  have hd := disjoint k S σ τ hb hv
  haveI : IsOpenImmersion c := by
    apply IsOpenImmersion.of_openCover_source _ (coprodOpenCover.{u,u} P P)
    · intro x y hxy
      obtain ⟨x | x, rfl⟩ := (coprodMk P P).surjective x
      <;> obtain ⟨y | y, rfl⟩ := (coprodMk P P).surjective y
      · simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, c, coprod.inl_desc] at hxy
        exact congrArg (fun z => coprodMk P P (.inl z)) (d.injective hxy)
      · simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
          c, coprod.inl_desc, coprod.inr_desc] at hxy
        exact (Set.disjoint_iff_forall_ne.mp hd ⟨x, rfl⟩ ⟨y, rfl⟩ hxy).elim
      · simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
          c, coprod.inl_desc, coprod.inr_desc] at hxy
        exact (Set.disjoint_iff_forall_ne.mp hd ⟨y, rfl⟩ ⟨x, rfl⟩ hxy.symm).elim
      · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, c, coprod.inr_desc] at hxy
        exact congrArg (fun z => coprodMk P P (.inr z)) (g.injective hxy)
    · rintro (i | i) <;> dsimp [coprodOpenCover, c] <;>
        simp only [coprod.inl_desc, coprod.inr_desc] <;> infer_instance
  haveI : Surjective c := by
    constructor
    intro t
    let T := pullback p p
    let F := T.residueField t
    let q := T.fromSpecResidueField t
    let a := q ≫ pullback.fst p p
    let b := q ≫ pullback.snd p p
    have hab : a ≫ p = b ≫ p := by simp only [a, b, Category.assoc, pullback.condition]
    have hsign := field_sign k S σ b a hab.symm
    let z : Spec F := Classical.choice inferInstance
    rcases hsign with h | h
    · have hq : a ≫ d = q := by
        apply pullback.hom_ext
        · simp only [Category.assoc, d, diagonal_fst, Category.comp_id]; rfl
        · simpa only [Category.assoc, d, diagonal_snd, Category.comp_id] using h.symm
      refine ⟨(coprod.inl : P ⟶ P ⨿ P) (a z), ?_⟩
      change (coprod.inl ≫ c) (a z) = t
      rw [coprod.inl_desc]
      change (a ≫ d) z = t
      rw [hq]
      exact T.fromSpecResidueField_apply t z
    · have hba : b = a ≫ τ.hom := by
        apply PhaseCoverProof.hom_ext k S σ
        · simpa only [Category.assoc, hb] using hab.symm
        · change b.appTop w = a.appTop (τ.hom.appTop w)
          rw [hv, map_neg]
          exact h
      have hq : a ≫ g = q := by
        apply pullback.hom_ext
        · simp only [Category.assoc, g, graph_fst, Category.comp_id]; rfl
        · simpa only [Category.assoc, g, graph_snd] using hba.symm
      refine ⟨(coprod.inr : P ⟶ P ⨿ P) (a z), ?_⟩
      change (coprod.inr ≫ c) (a z) = t
      rw [coprod.inr_desc]
      change (a ≫ g) z = t
      rw [hq]
      exact T.fromSpecResidueField_apply t z
  exact (isIso_iff_isOpenImmersion_and_surjective c).mpr ⟨inferInstance, inferInstance⟩

end PhaseOverlapProof
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaPhaseSwitchR0218

/-- The entire phase overlap is the diagonal plus the negating graph. -/
theorem phase_overlap_splitting : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (τ : CategoryTheory.Iso (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ)), CategoryTheory.CategoryStruct.comp (τ.hom) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) = ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ → τ.hom.appTop (ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ) = -(ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ) → ∃! c : CategoryTheory.Iso (CategoryTheory.Limits.coprod (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ)) (CategoryTheory.Limits.pullback (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ)), CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.inl) (c.hom)) (CategoryTheory.Limits.pullback.fst (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ)) = CategoryTheory.CategoryStruct.id (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) ∧ CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.inl) (c.hom)) (CategoryTheory.Limits.pullback.snd (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ)) = CategoryTheory.CategoryStruct.id (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) ∧ CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.inr) (c.hom)) (CategoryTheory.Limits.pullback.fst (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ)) = CategoryTheory.CategoryStruct.id (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) ∧ CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.inr) (c.hom)) (CategoryTheory.Limits.pullback.snd (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ)) = τ.hom := by
  intro k _ _ S σ τ hb hv
  let d := PhaseOverlapProof.diagonal k S σ
  let g := PhaseOverlapProof.graph k S σ τ hb
  letI := PhaseOverlapProof.splitting k S σ τ hb hv
  let c := asIso (coprod.desc d g)
  refine ⟨c, ?_, ?_⟩
  · simp only [c, asIso_hom, coprod.inl_desc, coprod.inr_desc,
      d, g, PhaseOverlapProof.diagonal_fst, PhaseOverlapProof.diagonal_snd,
      PhaseOverlapProof.graph_fst, PhaseOverlapProof.graph_snd, and_self]
  · intro e he
    apply Iso.ext
    apply coprod.hom_ext
    · apply pullback.hom_ext
      · simpa only [c, asIso_hom, coprod.inl_desc, d, PhaseOverlapProof.diagonal_fst] using he.1
      · simpa only [c, asIso_hom, coprod.inl_desc, d, PhaseOverlapProof.diagonal_snd] using he.2.1
    · apply pullback.hom_ext
      · simpa only [c, asIso_hom, coprod.inr_desc, g, PhaseOverlapProof.graph_fst] using he.2.2.1
      · simpa only [c, asIso_hom, coprod.inr_desc, g, PhaseOverlapProof.graph_snd] using he.2.2.2

#print axioms phase_overlap_splitting
end ArithmeticThetaPhaseFreeKeyR0219
