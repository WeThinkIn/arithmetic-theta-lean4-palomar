module

public import FaithfullyFlatSections
public import ProperFunctionsDefinitions
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace ArithmeticThetaConstantDescent
open ArithmeticThetaProperFunctions
 theorem base_change_constant_naturality
    (K L : Type u) [Field K] [Field L] [Algebra K L] (X : Scheme.{u})
    (f : Scheme.Hom X (Spec (CommRingCat.of K))) (c : K) :
    pullbackSections K L X f (constantMap K X f c) =
      constantMap L (baseChange K L X f) (structureMap K L X f) (algebraMap K L c) := by
  unfold pullbackSections constantMap
  have hΓ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K L))
  have happ :
      f.appTop ≫ (projection K L X f).appTop =
        (fieldMap K L).appTop ≫ (structureMap K L X f).appTop := by
    change (projection K L X f ≫ f).appTop =
      (structureMap K L X f ≫ fieldMap K L).appTop
    rw [pullback.condition]
  have hcomp :
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
        (projection K L X f).appTop).hom =
      ((CommRingCat.ofHom (algebraMap K L) ≫
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (structureMap K L X f).appTop)).hom := by
    rw [← Category.assoc, ← Category.assoc, hΓ, Category.assoc, happ]
    rfl
  exact congrArg (fun g => g c) hcomp

 theorem constant_descends_along_field_extension
    (K L : Type u) [Field K] [Field L] [Algebra K L] (X : Scheme.{u})
    (f : Scheme.Hom X (Spec (CommRingCat.of K))) [Nonempty X] [QuasiCompact f]
    (s : (X.presheaf.obj (Opposite.op ⊤))) (a : L) :
    pullbackSections K L X f s = constantMap L (baseChange K L X f)
      (structureMap K L X f) a → ∃! c : K,
      algebraMap K L c = a ∧ constantMap K X f c = s := by
  letI : Surjective f := ⟨by
    intro y
    let ⟨x⟩ := ‹Nonempty X›
    exact ⟨x, Subsingleton.elim _ _⟩⟩
  letI : Flat f := inferInstance
  intro h
  have hEq : leftOverlapMap X (Spec (CommRingCat.of K)) f s =
      rightOverlapMap X (Spec (CommRingCat.of K)) f s := by
    let Z := pullback (C := Scheme.{u}) f f
    let l : Z ⟶ X := pullback.fst (C := Scheme.{u}) f f
    let r : Z ⟶ X := pullback.snd (C := Scheme.{u}) f f
    let g : Z ⟶ Spec (CommRingCat.of K) := l ≫ f
    let W : Scheme := baseChange K L Z g
    let qZ : W ⟶ Z := projection K L Z g
    let u : W ⟶ baseChange K L X f :=
      pullback.lift (qZ ≫ l) (structureMap K L Z g) (by
        dsimp [qZ, g]
        rw [Category.assoc]
        exact pullback.condition)
    let v : W ⟶ baseChange K L X f :=
      pullback.lift (qZ ≫ r) (structureMap K L Z g) (by
        dsimp [qZ, g]
        rw [Category.assoc, ← pullback.condition]
        exact pullback.condition)
    have hu : u ≫ projection K L X f = qZ ≫ l := by
      dsimp [u]
      rw [pullback.lift_fst]
    have hv : v ≫ projection K L X f = qZ ≫ r := by
      dsimp [v]
      rw [pullback.lift_fst]
    have huS : u ≫ structureMap K L X f = structureMap K L Z g := by
      dsimp [u]
      rw [pullback.lift_snd]
    have hvS : v ≫ structureMap K L X f = structureMap K L Z g := by
      dsimp [v]
      rw [pullback.lift_snd]
    change l.appTop s = r.appTop s
    apply flat_surjective_global_sections_injective W Z qZ
    change (qZ ≫ l).appTop s = (qZ ≫ r).appTop s
    rw [← hu, ← hv]
    change u.appTop ((projection K L X f).appTop s) =
      v.appTop ((projection K L X f).appTop s)
    rw [show (projection K L X f).appTop s =
      constantMap L (baseChange K L X f) (structureMap K L X f) a from h]
    unfold constantMap
    change ((u ≫ structureMap K L X f).appTop) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom a) =
      ((v ≫ structureMap K L X f).appTop) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom a)
    rw [huS, hvS]
  obtain ⟨t, ht, htu⟩ := (fpqc_global_sections_equalizer X (Spec (CommRingCat.of K)) f s).mp hEq
  let c : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom t
  have htc : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c = t := by
    dsimp [c]
    simp
  have hs_c : constantMap K X f c = s := by
    change f.appTop ( (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) = s
    rw [htc, ht]
  have hconst :
      constantMap L (baseChange K L X f) (structureMap K L X f) (algebraMap K L c) =
        constantMap L (baseChange K L X f) (structureMap K L X f) a := by
    calc
      constantMap L (baseChange K L X f) (structureMap K L X f) (algebraMap K L c) =
          pullbackSections K L X f (constantMap K X f c) :=
            (base_change_constant_naturality K L X f c).symm
      _ = pullbackSections K L X f s := by rw [hs_c]
      _ = constantMap L (baseChange K L X f) (structureMap K L X f) a := h
  have hca : algebraMap K L c = a := by
    let q := structureMap K L X f
    have hq := flat_surjective_global_sections_injective
      (baseChange K L X f) (Spec (CommRingCat.of L)) q
    have hconst' : q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (algebraMap K L c)) =
        q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom a) := by
      simpa [q, constantMap] using hconst
    have hq' := hq hconst'
    have hh := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of L)).hom z) hq'
    simpa using hh
  refine ⟨c, ⟨hca, hs_c⟩, ?_⟩
  intro d hd
  have hsec : constantMap K X f d = constantMap K X f c := hd.2.trans hs_c.symm
  have hsec' : f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom d) =
      f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) := by
    simpa [constantMap] using hsec
  have hinv := flat_surjective_global_sections_injective X (Spec (CommRingCat.of K)) f hsec'
  have hh := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of K)).hom z) hinv
  simpa using hh
end ArithmeticThetaConstantDescent
