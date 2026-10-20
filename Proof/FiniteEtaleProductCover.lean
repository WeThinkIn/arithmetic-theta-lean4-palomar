module

public import FiniteEtaleSelectedComponent
import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section

namespace ArithmeticThetaCoverComparison

lemma affine_fiber_rank {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [Flat f]
    [IsFinite f] [IsAffine Y] (x : X) :
    letI := f.appTop.hom.toAlgebra
    let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
    letI : p.asIdeal.IsPrime := p.isPrime
    f.finrank x = Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(Y, ⊤)) := by
  letI := f.appTop.hom.toAlgebra
  letI : Module.Flat Γ(X, ⊤) Γ(Y, ⊤) := f.flat_appTop
  letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := f.finite_appTop
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  letI : p.asIdeal.IsPrime := p.isPrime
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  have hfin : f.finrank x = f.appTop.hom.finrank p := by
    unfold Scheme.Hom.finrank
    change (Limits.pullback.snd f
      (X.affineOpenCover.f (X.affineOpenCover.idx x))).appTop.hom.finrank _ = _
    have hpull := IsPullback.of_hasPullback f
      (X.affineOpenCover.f (X.affineOpenCover.idx x))
    have hpush := isPushout_appTop_of_isPullback hpull
    have hr := CommRingCat.finrank_eq_of_isPushout hpush f.flat_appTop f.finite_appTop
      ((Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))).isoSpec.hom
        (X.affineOpenCover.covers x).choose)
    have heq : PrimeSpectrum.comap
        ((X.affineOpenCover.f (X.affineOpenCover.idx x)).appTop.hom)
        ((Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))).isoSpec.hom
          (X.affineOpenCover.covers x).choose) = p := by
      rw [← AlgebraicGeometry.Spec.map_apply]
      have hn := congrArg (fun z => z (X.affineOpenCover.covers x).choose)
        (Scheme.isoSpec_hom_naturality
          (X.affineOpenCover.f (X.affineOpenCover.idx x)))
      simp only [Scheme.Hom.comp_apply] at hn
      rw [(X.affineOpenCover.covers x).choose_spec] at hn
      exact hn
    rw [heq] at hr
    exact hr
  rw [hfin]
  change Module.rankAtStalk (Γ(Y, ⊤)) p = _
  exact Module.rankAtStalk_eq (M := Γ(Y, ⊤)) p

lemma pushout_rank_product {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D]
    [Algebra C D] [IsScalarTower A B D] [IsScalarTower A C D]
    [Module.Finite A B] [Module.Flat A B] [Module.Finite A C] [Module.Flat A C]
    [h : Algebra.IsPushout A B C D] :
    Module.rankAtStalk (R := A) D = Module.rankAtStalk B * Module.rankAtStalk C := by
  let e : TensorProduct A B C ≃ₐ[B] D := Algebra.IsPushout.equiv A B C D
  let φ : TensorProduct A B C →ₗ[A] D :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw =>
            have hh : e (a • (z + w)) = (algebraMap A D a) • e (z + w) := by
              calc
                e (a • (z + w)) = e (a • z + a • w) := by rw [smul_add]
                _ = e (a • z) + e (a • w) := by rw [map_add]
                _ = (algebraMap A D a) • e z + (algebraMap A D a) • e w := by
                  simpa [Algebra.smul_def] using congrArg₂ (· + ·) hz hw
                _ = (algebraMap A D a) • e (z + w) := by
                  rw [map_add]
                  exact (smul_add _ _ _).symm
            simpa [e, Algebra.smul_def] using hh
        | tmul b c =>
            simp [e, Algebra.IsPushout.equiv_tmul, Algebra.smul_def,
              mul_assoc, IsScalarTower.algebraMap_apply A B D] }
  let eA : TensorProduct A B C ≃ₗ[A] D := LinearEquiv.ofBijective φ e.toRingEquiv.bijective
  calc
    Module.rankAtStalk (R := A) D = Module.rankAtStalk (R := A) (TensorProduct A B C) :=
      (Module.rankAtStalk_eq_of_equiv eA).symm
    _ = _ := Module.rankAtStalk_tensorProduct C

lemma affine_pullback_rank {Y Z X : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ X) [IsFinite f] [Flat f] [IsFinite g] [Flat g] (x : X) :
    (pullback.snd f g ≫ g).finrank x = f.finrank x * g.finrank x := by
  let P := pullback f g
  let r : P ⟶ X := pullback.snd f g ≫ g
  letI : IsAffine P := by dsimp [P]; infer_instance
  have hpb : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback _ _
  have hpush := isPushout_appTop_of_isPullback hpb
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(P, ⊤) := r.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := (pullback.fst f g).appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ(P, ⊤) := (pullback.snd f g).appTop.hom.toAlgebra
  letI : Module.Flat Γ(X, ⊤) Γ(Y, ⊤) := f.flat_appTop
  letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := f.finite_appTop
  letI : Module.Flat Γ(X, ⊤) Γ(Z, ⊤) := g.flat_appTop
  letI : Module.Finite Γ(X, ⊤) Γ(Z, ⊤) := g.finite_appTop
  letI : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ(P, ⊤) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change r.appTop.hom a = _
    have hc : r.appTop = (pullback.fst f g ≫ f).appTop := by
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop (pullback.condition.symm)
    rw [hc]
    rfl
  letI : IsScalarTower Γ(X, ⊤) Γ(Z, ⊤) Γ(P, ⊤) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change r.appTop.hom a = _
    rfl
  letI : IsFinite r := by dsimp [r]; infer_instance
  letI : Flat r := by dsimp [r]; infer_instance
  letI : Module.Flat Γ(X, ⊤) Γ(P, ⊤) := r.flat_appTop
  letI : Module.Finite Γ(X, ⊤) Γ(P, ⊤) := r.finite_appTop
  letI : Algebra.IsPushout Γ(X, ⊤) Γ(Y, ⊤) Γ(Z, ⊤) Γ(P, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have hr : Module.rankAtStalk (R := Γ(X, ⊤)) Γ(P, ⊤) =
      Module.rankAtStalk Γ(Y, ⊤) * Module.rankAtStalk Γ(Z, ⊤) :=
    pushout_rank_product
  rw [affine_fiber_rank r x, affine_fiber_rank f x, affine_fiber_rank g x]
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  change Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(P, ⊤)) =
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(Y, ⊤)) *
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(Z, ⊤))
  rw [← Module.rankAtStalk_eq (M := Γ(P, ⊤)) p,
    ← Module.rankAtStalk_eq (M := Γ(Y, ⊤)) p,
    ← Module.rankAtStalk_eq (M := Γ(Z, ⊤)) p]
  exact congrFun hr p

lemma basechange_product_square {Y Z X U : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) (i : U ⟶ X) :
    let f' := pullback.snd f i
    let g' := pullback.snd g i
    IsPullback
      (pullback.map f' g' f g (pullback.fst f i) (pullback.fst g i) i
        pullback.condition.symm pullback.condition.symm)
      (pullback.snd f' g' ≫ g') (pullback.snd f g ≫ g) i := by
  dsimp only
  let f' := pullback.snd f i
  let g' := pullback.snd g i
  let m := pullback.map f' g' f g (pullback.fst f i) (pullback.fst g i) i
    pullback.condition.symm pullback.condition.symm
  have hc : m ≫ (pullback.snd f g ≫ g) = (pullback.snd f' g' ≫ g') ≫ i := by
    simp [pullback.lift_fst, pullback.lift_snd, pullback.map,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, m, g', Category.assoc,
      pullback.condition]
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hc _ _ _ _)
  · intro c
    let a : c.pt ⟶ pullback f i := pullback.lift
      (c.fst ≫ pullback.fst f g) c.snd (by
        simpa [pullback.lift_fst, pullback.lift_snd, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc,
          pullback.condition] using c.condition)
    let b : c.pt ⟶ pullback g i := pullback.lift
      (c.fst ≫ pullback.snd f g) c.snd (by
        simpa [pullback.lift_fst, pullback.lift_snd, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] using c.condition)
    exact pullback.lift a b (by simp [pullback.lift_fst, pullback.lift_snd, pullback.map,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, a, b, f', g'])
  · intro c
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.map,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, m, Category.assoc]
  · intro c
    simp [pullback.lift_fst, pullback.lift_snd, pullback.map,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, g']
  · intro c k hk₁ hk₂
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa [pullback.lift_fst, pullback.lift_snd, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, m, Category.assoc] using
          congrArg (fun t => t ≫ pullback.fst f g) hk₁
      · simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc]
        change k ≫ pullback.fst f' g' ≫ f' = c.snd
        rw [pullback.condition]
        exact hk₂
    · apply pullback.hom_ext
      · simpa [pullback.lift_fst, pullback.lift_snd, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, m, Category.assoc] using
          congrArg (fun t => t ≫ pullback.snd f g) hk₁
      · simpa [pullback.lift_fst, pullback.lift_snd, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, g'] using hk₂

lemma pullback_rank_product {Y Z X : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    [IsFinite f] [Flat f] [IsFinite g] [Flat g] (x : X) :
    (pullback.snd f g ≫ g).finrank x = f.finrank x * g.finrank x := by
  obtain ⟨R, i, hi, x', rfl⟩ := X.exists_Spec_apply_eq x
  have hcart := basechange_product_square f g i
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hcart,
    ← Scheme.Hom.finrank_pullback_snd f i,
    ← Scheme.Hom.finrank_pullback_snd g i]
  exact affine_pullback_rank (pullback.snd f i) (pullback.snd g i) x'

theorem finite_etale_product_cover :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (s : ℕ) (Y : Fin s → AlgebraicGeometry.Scheme.{u})
      (p : ∀ i, Quiver.Hom (Y i) X) [∀ i, AlgebraicGeometry.IsFinite (p i)]
      [∀ i, AlgebraicGeometry.Etale (p i)] [∀ i, AlgebraicGeometry.Surjective (p i)],
      ∃ (T : AlgebraicGeometry.Scheme.{u}) (q : Quiver.Hom T X) (v : ∀ i, Quiver.Hom T (Y i)),
        AlgebraicGeometry.IsFinite q ∧ AlgebraicGeometry.Etale q ∧ AlgebraicGeometry.Surjective q ∧
        (∀ x : X, AlgebraicGeometry.Scheme.Hom.finrank q x = ∏ i : Fin s,
          AlgebraicGeometry.Scheme.Hom.finrank (p i) x) ∧
        (∀ i, CategoryTheory.CategoryStruct.comp (v i) (p i) = q) ∧
        ∀ (S : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom S X) (a : ∀ i, Quiver.Hom S (Y i)),
          (∀ i, CategoryTheory.CategoryStruct.comp (a i) (p i) = f) →
            ∃! g : Quiver.Hom S T, CategoryTheory.CategoryStruct.comp g q = f ∧
              ∀ i, CategoryTheory.CategoryStruct.comp g (v i) = a i := by
  intro X s
  induction s with
  | zero =>
      intro Y p hfin het hsurj
      letI := hfin
      letI := het
      letI := hsurj
      let q : X ⟶ X := 𝟙 X
      let v : ∀ i : Fin 0, X ⟶ Y i := fun i => Fin.elim0 i
      refine ⟨X, q, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · infer_instance
      · infer_instance
      · infer_instance
      · intro x
        simpa [q] using congrFun (Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X)) x
      · intro i
        exact Fin.elim0 i
      · intro S f a ha
        refine ⟨f, ?_, ?_⟩
        · constructor
          · simp [q]
          · intro i; exact Fin.elim0 i
        · intro g hg
          simpa [q] using hg.1
  | succ s ih =>
      intro Y p hfin het hsurj
      letI := hfin
      letI := het
      letI := hsurj
      let Y' : Fin s → Scheme := fun i => Y i.castSucc
      let p' : ∀ i : Fin s, Y' i ⟶ X := fun i => p i.castSucc
      letI : ∀ i, IsFinite (p' i) := fun i => inferInstance
      letI : ∀ i, Etale (p' i) := fun i => inferInstance
      letI : ∀ i, Surjective (p' i) := fun i => inferInstance
      obtain ⟨T₀, q₀, v₀, hq₀fin, hq₀et, hq₀surj, hq₀rank, hq₀comm, hq₀univ⟩ := ih Y' p'
      let qlast : Y (Fin.last s) ⟶ X := p (Fin.last s)
      let T : Scheme := pullback qlast q₀
      let q : T ⟶ X := pullback.snd qlast q₀ ≫ q₀
      let v : ∀ i : Fin (s + 1), T ⟶ Y i :=
        Fin.lastCases (pullback.fst qlast q₀) (fun i => pullback.snd qlast q₀ ≫ v₀ i)
      haveI : IsFinite q := by dsimp [q]; infer_instance
      haveI : Etale q := by dsimp [q]; infer_instance
      haveI : Surjective q := by dsimp [q]; infer_instance
      refine ⟨T, q, v, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
      · intro x
        dsimp [q]
        rw [pullback_rank_product, hq₀rank, Fin.prod_univ_castSucc]
        simp [p', qlast, mul_comm]
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [v, q] using (pullback.condition (f := qlast) (g := q₀))
        · simp only [v, Fin.lastCases_castSucc, Category.assoc]
          rw [hq₀comm j]
      · intro S f a ha
        obtain ⟨g₀, hg₀, huniq₀⟩ := hq₀univ S f (fun i => a i.castSucc) (fun i => ha i.castSucc)
        let g : S ⟶ T := pullback.lift (a (Fin.last s)) g₀ (by
          rw [ha (Fin.last s), hg₀.1])
        refine ⟨g, ?_, ?_⟩
        · constructor
          · dsimp [g, q]
            rw [pullback.lift_snd_assoc]
            exact hg₀.1
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simpa [g, v] using pullback.lift_fst (f := qlast) (g := q₀)
                (a (Fin.last s)) g₀ _
            · dsimp [g, v]
              rw [Fin.lastCases_castSucc, pullback.lift_snd_assoc]
              exact hg₀.2 j
        · intro g' hg'
          have hglast : g' ≫ pullback.fst qlast q₀ = a (Fin.last s) := by
            simpa [v] using hg'.2 (Fin.last s)
          have heq : g' ≫ pullback.snd qlast q₀ = g₀ := huniq₀ (g' ≫ pullback.snd qlast q₀) (by
            refine ⟨?_, ?_⟩
            · simpa [q, ← Category.assoc] using hg'.1
            · intro i
              simpa [v, ← Category.assoc] using hg'.2 i.castSucc)
          apply pullback.hom_ext
          · simpa [g] using hglast
          · rw [heq]
            simpa [g] using (pullback.lift_snd (f := qlast) (g := q₀)
              (a (Fin.last s)) g₀ _).symm

end ArithmeticThetaCoverComparison
