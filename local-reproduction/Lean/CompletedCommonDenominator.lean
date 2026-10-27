import CompletedParameterInjective

open AlgebraicGeometry CategoryTheory Opposite
universe u
noncomputable section
namespace ArithmeticThetaCompletedCharts

private lemma pow_smul_injective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (t : R)
    (hinj : Function.Injective (fun z : M => t • z)) :
    ∀ n : ℕ, Function.Injective (fun z : M => t ^ n • z) := by
  intro n
  induction n with
  | zero => intro x y h; simpa using h
  | succ n ih =>
      intro x y h
      apply ih
      apply hinj
      simpa [pow_succ', smul_smul] using h

private lemma localized_toLocalized_injective {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (t : R)
    (hinj : Function.Injective (fun z : M => t • z)) :
    Function.Injective
      (LocalizedModule.mkLinearMap (Submonoid.powers t) M) := by
  intro x y hxy
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists
    (Submonoid.powers t) (LocalizedModule.mkLinearMap (Submonoid.powers t) M)).mp hxy
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 t).mp s.2
  have hp : t ^ n • x = t ^ n • y := by
    simpa [Submonoid.smul_def, hn] using hs
  exact (pow_smul_injective t hinj n) hp

private lemma localized_restriction_toLocalized {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (t : R) (h : M →ₗ[R] N) (x : M) :
    IsLocalizedModule.map (Submonoid.powers t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) N) h
      (LocalizedModule.mkLinearMap (Submonoid.powers t) M x) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) N (h x) := by
  simpa only [IsLocalizedModule.mk'_one, LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.map_mk' (Submonoid.powers t)
    (LocalizedModule.mkLinearMap (Submonoid.powers t) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers t) N) h x
      (1 : Submonoid.powers t))

/-- A localized compatible family has a common parameter denominator. -/
theorem completed_common_denominator :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [AlgebraicGeometry.Flat f]
      (C : AlgebraicGeometry.Scheme.OrderedAffineCover X)
      (z : ArithmeticThetaCompletedCharts.LocalizedFamily
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C),
      ArithmeticThetaCompletedCharts.LocalizedCompatible
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C z →
      ∃ (b : ℕ) (w : ArithmeticThetaCompletedCharts.CompletedFamily
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C),
        ArithmeticThetaCompletedCharts.Compatible
          (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C w ∧
        ∀ i : C.ι,
          ArithmeticThetaCompletedCharts.toLocalized
            (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) (w i) =
          (PowerSeries.X : PowerSeries k) ^ b • z i := by
  intro k _ X f _ C z hz
  classical
  by_cases hι : Nonempty C.ι
  · letI : Nonempty C.ι := hι
    let p : ∀ i : C.ι,
        Completed (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) ×
          Submonoid.powers (PowerSeries.X : PowerSeries k) :=
      fun i => Classical.choose (IsLocalizedModule.mk'_surjective
        (Submonoid.powers (PowerSeries.X : PowerSeries k))
        (toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i)) (z i))
    have hp : ∀ i : C.ι,
        IsLocalizedModule.mk'
          (toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i))
          (p i).1 (p i).2 = z i := by
      intro i
      exact Classical.choose_spec (IsLocalizedModule.mk'_surjective
        (Submonoid.powers (PowerSeries.X : PowerSeries k))
        (toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i)) (z i))
    let x : ∀ i : C.ι, Completed (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) :=
      fun i => (p i).1
    let n : C.ι → ℕ := fun i => Classical.choose
      ((Submonoid.mem_powers_iff (p i).2.1 (PowerSeries.X : PowerSeries k)).mp (p i).2.2)
    have hn : ∀ i : C.ι, (PowerSeries.X : PowerSeries k) ^ n i = (p i).2.1 := by
      intro i
      exact Classical.choose_spec
        ((Submonoid.mem_powers_iff (p i).2.1 (PowerSeries.X : PowerSeries k)).mp (p i).2.2)
    have hx : ∀ i : C.ι,
        IsLocalizedModule.mk'
          (toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i))
          (x i) ⟨(PowerSeries.X : PowerSeries k) ^ n i,
            (show (PowerSeries.X : PowerSeries k) ^ n i ∈
              Submonoid.powers (PowerSeries.X : PowerSeries k) from
              Submonoid.pow_mem (Submonoid.powers (PowerSeries.X : PowerSeries k))
                (Submonoid.mem_powers _) (n i))⟩ = z i := by
      intro i
      have heq : (p i).2 = ⟨(PowerSeries.X : PowerSeries k) ^ n i,
          Submonoid.pow_mem (Submonoid.powers (PowerSeries.X : PowerSeries k))
            (Submonoid.mem_powers _) (n i)⟩ := Subtype.ext (hn i).symm
      simpa [x, heq] using hp i
    let b : ℕ := Finset.univ.sup' Finset.univ_nonempty n
    let w : CompletedFamily (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C :=
      fun i => (PowerSeries.X : PowerSeries k) ^ (b - n i) • x i
    have hnle : ∀ i : C.ι, n i ≤ b := by
      intro i
      exact Finset.le_sup' n (Finset.mem_univ i)
    have hrepr : ∀ i : C.ι,
        toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) (x i) =
          (PowerSeries.X : PowerSeries k) ^ n i • z i := by
      intro i
      have h := (IsLocalizedModule.mk'_eq_iff
        (S := Submonoid.powers (PowerSeries.X : PowerSeries k))
        (f := toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i))).mp (hx i)
      simpa [Submonoid.smul_def] using h
    have hpow : ∀ i : C.ι,
        toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) (w i) =
          (PowerSeries.X : PowerSeries k) ^ b • z i := by
      intro i
      have hm : IsLocalizedModule.mk'
          (toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i))
          (w i) (1 : Submonoid.powers (PowerSeries.X : PowerSeries k)) =
          (PowerSeries.X : PowerSeries k) ^ b • z i := by
        apply (IsLocalizedModule.mk'_eq_iff
        (S := Submonoid.powers (PowerSeries.X : PowerSeries k))
        (f := toLocalized (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i))).2
        rw [show w i = (PowerSeries.X : PowerSeries k) ^ (b - n i) • x i from rfl,
          map_smul, hrepr i]
        simp only [one_smul]
        rw [smul_smul]
        rw [← pow_add]
        rw [Nat.sub_add_cancel (hnle i)]
      simpa only [IsLocalizedModule.mk'_one] using hm
    refine ⟨b, w, ?_, hpow⟩
    intro i j
    apply localized_toLocalized_injective
      (PowerSeries.X : PowerSeries k)
      (completed_parameter_injective k X f (C.U i ⊓ C.U j))
    rw [← localized_restriction_toLocalized,
      ← localized_restriction_toLocalized, hpow i, hpow j, map_smul, map_smul]
    simpa [localizedRestriction] using
      congrArg (fun q => (PowerSeries.X : PowerSeries k) ^ b • q) (hz i j)
  · letI : IsEmpty C.ι := not_nonempty_iff.mp hι
    let w : CompletedFamily (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C :=
      fun i => isEmptyElim i
    refine ⟨0, w, ?_, ?_⟩
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i

end ArithmeticThetaCompletedCharts
