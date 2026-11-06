module

public import FieldSectionImageR0233
public import FinitePullbackSectionDegree

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCyclotomicModularityR0239
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSharpKernelR0195
open ArithmeticThetaFieldImageR0233 ArithmeticThetaPullback

/-- Faithfulness on the prescribed dominant disk over the given field. -/
theorem arithmetic_section_relations :
∀ (k : Type) [Field k] [CharZero k] (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ∀ c : Fin h → k, ArithmeticThetaFieldImageR0233.combination k (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections c = 0 ↔ ArithmeticThetaFieldImageR0233.seriesCombination k A c = 0 := by
  intro k _ _ n h hn hh A hA G c
  classical
  have hN := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 0 < level (commonN A) := Nat.mul_pos (by decide) (pow_pos hN 2)
  letI := G.cover.integral
  letI := G.frame.dominant
  letI : IsDominant G.frame.disk := IsDominant.of_comp (genericInclusion k) G.frame.disk
  letI : NoetherianSpace (Disk k) := inferInstance
  let J := ArithmeticThetaArithmeticFieldR0231.half G
  let M := tensorPower G.cover.space J n
  obtain ⟨hY, _hcurve, _hnormal, _hinv, ⟨ι, ⟨C⟩⟩, _hbound⟩ := G.degree
  letI := hY
  have hM : IsLineBundle G.cover.space M :=
    ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C
  have hp : Function.Injective (pullbackPowerSection G.frame.disk J n) := by
    intro s t hst
    apply ArithmeticThetaDegreeAssembly.pullbackGlobalSection_injective G.frame.disk M hM
    exact (ConcreteCategory.bijective_of_isIso
      ((pullback_tensorPower_iso (Disk k) G.cover.space G.frame.disk J n).hom.app
        (G.frame.disk ⁻¹ᵁ (⊤ : G.cover.space.Opens)))).injective hst
  have hf := ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.tensor_frame
    _ G.frame.frame G.frame.isFrame n
  have hf' : Function.Injective (fun a : Γ(Disk k, ⊤) => a •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback G.frame.disk).obj J) n ⊤
        G.frame.frame) := by
    simpa only [ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.res_self]
      using (hf ⊤ le_rfl).injective
  have hz : pullbackPowerSection G.frame.disk J n 0 = 0 := by
    unfold pullbackPowerSection pullbackGlobalSection
    change ((pullback_tensorPower_iso (Disk k) G.cover.space G.frame.disk J n).hom.app
      (G.frame.disk ⁻¹ᵁ (⊤ : G.cover.space.Opens))).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction G.frame.disk).unit.app
        (tensorPower G.cover.space J n)).app ⊤).hom 0) = 0
    simp only [map_zero]
  have hex := G.expansion c
  constructor
  · intro hs
    have he : ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (ArithmeticThetaArithmeticFieldR0231.expanded k A c) = 0 := by
      apply hf'
      dsimp only
      rw [zero_smul]
      rw [← hex]
      change pullbackPowerSection G.frame.disk J n
        (combination k (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections c) = 0
      rw [hs, hz]
    have he' : ArithmeticThetaArithmeticFieldR0231.expanded k A c = 0 := by
      have he0 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom he
      simpa only [ArithmeticThetaOpenHodgeR0180.scalar, Iso.inv_hom_id_apply,
        map_zero] using he0
    ext m
    have hc := congrArg (PowerSeries.coeff (level (commonN A) * m)) he'
    simpa [ArithmeticThetaArithmeticFieldR0231.expanded, seriesCombination,
      PowerSeries.coeff_subst_X_pow (ne_of_gt hL), Nat.mul_div_right m hL] using hc
  · intro ht
    apply hp
    rw [hz]
    change pullbackPowerSection G.frame.disk J n
      (∑ i, baseScalar k (ArithmeticThetaArithmeticFieldR0231.structureMap G) (c i) •
        G.sections i) = 0
    rw [hex]
    have he : ArithmeticThetaArithmeticFieldR0231.expanded k A c = 0 := by
      change PowerSeries.subst _ (seriesCombination k A c) = 0
      rw [ht]
      ext m
      simp [PowerSeries.coeff_subst_X_pow (ne_of_gt hL)]
    rw [he]
    simp [ArithmeticThetaOpenHodgeR0180.scalar]

/-- All six exact image clauses for the same field-generic compact sections. -/
theorem arithmetic_section_image :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ),
      0 < n → 0 < h → ∀ (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ∀ B : ℕ,
      ArithmeticThetaSharpKernelR0195.cutoff A ≤ B →
      SectionImage k A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro k _ _ n h hn hh A hA G B hB
  classical
  let b := ArithmeticThetaArithmeticFieldR0231.structureMap G
  have hr := arithmetic_section_relations k n h hn hh A hA G
  obtain ⟨hk, hi, hspan, hc, hu⟩ := field_series_image k n h A hA B hB
  have hp (c : Fin h → k) (d : Fin (pivotCount A B) → k) :
      combination k b G.sections c = pivotCombination k A B b G.sections d ↔
        seriesCombination k A c = seriesPivot k A B d := by
    change combination k b G.sections c =
      ∑ t, baseScalar k b (d t) • G.sections (ArithmeticThetaComputed.selectedIndex A B t) ↔ _
    rw [← FieldSectionImageProof.combination_insert,
      FieldSectionImageProof.equality k b G.sections A hr]
    exact congrArg (fun z => seriesCombination k A c = z)
      (FieldSeriesImageProof.inserted k A B d) |>.to_iff
  have hs (j : Fin h) (d : Fin (pivotCount A B) → k) :
      G.sections j = pivotCombination k A B b G.sections d ↔
        ArithmeticThetaArithmeticFieldR0231.theta k (A j) = seriesPivot k A B d := by
    have he := hp (Pi.single j 1) d
    rw [FieldSectionImageProof.combination_single] at he
    change _ ↔ FieldSeriesImageProof.linear k A (Pi.single j 1) = _ at he
    rw [FieldSeriesImageProof.single] at he
    exact he
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hr c).trans (hk c)
  · intro d hd
    apply hi d
    have hz := (hr (FieldSeriesImageProof.insert k
      (ArithmeticThetaComputed.selectedIndex A B) d)).mp (by
        simpa only [FieldSectionImageProof.combination_insert, pivotCombination] using hd)
    change FieldSeriesImageProof.linear k A _ = 0 at hz
    rwa [FieldSeriesImageProof.inserted] at hz
  · intro c
    obtain ⟨d, hd, hud⟩ := hspan c
    exact ⟨d, (hp c d).mpr hd, fun e he => hud e ((hp c e).mp he)⟩
  · intro j
    exact (hs j _).mpr (hc j)
  · intro j d hd
    exact hu j d ((hs j _).mp hd)


#print axioms arithmetic_section_relations
#print axioms arithmetic_section_image
end ArithmeticThetaCyclotomicModularityR0239
