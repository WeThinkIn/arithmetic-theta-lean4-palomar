module

public import ScalarExtensionDiskFrameR0240
public import ScalarExtensionExpansionR0240
public import CertifiedPrefixFieldImageR0240
public import FieldSectionImageR0233

@[expose] public section

/-! Faithful full-series relations and certified pivot images for the literal
pullbacks of the same arithmetic compact sections. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSharpKernelR0195
open ArithmeticThetaFieldImageR0233 ArithmeticThetaPullback

/-- The dominant lifted disk detects exactly all full theta relations over the
extension field, with its actual structural scalar action. -/
theorem scalar_extension_section_relations
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (c : Fin h → l) :
    combination l (structureMap ι G) (sections ι G) c = 0 ↔
      seriesCombination l A c = 0 := by
  classical
  have hN := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 0 < level (commonN A) := Nat.mul_pos (by decide) (pow_pos hN 2)
  have hg := scalar_extension_geometry k l ι n h hn hh A hA G
  letI : GeometricallyIntegral (structureMap ι G) := hg.2.2.2.1
  letI : IsIntegral (Space ι G) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap ι G)
  obtain ⟨D, hframe, hdominant⟩ := scalar_extension_disk_frame k l ι n h hn hh A hA G
  letI := hdominant
  letI : IsDominant D.map := IsDominant.of_comp (genericInclusion l) D.map
  letI : NoetherianSpace (Disk l) := inferInstance
  let J := line ι G
  let M := tensorPower (Space ι G) J n
  have hM : IsLineBundle (Space ι G) M := hg.2.2.2.2.2
  have hp : Function.Injective (pullbackPowerSection D.map J n) := by
    intro s t hst
    apply ArithmeticThetaDegreeAssembly.pullbackGlobalSection_injective D.map M hM
    exact (ConcreteCategory.bijective_of_isIso
      ((pullback_tensorPower_iso (Disk l) (Space ι G) D.map J n).hom.app
        (D.map ⁻¹ᵁ (⊤ : (Space ι G).Opens)))).injective hst
  have hf := ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.tensor_frame
    _ (frame ι G D) hframe n
  have hf' : Function.Injective (fun a : Γ(Disk l, ⊤) => a •
      tensorPowerSection (Disk l) ((Scheme.Modules.pullback D.map).obj J) n ⊤
        (frame ι G D)) := by
    simpa only [ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.res_self]
      using (hf ⊤ le_rfl).injective
  have hz : pullbackPowerSection D.map J n 0 = 0 := by
    unfold pullbackPowerSection pullbackGlobalSection
    change ((pullback_tensorPower_iso (Disk l) (Space ι G) D.map J n).hom.app
      (D.map ⁻¹ᵁ (⊤ : (Space ι G).Opens))).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction D.map).unit.app
        (tensorPower (Space ι G) J n)).app ⊤).hom 0) = 0
    simp only [map_zero]
  have hex := (scalar_extension_expansion k l ι n h hn hh A hA G D) c
  constructor
  · intro hs
    have he : ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries l)
        (ArithmeticThetaArithmeticFieldR0231.expanded l A c) = 0 := by
      apply hf'
      dsimp only
      rw [zero_smul]
      rw [← hex]
      change pullbackPowerSection D.map J n
        (combination l (structureMap ι G) (sections ι G) c) = 0
      rw [hs, hz]
    have he' : ArithmeticThetaArithmeticFieldR0231.expanded l A c = 0 := by
      have he0 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries l))).hom he
      simpa only [ArithmeticThetaOpenHodgeR0180.scalar, Iso.inv_hom_id_apply,
        map_zero] using he0
    ext m
    have hc := congrArg (PowerSeries.coeff (level (commonN A) * m)) he'
    simpa [ArithmeticThetaArithmeticFieldR0231.expanded, seriesCombination,
      PowerSeries.coeff_subst_X_pow (ne_of_gt hL), Nat.mul_div_right m hL] using hc
  · intro ht
    apply hp
    rw [hz]
    change pullbackPowerSection D.map (line ι G) n
      (combination l (structureMap ι G) (sections ι G) c) = 0
    rw [hex]
    have he : ArithmeticThetaArithmeticFieldR0231.expanded l A c = 0 := by
      change PowerSeries.subst _ (seriesCombination l A c) = 0
      rw [ht]
      ext m
      simp [PowerSeries.coeff_subst_X_pow (ne_of_gt hL)]
    rw [he]
    simp [ArithmeticThetaOpenHodgeR0180.scalar]

/-- Every complete prefix certificate gives all six image clauses for the
same pulled-back sections, including certificates below the sharp cutoff. -/
theorem scalar_extension_certified_image
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (B : ℕ)
    (hcert : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin)) :
    SectionImage l A B (structureMap ι G) (sections ι G) := by
  classical
  let b := structureMap ι G
  have hr := scalar_extension_section_relations k l ι n h hn hh A hA G
  obtain ⟨hk, hi, hspan, hc, hu⟩ := certified_prefix_field_image l n h A hA B hcert
  have hp (c : Fin h → l) (d : Fin (pivotCount A B) → l) :
      combination l b (sections ι G) c = pivotCombination l A B b (sections ι G) d ↔
        seriesCombination l A c = seriesPivot l A B d := by
    change combination l b (sections ι G) c =
      ∑ t, baseScalar l b (d t) • (sections ι G) (ArithmeticThetaComputed.selectedIndex A B t) ↔ _
    rw [← FieldSectionImageProof.combination_insert,
      FieldSectionImageProof.equality l b (sections ι G) A hr]
    exact congrArg (fun z => seriesCombination l A c = z)
      (FieldSeriesImageProof.inserted l A B d) |>.to_iff
  have hs (j : Fin h) (d : Fin (pivotCount A B) → l) :
      (sections ι G) j = pivotCombination l A B b (sections ι G) d ↔
        ArithmeticThetaArithmeticFieldR0231.theta l (A j) = seriesPivot l A B d := by
    have he := hp (Pi.single j 1) d
    rw [FieldSectionImageProof.combination_single] at he
    change _ ↔ FieldSeriesImageProof.linear l A (Pi.single j 1) = _ at he
    rw [FieldSeriesImageProof.single] at he
    exact he
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hr c).trans (hk c)
  · intro d hd
    apply hi d
    have hz := (hr (FieldSeriesImageProof.insert l
      (ArithmeticThetaComputed.selectedIndex A B) d)).mp (by
        simpa only [FieldSectionImageProof.combination_insert, pivotCombination] using hd)
    change FieldSeriesImageProof.linear l A _ = 0 at hz
    rwa [FieldSeriesImageProof.inserted] at hz
  · intro c
    obtain ⟨d, hd, hud⟩ := hspan c
    exact ⟨d, (hp c d).mpr hd, fun e he => hud e ((hp c e).mp he)⟩
  · intro j
    exact (hs j _).mpr (hc j)
  · intro j d hd
    exact hu j d ((hs j _).mp hd)


#print axioms scalar_extension_section_relations
#print axioms scalar_extension_certified_image
end ArithmeticThetaScalarExtensionR0240
