import RelativeCyclicQuotientDefinitionsR0173
import RelativeCurveGeometryR0169
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre

/-! Pointed morphisms preserve the actual relative elliptic group laws.
The generic-fiber rigidity theorem is descended using flatness of the source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeIsogenyHodgeR0172

namespace PointedRelativeGroupHom
open GoodReductionJacobian.RelativeGroupLaw

/-- Rigidity on the generic fiber, followed by flat descent of the morphism equality. -/
theorem relative_rigidity {R : Type u} [CommRing R] [IsDomain R]
    {A B : Scheme.{u}} {p : A ⟶ Spec (CommRingCat.of R)}
    {q : B ⟶ Spec (CommRingCat.of R)}
    [Smooth p] [IsProper p] [GeometricallyIntegral p]
    [Smooth q] [IsProper q] [GeometricallyIntegral q]
    (G : GoodReductionJacobian.RelativeGroupLaw R p)
    (H : GoodReductionJacobian.RelativeGroupLaw R q)
    (f : SchemeHomOver p q)
    (hf : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      NeronModelInfra.schemeHomOverComp (G.one t) f = H.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t p) :
    (G.mul t x y).val ≫ f.val =
      (H.mul t (NeronModelInfra.schemeHomOverComp x f)
        (NeronModelInfra.schemeHomOverComp y f)).val := by
  let K := FractionRing R
  let ι := specGenericFibreInclusion R K
  let GK := G.baseChange ι
  let HK := H.baseChange ι
  let fK := NeronSpecialFibreInfra.fibreRestrictAlong ι q p f
  haveI : IsIntegral (pullback p ι) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd p ι)
  haveI : IsIntegral (pullback q ι) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd q ι)
  have hB : GoodReductionJacobian.AbelianSchemePropertyBundle K (pullback.snd q ι) := {
    smooth := inferInstance
    proper := inferInstance
    connectedFibres := fun s => by
      have he : (pullback.snd q ι).base ⁻¹' {s} = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      rw [he]
      exact isConnected_univ
    hasGroupLaw := ⟨HK⟩ }
  have hone : NeronModelInfra.schemeHomOverComp (GK.one (𝟙 _)) fK = HK.one (𝟙 _) := by
    apply (baseChangePointEquiv ι (𝟙 _)).injective
    change baseChangePointToBase ι _ = baseChangePointToBase ι _
    rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_one,
      baseChangePointToBase_one]
    exact hf _
  apply GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre R K H G f
  intro S s a b
  have hm :=
    GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      K GK HK hB fK hone s (baseChangePointOfBase ι a) (baseChangePointOfBase ι b)
  have hm' := congrArg (baseChangePointToBase ι) hm
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_mul,
    baseChangePointToBase_mul, baseChangePointToBase_comp_fibreRestrictAlong,
    baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_ofBase,
    baseChangePointToBase_ofBase] at hm'
  exact congrArg Subtype.val hm'

variable (R : Type u) [CommRing R] (W V : WeierstrassCurve R)
    (G : Law R W) (H : Law R V)
    (hG : IsOriginLaw R W G) (hH : IsOriginLaw R V H)
    (f : PointedMap R W V)

include hG hH

lemma map_one {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R)) :
    mapPoint R W f t (G.one t) = H.one t := by
  apply Subtype.ext
  change (G.one t).val ≫ f.map = (H.one t).val
  rw [hG.1 t, hH.1 t, Category.assoc, f.origin_eq]

/-- The zero case uses pointedness; the successor case uses preservation of addition. -/
lemma map_nsmul (hf : IsGroupHom R W G H f)
    {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (structureMap R W)) (j : ℕ) :
    mapPoint R W f t (G.nsmul t j x) = H.nsmul t j (mapPoint R W f t x) := by
  induction j with
  | zero => exact map_one R W V G H hG hH f t
  | succ j ih =>
    change mapPoint R W f t (G.mul t (G.nsmul t j x) x) =
      H.mul t (H.nsmul t j (mapPoint R W f t x)) (mapPoint R W f t x)
    rw [hf X t, ih]

end PointedRelativeGroupHom

/-- Every pointed relative elliptic morphism is a group morphism and commutes
with all multiplication maps, including the zero map. -/
theorem pointed_relative_group_hom :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (V : WeierstrassCurve R) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V), ArithmeticThetaRelativeCyclicQuotientR0173.IsGroupHom R W G H f ∧ ∀ j : ℕ, CategoryTheory.CategoryStruct.comp (G.schemeNsmul j) f.map = CategoryTheory.CategoryStruct.comp f.map (H.schemeNsmul j) := by
  intro R _ _ _ _ _ W _ G hG V _ H hH f
  have hW := relative_curve_geometry R W
  have hV := relative_curve_geometry R V
  letI := hW.2.2.2.2.2.1
  letI := hW.2.2.2.2.2.2
  letI := hV.2.2.2.2.2.1
  letI := hV.2.2.2.2.2.2
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsProper (structureMap R V) := WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  let g := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G
  let h := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ H
  have hf : IsGroupHom R W G H f := by
    intro X t x y
    apply Subtype.ext
    exact PointedRelativeGroupHom.relative_rigidity g h ⟨f.map, f.over_eq⟩
      (fun t => PointedRelativeGroupHom.map_one R W V G H hG hH f t) t x y
  refine ⟨hf, fun j => ?_⟩
  have hn := congrArg Subtype.val
    (PointedRelativeGroupHom.map_nsmul R W V G H hG hH f hf
      (structureMap R W) WeierstrassProjModel.RelativeGroupLaw.idPoint j)
  change G.schemeNsmul j ≫ f.map = _ at hn
  rw [hn]
  exact (ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul
    H (structureMap R W) ⟨f.map, f.over_eq⟩ j).symm

end ArithmeticThetaRelativeCyclicQuotientR0173
