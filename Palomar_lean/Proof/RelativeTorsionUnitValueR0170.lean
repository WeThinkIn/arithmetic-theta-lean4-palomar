module

public import RelativeKatoNaturalityDefinitionsR0170
public import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
public import RelativeKatoExistenceR0169

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
namespace TorsionUnitValue
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- Two sections killed by the same unramified separated map cannot meet in a
fiber without agreeing on a connected base. -/
lemma sections_eq_of_meet {S X Y : Scheme.{u}} [PreconnectedSpace S]
    (p : X ⟶ S) (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f] [IsSeparated f]
    (a b : S ⟶ X) (ha : a ≫ p = 𝟙 S) (hb : b ≫ p = 𝟙 S)
    (hf : a ≫ f = b ≫ f) (x y : S) (hxy : a x = b y) : a = b := by
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  letI : Nonempty ↥(pullback a b) := ⟨z⟩
  have he : pullback.fst a b = pullback.snd a b := by
    have H := congrArg (fun k => k ≫ p) (pullback.condition (f := a) (g := b))
    simpa only [Category.assoc, ha, hb, Category.comp_id] using H
  apply eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace f a b hf
    (pullback.fst a b)
  exact (pullback.condition (f := a) (g := b)).trans (congrArg (fun k => k ≫ b) he.symm)

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
  [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
  (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
lemma avoids_torsion (P : Spec (CommRingCat.of R) ⟶ Curve R W)
    (hP : P ≫ structureMap R W = 𝟙 _) (N : ℕ) (hN : 0 < N)
    (hNP : P ≫ G.schemeNsmul N = origin R W) (hne : P ≠ origin R W)
    (c : ℕ) (hcN : Nat.Coprime c N) :
    ∀ x : Spec (CommRingCat.of R),
      G.schemeNsmul c (P x) ∉ Set.range (origin R W) := by
  letI := G.pointGroup (𝟙 (Spec (CommRingCat.of R)))
  let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (structureMap R W) := ⟨P, hP⟩
  have hpow (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (structureMap R W))
      (n : ℕ) : G.nsmul (𝟙 _) n a = a ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih]; rfl
  have hval (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (structureMap R W))
      (n : ℕ) : a.val ≫ G.schemeNsmul n = (a ^ n).val :=
    (comp_schemeNsmul G (𝟙 _) a n).trans (congrArg Subtype.val (hpow a n))
  have hone : (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of R)))
      (structureMap R W)).val = origin R W := by
    change (G.one (𝟙 (Spec (CommRingCat.of R)))).val = origin R W
    exact (hG.1 (𝟙 (Spec (CommRingCat.of R)))).trans (Category.id_comp _)
  have hzN : z ^ N = 1 := Subtype.ext ((hval z N).symm.trans (hNP.trans hone.symm))
  have hz : z ≠ 1 := fun H => hne ((congrArg Subtype.val H).trans hone)
  have hzc : z ^ c ≠ 1 := by
    intro H
    apply hz
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hcN.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one H) (orderOf_dvd_of_pow_eq_one hzN)
  let Q := (z ^ c).val
  have hQ : Q ≫ structureMap R W = 𝟙 _ := (z ^ c).property
  have hQN : Q ≫ G.schemeNsmul N = origin R W := by
    rw [hval (z ^ c) N, pow_right_comm, hzN, one_pow, hone]
  obtain ⟨hFinite, hEtale, _, _⟩ := relative_multiplication_degree R W G hG N hN
  letI := hEtale
  letI := hFinite
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have hQeq : Q = origin R W := sections_eq_of_meet (structureMap R W)
    (G.schemeNsmul N) Q (origin R W) hQ
    (WeierstrassProjModel.kwZeroSect R W).property
    (hQN.trans (RelativeExistence.origin_fixed R W G hG N).symm) x y (by
      change (z ^ c).val x = origin R W y
      rw [← hval z c]
      exact hy.symm)
  exact hzc (Subtype.ext (hQeq.trans hone.symm))

/-- Actual evaluations of one rational function agree after restricting both
regular representatives to the intersection of their neighborhoods. -/
lemma hasValue_unique (P : Spec (CommRingCat.of R) ⟶ Curve R W)
    (g : (Curve R W).functionField) {v w : R}
    (hv : HasValue R W P g v) (hw : HasValue R W P g w) : v = w := by
  obtain ⟨U, hU, eU, a, _, ha, hva⟩ := hv
  obtain ⟨V, hV, eV, b, _, hb, hwb⟩ := hw
  letI := hU
  letI := hV
  let T := U ⊓ V
  have eT : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ T := by
    intro x hx
    exact ⟨eU hx, eV hx⟩
  letI : Nonempty T := ⟨⟨P (genericPoint (Spec (CommRingCat.of R))), eT trivial⟩⟩
  let iU : T ⟶ U := homOfLE inf_le_left
  let iV : T ⟶ V := homOfLE inf_le_right
  have heq : (Curve R W).presheaf.map iU.op a = (Curve R W).presheaf.map iV.op b := by
    apply (Curve R W).germToFunctionField_injective T
    change (Curve R W).presheaf.germ T _ _ _ = (Curve R W).presheaf.germ T _ _ _
    rw [(Curve R W).presheaf.germ_res_apply, (Curve R W).presheaf.germ_res_apply]
    exact ha.trans hb.symm
  have heval : P.appLE U ⊤ eU a = P.appLE V ⊤ eV b := by
    have H := congrArg (fun s => P.appLE T ⊤ eT s) heq
    simpa only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using H
  exact hva.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom heval).trans hwb)

end TorsionUnitValue
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169

/-- Every nonidentity prime-to-c torsion section has a unique unit Kato value. -/
theorem relative_torsion_unit_value :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (P : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of R)) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hP : CategoryTheory.CategoryStruct.comp P (ArithmeticThetaRelativeKatoR0169.structureMap R W) = CategoryTheory.CategoryStruct.id _) (N : ℕ) (hN : 0 < N) (hNP : CategoryTheory.CategoryStruct.comp P (G.schemeNsmul N) = ArithmeticThetaRelativeKatoR0169.origin R W) (hne : P ≠ ArithmeticThetaRelativeKatoR0169.origin R W) (hcN : Nat.Coprime c N), (∀ x : AlgebraicGeometry.Spec (CommRingCat.of R), G.schemeNsmul c (P x) ∉ Set.range (ArithmeticThetaRelativeKatoR0169.origin R W)) ∧ ∃! v : R, IsUnit v ∧ ArithmeticThetaRelativeKatoNaturalityR0170.HasValue R W P g v := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG c hc hc6 g hg P hP N hN hNP hne hcN
  have hav := TorsionUnitValue.avoids_torsion R W G hG P hP N hN hNP hne c hcN
  refine ⟨hav, ?_⟩
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
  letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
  let U : (Curve R W).Opens := (G.schemeNsmul c) ⁻¹ᵁ
    ⟨(Set.range (origin R W))ᶜ, (origin R W).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have e : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U := fun x _ => hav x
  letI : Nonempty U := ⟨⟨P (genericPoint (Spec (CommRingCat.of R))), e trivial⟩⟩
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  have hu := (RelativeExistence.relative_of_generic R W G hG C c hc hc6 g (hg.2 C)).2
  obtain ⟨a, ⟨ha, hau⟩, _⟩ := hu U (fun x hx => hx)
  let v := (Scheme.ΓSpecIso (CommRingCat.of R)).hom (P.appLE U ⊤ e a)
  have hv : HasValue R W P g v := ⟨U, inferInstance, e, a, hau, ha, rfl⟩
  refine ⟨v, ⟨?_, hv⟩, ?_⟩
  · exact (hau.map (P.appLE U ⊤ e).hom).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  · intro w hw
    exact TorsionUnitValue.hasValue_unique R W P g hw.2 hv

#print axioms relative_torsion_unit_value
end ArithmeticThetaRelativeKatoNaturalityR0170

