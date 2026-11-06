module

public import RelativeCyclicQuotientExistenceR0173
public import RelativeTorsionUnitValueR0170
public import PointedRelativeGroupHomR0173

@[expose] public section

/-! Descent of a source lift and its actual unit Kato value. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeIsogenyHodgeR0172 ArithmeticThetaRelativeKatoNaturalityR0170

/-- The same quotient carries the lift to a nowhere-identity torsion section
and the normalized Kato function has a unique unit value along this section. -/
theorem cyclic_quotient_torsion_kato_value :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G n) (V : WeierstrassCurve R) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (hf : ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient R W G P f) [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R V)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R V)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R V)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R V)] (N : ℕ) (hN : 0 < N) (Q : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hQ : ArithmeticThetaRelativeCyclicQuotientR0173.LiftConditions R W G P N Q), CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp Q f.map) (H.schemeNsmul N) = ArithmeticThetaRelativeKatoR0169.origin R V ∧ Disjoint (Set.range (CategoryTheory.CategoryStruct.comp Q f.map)) (Set.range (ArithmeticThetaRelativeKatoR0169.origin R V)) ∧ ∀ (g : (ArithmeticThetaRelativeKatoR0169.Curve R V).functionField), ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R V H (1+12*N) g → ∃! v : R, IsUnit v ∧ ArithmeticThetaRelativeKatoNaturalityR0170.HasValue R V (CategoryTheory.CategoryStruct.comp Q f.map) g v := by
  intro R _ _ _ _ _ W _ G hG n hn P V _ H hH f hf _ _ _ _ N hN Q hQ
  have ho : origin R V ≫ structureMap R V = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R V).property
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsProper (structureMap R V) :=
    WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  haveI : IsClosedImmersion (origin R V ≫ structureMap R V) := by
    rw [ho]; infer_instance
  haveI : IsClosedImmersion (origin R V) :=
    IsClosedImmersion.of_comp _ (structureMap R V)
  have hs (i : Fin n) : multiple R W G P i ≫ structureMap R W = 𝟙 _ := by
    simp only [multiple, Category.assoc, G.schemeNsmul_over, P.over_eq]
  haveI (i : Fin n) : IsClosedImmersion (multiple R W G P i) := by
    haveI : IsClosedImmersion (multiple R W G P i ≫ structureMap R W) := by
      rw [hs]; infer_instance
    exact IsClosedImmersion.of_comp _ (structureMap R W)
  have hk := hf.2.2.2.2
  have hkill (i : Fin n) : multiple R W G P i ≫ f.map = origin R V := by
    have hle : (origin R V).ker ≤ (multiple R W G P i ≫ f.map).ker := by
      rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, hk]
      exact iInf_le _ i
    let a := IsClosedImmersion.lift (origin R V) (multiple R W G P i ≫ f.map) hle
    have ha : a ≫ origin R V = multiple R W G P i ≫ f.map :=
      IsClosedImmersion.lift_fac _ _ _
    have haid : a = 𝟙 _ := by
      have he := congrArg (fun k => k ≫ structureMap R V) ha
      simpa only [Category.assoc, ho, Category.comp_id, f.over_eq, hs] using he
    rw [← ha, haid, Category.id_comp]
  have htor : (Q ≫ f.map) ≫ H.schemeNsmul N = origin R V := by
    obtain ⟨i, hi⟩ := hQ.2.1
    rw [Category.assoc, ← (pointed_relative_group_hom R W G hG V H hH f).2 N,
      ← Category.assoc, hi, hkill]
  have havoid : Disjoint (Set.range (Q ≫ f.map)) (Set.range (origin R V)) := by
    let s (i : Fin n) := multiple R W G P i
    let m : (∐ fun _ : Fin n => Base R) ⟶ Curve R W := Sigma.desc s
    haveI : IsClosedImmersion m :=
      ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
        (fun i j hij => P.disjoint i j hij)
    have hmker : kernelIdeal R W G P = m.ker := by
      rw [← m.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin n => Base R))]
      change (⨅ i, (s i).ker) = _
      congr 1
      funext i
      congr 1
      exact (Sigma.ι_desc s i).symm
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ he
    have hx : Q x ∈ ((origin R V).ker.comap f.map).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change f.map (Q x) ∈ ((origin R V).ker.support : Set (Curve R V))
      rw [Scheme.Hom.support_ker,
        (origin R V).isClosedEmbedding.isClosed_range.closure_eq]
      exact ⟨y, he.symm⟩
    rw [hk, hmker] at hx
    change Q x ∈ (m.ker.support : Set (Curve R W)) at hx
    rw [Scheme.Hom.support_ker,
      m.isClosedEmbedding.isClosed_range.closure_eq] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨i, t, ht⟩ := (sigmaOpenCover (fun _ : Fin n => Base R)).exists_eq z
    have ht' : Sigma.ι (fun _ : Fin n => Base R) i t = z := ht
    have he' : multiple R W G P i t = Q x := by
      calc
        multiple R W G P i t = (Sigma.ι (fun _ : Fin n => Base R) i ≫ m) t := by
          rw [Sigma.ι_desc]
        _ = Q x := by change m (Sigma.ι (fun _ : Fin n => Base R) i t) = Q x; rw [ht', hz]
    exact (Set.disjoint_iff_forall_ne.mp (hQ.2.2 i)) ⟨x, rfl⟩ ⟨t, rfl⟩ he'.symm
  refine ⟨htor, havoid, ?_⟩
  intro g hg
  have hsec : (Q ≫ f.map) ≫ structureMap R V = 𝟙 _ := by
    rw [Category.assoc, f.over_eq, hQ.1]
  have hne : Q ≫ f.map ≠ origin R V := by
    intro he
    have x := genericPoint (Base R)
    exact (Set.disjoint_iff_forall_ne.mp havoid) ⟨x, rfl⟩ ⟨x, rfl⟩
      (congrArg (fun k : Base R ⟶ Curve R V => k x) he)
  have hc : 1 < 1 + 12 * N := by omega
  have hc6 : Nat.Coprime (1 + 12 * N) 6 := by
    simpa [← Nat.mul_assoc] using (Nat.coprime_add_mul_left_left 1 6 (2 * N)).mpr (Nat.coprime_one_left 6)
  have hcN : Nat.Coprime (1 + 12 * N) N := by
    exact (Nat.coprime_add_mul_right_left 1 N 12).mpr (Nat.coprime_one_left N)
  exact (relative_torsion_unit_value R V H hH (1 + 12 * N) hc hc6 g hg
    (Q ≫ f.map) hsec N hN htor hne hcN).2

end ArithmeticThetaRelativeCyclicQuotientR0173
