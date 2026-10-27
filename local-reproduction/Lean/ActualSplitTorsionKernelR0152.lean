import KatoAnnularDefinitionsR0152
import SplitFiniteMarkedDivisorR0133
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152
namespace ActualSplitTorsionKernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146

lemma torsionIndex_injective (c : ℕ) : Function.Injective (torsionIndex (r := 2*c) c) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [torsionIndex] at this
  omega

lemma marked_killed (k : Type u) [Field k] [CharZero k]
    (c : ℕ) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : Tower k (2*c) hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex (2*c) hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c)
    (ab : Fin c × Fin c) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) p) :
    G.nsmul (𝟙 _) c (pointOver k M (𝟙 _) p hp.1) = G.one (𝟙 _) := by
  apply (marked_exact_torsion k (2*c) hr h3 T (even_two_mul c)
    M hM s hs G hG (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) p hp c).2
  refine ⟨?_, ?_⟩
  · exact ⟨ab.1.val, by dsimp [torsionIndex]; ring⟩
  · have hz : ζ ^ c = 1 := Units.ext (by simpa using hζ.pow_eq_one)
    rw [← pow_mul, Nat.mul_comm ab.2.val c, pow_mul, hz, one_pow]

lemma sections_disjoint {F : Type u} [Field F] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of F)) (a b : Spec (.of F) ⟶ X)
    (ha : a ≫ q = 𝟙 _) (hb : b ≫ q = 𝟙 _) (hne : a ≠ b) :
    Disjoint (Set.range a) (Set.range b) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  haveI : Surjective (pullback.fst a b) := ⟨fun t => ⟨w, Subsingleton.elim _ _⟩⟩
  haveI : Epi (pullback.fst a b) := Flat.epi_of_flat_of_surjective _
  have hfst : pullback.fst a b = pullback.snd a b := by
    have h := congrArg (fun f => f ≫ q) (pullback.condition (f := a) (g := b))
    simpa only [Category.assoc, ha, hb, Category.comp_id] using h
  apply hne
  apply (cancel_epi (pullback.fst a b)).mp
  rw [pullback.condition, hfst]

lemma sigmaSpec_isIso (F : Type u) [Field F] (ι : Type u) [Fintype ι] :
    IsIso (sigmaSpec (fun _ : ι => CommRingCat.of F)) := by
  classical
  let q := sigmaSpec (fun _ : ι => CommRingCat.of F)
  haveI : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : ι => F)).surjective x
    refine ⟨Sigma.ι (fun _ : ι => Spec (.of F)) i y, ?_⟩
    change (Sigma.ι (fun _ : ι => Spec (.of F)) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : ι => Spec (.of F)) i ≫ q =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι => F) i)) from
      ι_sigmaSpec _ i]
    exact hy
  exact (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩

lemma sigma_structure_rank (F : Type u) [Field F] (ι : Type u) [Fintype ι]
    (z : Spec (.of F)) :
    (Sigma.desc (fun _ : ι => 𝟙 (Spec (.of F)))).finrank z = Fintype.card ι := by
  let q := sigmaSpec (fun _ : ι => CommRingCat.of F)
  let b := Spec.map (CommRingCat.ofHom (algebraMap F (ι → F)))
  haveI : IsIso q := sigmaSpec_isIso F ι
  haveI : IsFinite b := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have h : Sigma.desc (fun _ : ι => 𝟙 (Spec (.of F))) = q ≫ b := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc, q, ι_sigmaSpec_assoc, b, ← Spec.map_comp]
    convert (Spec.map_id (CommRingCat.of F)).symm using 1
    congr 1
  rw [h, Scheme.Hom.finrank_comp_left_of_isIso]
  change (Spec.map (CommRingCat.ofHom (algebraMap F (ι → F)))).finrank z = _
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simp

lemma split_fiber {F : Type u} [Field F] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of F)) (f : X ⟶ X) [IsFinite f] [Etale f]
    (e : Spec (.of F) ⟶ X) (he : e ≫ q = 𝟙 _)
    (ι : Type u) [Fintype ι] (p : ι → (Spec (.of F) ⟶ X))
    (hp : ∀ i, p i ≫ q = 𝟙 _) (hinj : Function.Injective p)
    (hkill : ∀ i, p i ≫ f = e)
    (hrank : ∀ x, f.finrank x = Fintype.card ι) :
    e.ker.comap f = ⨅ i, (p i).ker := by
  haveI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id q e he
  haveI (i : ι) : IsClosedImmersion (p i) :=
    isClosedImmersion_of_comp_eq_id q (p i) (hp i)
  let m := Sigma.desc p
  let b := Sigma.desc (fun _ : ι => 𝟙 (Spec (.of F)))
  haveI : Etale b := IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma p
      (fun i j hij => sections_disjoint q (p i) (p j) (hp i) (hp j)
        (fun h => hij (hinj h)))
  have hw : m ≫ f = b ≫ e := by
    apply Sigma.hom_ext
    intro i
    simpa only [m, b, Sigma.ι_desc_assoc, Category.id_comp] using hkill i
  let l := pullback.lift m b hw
  have hl : l ≫ pullback.fst f e = m := pullback.lift_fst _ _ _
  haveI : IsClosedImmersion l := by
    haveI : IsClosedImmersion (l ≫ pullback.fst f e) := by rw [hl]; infer_instance
    exact IsClosedImmersion.of_comp l (pullback.fst f e)
  haveI : IsIso l := by
    apply isIso_of_isClosedImmersion_of_finrank_comp_eq l (pullback.snd f e) b
      (pullback.lift_snd _ _ _)
    intro z
    rw [sigma_structure_rank, Scheme.Hom.finrank_pullback_snd]
    exact (hrank _).symm
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion e f,
    ← Scheme.Hom.ker_comp_of_isIso l, hl,
    ← m.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : ι => Spec (.of F)))]
  congr 1
  funext i
  congr 1
  exact Sigma.ι_desc p i

end ActualSplitTorsionKernel
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open ActualSplitTorsionKernel

/-- The full multiplication kernel is the disjoint union of the actual marked sections. -/
theorem actual_split_torsion_kernel :
    ∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (p : Fin c × Fin c → Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ∀ ab, ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaKatoAnnularR0152.torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) (p ab)), ArithmeticThetaKatoAnnularR0152.SplitKernel k M s hs.1 G p (fun ab => (hp ab).1) := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ p hp
  obtain ⟨hfin, het, _, hdegree⟩ := multiplication_finite_etale_degree
    k (2*c) hr h3 T (even_two_mul c) M hM s hs G hG c (by omega)
  letI := hfin
  letI := het
  suffices H : (genericPoint k M s hs.1).ker.comap (multiplication k M G c) =
      ⨅ ab : ULift.{u} (Fin c × Fin c), (genericPoint k M (p ab.down) (hp ab.down).1).ker by
    simpa only [SplitKernel, iInf_ulift] using H
  apply split_fiber (genericStructure k M) (multiplication k M G c)
    (genericPoint k M s hs.1) (genericPoint_structure k M s hs.1)
    (ULift.{u} (Fin c × Fin c)) (fun ab => genericPoint k M (p ab.down) (hp ab.down).1)
    (fun ab => genericPoint_structure k M (p ab.down) (hp ab.down).1)
  · intro ab ab' hh
    apply ULift.ext
    change genericPoint k M (p ab.down) (hp ab.down).1 =
      genericPoint k M (p ab'.down) (hp ab'.down).1 at hh
    obtain ⟨ab⟩ := ab
    obtain ⟨ab'⟩ := ab'
    have hpoints : pointOver k M (𝟙 _) (p ab) (hp ab).1 =
        pointOver k M (𝟙 _) (p ab') (hp ab').1 := by
      apply Subtype.ext
      simpa only [pointOver, Category.id_comp] using hh
    obtain ⟨hi, hz⟩ := MarkedExactTorsion.labels_eq k M hM (p ab) (p ab')
      (hp ab) (hp ab') hpoints
    apply Prod.ext (torsionIndex_injective c hi)
    apply Fin.ext
    apply hζ.pow_inj ab.2.isLt ab'.2.isLt
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hz
  · rintro ⟨ab⟩
    have ht := marked_killed k c hr h3 T M hM s hs G hG ζ hζ ab (p ab) (hp ab)
    have hh := comp_schemeNsmul G (𝟙 _) (pointOver k M (𝟙 _) (p ab) (hp ab).1) c
    rw [ht, hG.1] at hh
    simpa only [pointOver, Category.id_comp, multiplication, universalPoint,
      WeierstrassProjModel.RelativeGroupLaw.schemeNsmul] using hh
  · intro x
    simpa only [Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin, pow_two] using hdegree x

#print axioms actual_split_torsion_kernel
end ArithmeticThetaKatoAnnularR0152
