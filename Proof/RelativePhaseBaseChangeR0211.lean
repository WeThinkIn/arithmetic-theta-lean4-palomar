module

public import RelativeGeometricPhaseR0211

@[expose] public section

/-! Naturality of the regular geometric phase through the actual Cartesian map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativePhaseBaseChange
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open RelativeAlphaNaturality RelativeGeometricPhase

/-- Both polynomial expressions have weight sixteen. Only the first two doubled
labels enter the normalized tangent formula. -/
lemma polynomial_covariance {F : Type u} [CommRing F]
    (e d : Fin 3 → F) (x y v w : Fin 2 → F) (a r : F)
    (he : ∀ i : Fin 2, e i.castSucc = a^2*d i.castSucc+r)
    (hx : ∀ i, x i = a^2*v i+r) (hy : ∀ i, y i = a^3*w i) :
    numerator e x y = a^16 * numerator d v w ∧
    denominator e x y = a^16 * denominator d v w := by
  have h0 := he 0
  have h1 := he 1
  change e 0 = a^2*d 0+r at h0
  change e 1 = a^2*d 1+r at h1
  simp only [numerator, denominator, tangentNumerator,
    show (0 : Fin 2).castSucc = (0 : Fin 3) from rfl,
    show (1 : Fin 2).castSucc = (1 : Fin 3) from rfl, h0, h1, hx, hy]
  constructor <;> ring

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
lemma phase_formula (M : FullLevel R W G 4 (𝟙 (Base R)))
    (z : R) (hz : GeometricPhase R W G M z)
    (e : Fin 3 → R) (x y : Fin 2 → R) (hc : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F) :
    let Y := fun i => completedY R W (x i) (y i)
    ι (denominator e x Y) ≠ 0 ∧
    ι z = ι (numerator e x Y) / ι (denominator e x Y) := by
  obtain ⟨he, ⟨m, hm, _⟩, _⟩ :=
    (relative_split_fiber_basis R W G hG M).2 e x y hc F ι
  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character F (ι ∘ e) he
  have hp := pairing_formula W G hG M e x y hc F ι m hm D
  exact ⟨hp.1, (hz.2 e x y hc F ι m hm D).trans hp.2⟩

include hG in
/-- Over a field the pointed Cartesian map supplies one actual variable change.
Its chart equations compare both marked points and their doubled labels. -/
lemma field_naturality (M : FullLevel R W G 4 (𝟙 (Base R)))
    (F : Type u) [Field F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (hH : IsOriginLaw F V H) (N : FullLevel F V H 4 (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hM : MarkingCompatible R W G M F V H N ι b)
    (z : R) (w : F) (hz : GeometricPhase R W G M z)
    (hw : GeometricPhase F V H N w) : ι z = w := by
  classical
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  obtain ⟨e, x, y, hc⟩ := hz.1
  obtain ⟨d, v, t, hd⟩ := hw.1
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy⟩ := cartesian_field_chart W V ι b hb.1 hb.2.1
  have hn (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
      (Q : SchemeHomOver (𝟙 (Base F)) (structureMap F V))
      (hPQ : Q.val ≫ b = baseMap R F ι ≫ P.val) (n : ℕ) :
      (H.nsmul (𝟙 _) n Q).val ≫ b = baseMap R F ι ≫ (G.nsmul (𝟙 _) n P).val := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.assoc,hb.2.2,← Category.assoc,hPQ,Category.assoc]
  have h0 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.x N.x hM.1 2)
    _ _ _ _ (hc.1 0) (hd.1 0) (C.u : F) C.r C.s C.t hχx hχy
  have h1 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hM.2 2)
    _ _ _ _ (hc.1 1) (hd.1 1) (C.u : F) C.r C.s C.t hχx hχy
  have hp := coordinate_values_natural W V ι b χ hχ _ _ hM.1
    _ _ _ _ hc.2.2.1 hd.2.2.1 (C.u : F) C.r C.s C.t hχx hχy
  have hq := coordinate_values_natural W V ι b χ hχ _ _ hM.2
    _ _ _ _ hc.2.2.2 hd.2.2.2 (C.u : F) C.r C.s C.t hχx hχy
  have he (i : Fin 2) : ι (e i.castSucc) = (C.u : F)^2*d i.castSucc+C.r := by
    fin_cases i
    · exact h0.1
    · exact h1.1
  have hx (i : Fin 2) : ι (x i) = (C.u : F)^2*v i+C.r := by
    fin_cases i
    · exact hp.1
    · exact hq.1
  have hy (i : Fin 2) : ι (y i) = (C.u : F)^3*t i+(C.u : F)^2*C.s*v i+C.t := by
    fin_cases i
    · exact hp.2
    · exact hq.2
  have hY (i : Fin 2) : ι (completedY R W (x i) (y i)) =
      (C.u : F)^3 * completedY F V (v i) (t i) := by
    rw [completed_y_map, hx, hy, completed_y_variable, hC]
  have hpz := phase_formula W G hG M z hz e x y hc F ι
  have hpw := phase_formula V H hH N w hw d v t hd F (RingHom.id F)
  simp only [RingHom.id_apply] at hpw
  rw [hpz.2, hpw.2, map_numerator, map_denominator]
  obtain ⟨hnum, hden⟩ := polynomial_covariance (ι ∘ e) d (ι ∘ x)
    (fun i => ι (completedY R W (x i) (y i))) v
    (fun i => completedY F V (v i) (t i)) (C.u : F) C.r he hx hY
  dsimp only [Function.comp_def] at hnum hden ⊢
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 16 C.u.ne_zero)]

end RelativePhaseBaseChange
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190

/-- Naturality for arbitrary normal-affine base changes, including noninjective
specializations and changes of Weierstrass presentation. -/
theorem relative_phase_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws), ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs → ∀ (Ms : ArithmeticThetaFullLevelCoverR0175.FullLevel S Ws Gs 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)), ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b → ArithmeticThetaRelativeFourCharacterR0211.MarkingCompatible R W G M S Ws Gs Ms ι b → ∀ (z : R) (zs : S), ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z → ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase S Ws Gs Ms zs → ι z = zs := by
  intro R _ _ _ _ _ W _ G hG M S _ _ _ _ _ V _ H hH N ι b hb hM z zs hz hzs
  classical
  letI := (relative_curve_geometry S V).1
  letI := (relative_curve_geometry S V).2.1
  letI := (relative_curve_geometry S V).2.2.2.1
  letI := (relative_curve_geometry S V).2.2.2.2.1
  obtain ⟨C⟩ := relative_generic_comparison S V H hH
  let K := FractionRing S
  let Z := V.map (algebraMap S K)
  let κ : S →+* K := algebraMap S K
  have hc : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange S V H K Z C.law κ C.map :=
    ⟨C.cartesian,C.origin_eq,C.multiplication_eq⟩
  have hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G K Z C.law (κ.comp ι) (C.map ≫ b) := by
    refine ⟨?_,?_,?_⟩
    · rw [CommRingCat.ofHom_comp,Spec.map_comp]
      exact C.cartesian.paste_horiz hb.1
    · rw [← Category.assoc,hc.2.1,Category.assoc,hb.2.1,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
    · intro n
      rw [← Category.assoc,C.multiplication_eq,Category.assoc,hb.2.2,Category.assoc]
  let B : FullLevel S V H 4 ((𝟙 (Base K)) ≫ baseMap S K κ) :=
    BaseChange.restrict N (baseMap S K κ) (by simp)
  let Nk : FullLevel K Z C.law 4 (𝟙 (Base K)) := BaseChange.up hc hH C.originLaw B
  have hNx : Nk.x.val ≫ C.map = baseMap S K κ ≫ N.x.val := BaseChange.up_x hc hH C.originLaw B
  have hNy : Nk.y.val ≫ C.map = baseMap S K κ ≫ N.y.val := BaseChange.up_y hc hH C.originLaw B
  have hKx : Nk.x.val ≫ (C.map ≫ b) = baseMap R K (κ.comp ι) ≫ M.x.val := by
    rw [← Category.assoc,hNx,Category.assoc,hM.1]
    simp only [baseMap,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  have hKy : Nk.y.val ≫ (C.map ≫ b) = baseMap R K (κ.comp ι) ≫ M.y.val := by
    rw [← Category.assoc,hNy,Category.assoc,hM.2]
    simp only [baseMap,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  obtain ⟨zk, hzk, _⟩ := relative_geometric_phase K Z C.law C.originLaw Nk
  apply IsFractionRing.injective S K
  exact (RelativePhaseBaseChange.field_naturality W G hG M K Z C.law C.originLaw Nk
    (κ.comp ι) (C.map ≫ b) hd ⟨hKx,hKy⟩ z zk hz hzk.1).trans
    (RelativePhaseBaseChange.field_naturality V H hH N K Z C.law C.originLaw Nk
      κ C.map hc ⟨hNx,hNy⟩ zs zk hzs hzk.1).symm

#print axioms relative_phase_base_change
end ArithmeticThetaRelativeFourCharacterR0211
