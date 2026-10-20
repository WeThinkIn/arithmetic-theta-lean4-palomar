module

public import GeometricThetaLiftsDefinitionsR0141

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The geometric inversion lift: preservation of the actual identity divisor
and its ideal-power module. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (idealPullbackIso comap_power)

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma negIndex_zero : negIndex r hr (zeroIndex r hr) = zeroIndex r hr := by
  apply Fin.ext
  simp [negIndex, zeroIndex]

/-- The actual algebraized inversion fixes the marked identity section. -/
lemma inversion_fixes_identity (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) : s ≫ iv.hom = s := by
  have ht := (algebraized_marked_transport k r hr h3 T M hM rot scal iv ha
    (zeroIndex r hr) 1 s hs).2.2
  have ht' : MarkedLift k M (zeroIndex r hr) 1 (s ≫ iv.hom) := by
    simpa only [negIndex_zero, inv_one] using ht
  exact (marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) 1).unique ht' hs

/-- A fixed closed section has an invariant scheme-theoretic kernel ideal. -/
lemma fixed_section_ideal {X B : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s]
    (iv : X ≅ X) (hs : s ≫ iv.hom = s) : s.ker.comap iv.hom = s.ker := by
  apply AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange (b := 𝟙 B)
  exact IsPullback.of_vert_isIso ⟨by simpa using hs⟩

/-- Divisor invariance, including every ideal power, on the proper model. -/
lemma inversion_power_ideal (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) (d : ℕ) :
    (s.ker^d).comap iv.hom = s.ker^d := by
  letI : IsClosedImmersion s :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM s hs.1
  rw [comap_power, fixed_section_ideal s iv
    (inversion_fixes_identity k h3 M hM s hs rot scal iv ha)]

/-- The canonical lift of inversion to the actual ideal-power sheaf. -/
def modelLift (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) (d : ℕ) :
    powerModule k M s d ≅ (Scheme.Modules.pullback iv.hom).obj (powerModule k M s d) :=
  (idealPullbackIso iv.hom (s.ker^d) (s.ker^d)
    (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d)
    (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d)
    (inversion_power_ideal k h3 M hM s hs rot scal iv ha d)).symm

/-- Base change uses the very morphism occurring in the frozen lift type. -/
lemma inversionMap_inclusion (M : Model k T)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    inversionMap k M rot scal iv ha ≫ genericInclusion k M =
      genericInclusion k M ≫ iv.hom := by
  exact pullback.lift_fst _ _ _

def genericLift (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) (d : ℕ) :
    Lift k M s d (inversionMap k M rot scal iv ha) :=
  (Scheme.Modules.pullback (genericInclusion k M)).mapIso
      (modelLift k h3 M hM s hs rot scal iv ha d) ≪≫
    (Scheme.Modules.pullbackComp (genericInclusion k M) iv.hom).app (powerModule k M s d) ≪≫
    (Scheme.Modules.pullbackCongr (inversionMap_inclusion k M rot scal iv ha).symm).app
      (powerModule k M s d) ≪≫
    ((Scheme.Modules.pullbackComp (inversionMap k M rot scal iv ha)
      (genericInclusion k M)).app (powerModule k M s d)).symm

open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140

lemma inversionMap_structure (M : Model k T)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    inversionMap k M rot scal iv ha ≫ genericStructure k M = genericStructure k M := by
  exact pullback.lift_snd _ _ _

lemma inversionMap_sq (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    inversionMap k M rot scal iv ha ≫ inversionMap k M rot scal iv ha = 𝟙 _ := by
  have hiv := (AlgebraizedActionLawsR0137.laws M hM rot scal iv ha).2.2.2.1
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ genericInclusion k M = (𝟙 _) ≫ genericInclusion k M
    rw [Category.assoc, inversionMap_inclusion,
      ← Category.assoc _ (genericInclusion k M) iv.hom, inversionMap_inclusion,
      Category.assoc, hiv, Category.comp_id, Category.id_comp]
  · change (_ ≫ _) ≫ genericStructure k M = (𝟙 _) ≫ genericStructure k M
    simp only [Category.assoc, inversionMap_structure, Category.id_comp]

lemma inversionMap_isIso (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) : IsIso (inversionMap k M rot scal iv ha) :=
  ⟨⟨inversionMap k M rot scal iv ha, inversionMap_sq k M hM rot scal iv ha,
    inversionMap_sq k M hM rot scal iv ha⟩⟩

/-- The canonical section is still an injection on the actual generic fiber. -/
lemma generic_inclusion_realizes (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :
    IdealRealization ((s.ker^d).comap (genericInclusion k M))
      (genericPower k M s d) (restrictDual k M s d (idealInclusion (s.ker^d))) := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  exact pullback_open_realization (genericInclusion k M) _ _ _ (ideal_realization _)

/-- The pointwise combination predicate is equality of actual sheaf morphisms. -/
lemma combines_eq (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (c : Fin m → LaurentSeries k)
    (φ : GenericDual k M s d) (hc : Combines k M s d m b c φ) :
    φ = ∑ ν : Fin m, scale
      ((genericStructure k M).appTop ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv (c ν)))
      (b ν) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [sum_app]
  trans ∑ ν : Fin m, scalarAt k M U (c ν) *
    (show Γ(genericScheme k M, U) from (b ν).app U x)
  · exact hc U x
  · apply Finset.sum_congr rfl
    intro ν _
    exact (scale_app _ (b ν) U x).symm

/-- Agreement on a complete basis determines the whole induced action.
Pullback of scalars is kept explicit, so this lemma does not assume a spurious
linear structure on sheaf pullback. -/
lemma act_ext_of_basis (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (f : genericScheme k M ⟶ genericScheme k M) (e e' : Lift k M s d f)
    (he : ∀ ν, act k M s d f e (b ν) = act k M s d f e' (b ν))
    (φ : GenericDual k M s d) : act k M s d f e φ = act k M s d f e' φ := by
  obtain ⟨c, hc, -⟩ := hb φ
  rw [combines_eq k M s d m b c φ hc]
  change e.hom ≫ pulledInclusion f _ = e'.hom ≫ pulledInclusion f _
  rw [pull_sum, Preadditive.comp_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [pull_scale, scale_precomp, scale_precomp]
  exact congrArg (scale _) (he ν)

/-- A lift over an isomorphism is determined by its action on a complete basis. -/
lemma lift_ext_of_basis (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (f : genericScheme k M ⟶ genericScheme k M) [IsIso f]
    (e e' : Lift k M s d f)
    (he : ∀ ν, act k M s d f e (b ν) = act k M s d f e' (b ν)) : e = e' := by
  let j := restrictDual k M s d (idealInclusion (s.ker^d))
  have hj := generic_inclusion_realizes k M s d
  letI : Mono (pulledInclusion f j) :=
    (pullback_open_realization f _ _ _ hj).1
  apply Iso.ext
  apply (cancel_mono (pulledInclusion f j)).mp
  exact act_ext_of_basis k M s d m b hb f e e' he j

/-- Uniqueness in the frozen theorem follows from the accepted actual theta
basis and geometric cancellation, independently of the existence calculation. -/
lemma reversing_lift_unique (m : ℕ) (hm : 0 < m) (he : Even m)
    {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k TT) (hM : IsModel k TT M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv)
    (e e' : Lift k M s m (inversionMap k M rot scal iv ha))
    (h : Reverses k M s m m hm (inversionMap k M rot scal iv ha) e
      (genericTheta k m hm he M hM s hs))
    (h' : Reverses k M s m m hm (inversionMap k M rot scal iv ha) e'
      (genericTheta k m hm he M hM s hs)) : e = e' := by
  letI := inversionMap_isIso k M hM rot scal iv ha
  exact lift_ext_of_basis k M s m m (genericTheta k m hm he M hM s hs)
    (generic_theta_basis k m hm he TT M hM s hs) _ e e'
    (fun ν => (h ν).trans (h' ν).symm)

namespace Numerators
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaCorrectedGammaR0061

lemma reduction_of (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1 a

omit [CharZero k] in
lemma nodeEquiv_mk (p : MvPolynomial (Fin 2) (PowerSeries k)) :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 p) =
      ArithmeticThetaNodeCharts.quotientMap k p := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

lemma reduction_tau (n : ℕ) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      base k n (ArithmeticThetaInfinitesimalPolygonR0129.parameter k n) := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.C PowerSeries.X))) = _
  rw [reduction_of, nodeEquiv_mk]
  rfl

lemma reduction_cx (n : ℕ) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0))) = _
  rw [reduction_of, nodeEquiv_mk]
  rfl

lemma reduction_cy (n : ℕ) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1))) = _
  rw [reduction_of, nodeEquiv_mk]
  rfl

lemma reduction_kills (n : ℕ) (z : Hat k)
    (hz : z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1)) :
    completedReduction k n z = 0 := by
  change (Classical.choose (finite_stage_completion_comparison k n)) (trunc _ _ n z) = 0
  have hfil : ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) =
      (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^(n+1) := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
      ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  rw [hfil] at hz
  rw [show trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

lemma swap_parameter (n : ℕ) :
    TowerInversionR0137.swap k n (base k n (ArithmeticThetaInfinitesimalPolygonR0129.parameter k n)) =
      base k n (ArithmeticThetaInfinitesimalPolygonR0129.parameter k n) :=
  TowerInversionR0137.swap_base_apply k n _

lemma swap_equation (n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n (equation k r n (Fin.rev i)) = equation k r n i := by
  have h₁ : (Fin.rev i).val = 0 ↔ i.val + 1 = r := by simp only [Fin.rev]; omega
  have h₂ : (Fin.rev i).val + 1 = r ↔ i.val = 0 := by simp only [Fin.rev]; omega
  simp only [equation, h₁, h₂, map_mul, apply_ite, map_sub, map_one,
    TowerInversionR0137.swap_x, TowerInversionR0137.swap_y]
  split_ifs <;> ring

lemma swap_leftTailFactor (n l : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n
      (completedReduction k n (leftTailFactor k r (Fin.rev i).val l)) =
    completedReduction k n (rightTailFactor k r i.val l) := by
  have h₁ : (Fin.rev i).val = 0 ↔ i.val + 1 = r := by simp only [Fin.rev]; omega
  have hexp : r*l + (Fin.rev i).val = r*(l+1)-i.val-1 := by
    simp only [Fin.rev, Nat.mul_add, Nat.mul_one]; omega
  simp only [leftTailFactor, rightTailFactor, h₁]
  split_ifs
  · simp
  · simp only [leftFactor, rightFactor, leftExponent, rightExponent, hexp,
      map_sub, map_mul, map_pow, map_one]
    have ht : completedReduction k n (tau k) = base k n (ArithmeticThetaInfinitesimalPolygonR0129.parameter k n) := reduction_tau k n
    have hx : completedReduction k n (cx k) = coordX k n := reduction_cx k n
    have hy : completedReduction k n (cy k) = coordY k n := reduction_cy k n
    rw [ht, hx, hy, swap_parameter, TowerInversionR0137.swap_x]

lemma swap_rightTailFactor (n l : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n
      (completedReduction k n (rightTailFactor k r (Fin.rev i).val l)) =
    completedReduction k n (leftTailFactor k r i.val l) := by
  have h := congrArg (TowerInversionR0137.swap k n) (swap_leftTailFactor k n l (Fin.rev i))
  have hs (a : A k n) : TowerInversionR0137.swap k n (TowerInversionR0137.swap k n a) = a :=
    RingHom.congr_fun (TowerInversionR0137.swap_sq k n) a
  simpa only [Fin.rev_rev, hs] using h.symm

/-- Inversion interchanges the two tails at every finite cutoff. -/
lemma swap_tailPartial (n N : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n
      (completedReduction k n (tailPartial k r (Fin.rev i).val N)) =
    completedReduction k n (tailPartial k r i.val N) := by
  simp only [tailPartial, map_mul, map_prod, swap_leftTailFactor, swap_rightTailFactor]
  exact mul_comm _ _

/-- The actual chosen gamma-tail units obey inversion, at every thickness. -/
lemma swap_gammaTail (n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n
      (completedReduction k n (gammaTail k r hr (Fin.rev i))) =
    completedReduction k n (gammaTail k r hr i) := by
  have hlim (j : Fin r) : Converges k r j.val (tailPartial k r j.val)
      (gammaTail k r hr j) := by
    have hval : (gammaTail k r hr j : Hat k) =
        Classical.choose (gamma_tail_exists k r j.val hr j.isLt) := IsUnit.unit_spec _
    rw [hval]
    exact (Classical.choose_spec (gamma_tail_exists k r j.val hr j.isLt)).2
  obtain ⟨N, hN⟩ := hlim i (n+1)
  obtain ⟨P, hP⟩ := hlim (Fin.rev i) (n+1)
  have h₁ := reduction_kills k n _ (hN (max N P) (le_max_left _ _))
  have h₂ := reduction_kills k n _ (hP (max N P) (le_max_right _ _))
  rw [map_sub, sub_eq_zero] at h₁ h₂
  rw [h₁, h₂, swap_tailPartial]

end Numerators

namespace Weighted
open ArithmeticThetaScaledAnnularR0050

def ex (m j : ℕ) (b : ℤ) : ℕ :=
  (2*m)^2 - thetaShift 1 j + j*(m/2) + (thetaExponent 1 1 j b).toNat + m/2 + b.toNat

def ey (m j : ℕ) (b : ℤ) : ℕ :=
  (2*m)^2 - thetaShift 1 j + j*(m/2) + (thetaExponent 1 1 j b).toNat + (-b).toNat

lemma shift_le (m j : ℕ) (hj : j < 2*m) : thetaShift 1 j ≤ (2*m)^2 := by
  dsimp [thetaShift]
  nlinarith

lemma ex_cast (m j : ℕ) (hj : j < 2*m) (b : ℤ) :
    (ex m j b : ℤ) = (2*(m : ℤ))^2 + (j : ℤ)*(m/2 : ℕ) + b^2 +
      ((j : ℤ)+1)*b + (m/2 : ℕ) := by
  have hE := (theta_exponent_control 1 1 j (by decide) (by decide)).1 b
  dsimp only [ex]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add,
    Nat.cast_sub (shift_le m j hj), Int.toNat_of_nonneg hE]
  by_cases hb : 0 ≤ b
  · simp only [thetaExponent, if_pos hb, Int.toNat_of_nonneg hb,
      Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    ring
  · rw [Int.toNat_eq_zero.mpr (by omega : b ≤ 0)]
    simp only [thetaExponent, if_neg hb, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring

lemma ey_cast (m j : ℕ) (hj : j < 2*m) (b : ℤ) :
    (ey m j b : ℤ) = (2*(m : ℤ))^2 + (j : ℤ)*(m/2 : ℕ) + b^2 + (j : ℤ)*b := by
  have hE := (theta_exponent_control 1 1 j (by decide) (by decide)).1 b
  dsimp only [ey]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add,
    Nat.cast_sub (shift_le m j hj), Int.toNat_of_nonneg hE]
  by_cases hb : 0 ≤ b
  · rw [Int.toNat_eq_zero.mpr (by omega : -b ≤ 0)]
    simp only [thetaExponent, if_pos hb, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring
  · rw [Int.toNat_of_nonneg (by omega : 0 ≤ -b)]
    simp only [thetaExponent, if_neg hb, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    ring

lemma ex_rev (m : ℕ) (he : Even m) (j : Fin (2*m)) (b : ℤ) :
    ex m j.val b = ey m (Fin.rev j).val (-b-m) := by
  apply Nat.cast_injective (R := ℤ)
  rw [ex_cast m j.val j.isLt, ey_cast m (Fin.rev j).val (Fin.rev j).isLt]
  have hrev : ((Fin.rev j).val : ℤ) = 2*(m : ℤ)-1-j.val := by
    simp only [Fin.rev]; omega
  have hm : 2*(m/2 : ℕ) = m := Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  have hm' : (m : ℤ) = 2*(m/2 : ℕ) := by exact_mod_cast hm.symm
  rw [hrev, hm']
  ring

lemma ey_rev (m : ℕ) (he : Even m) (j : Fin (2*m)) (b : ℤ) :
    ey m j.val b = ex m (Fin.rev j).val (-b-m) := by
  have h := ex_rev m he (Fin.rev j) (-b-m)
  rw [show -(-b-(m : ℤ))-(m : ℤ) = b by ring] at h
  simpa only [Fin.rev_rev] using h.symm

def term {R : Type*} [CommRing R] (m j : ℕ) (b : ℤ) (x y : R) : R :=
  (x*y)^((2*m)^2-thetaShift 1 j) *
    ((x*y)^(j*(m/2)) * x^(m/2) *
      ((x*y)^(thetaExponent 1 1 j b).toNat *
        (if 0 ≤ b then x^b.toNat else y^(-b).toNat)))

lemma term_eq {R : Type*} [CommRing R] (m j : ℕ) (b : ℤ) (x y : R) :
    term m j b x y = x^(ex m j b) * y^(ey m j b) := by
  by_cases hb : 0 ≤ b
  · simp only [term, if_pos hb, ex, ey, Int.toNat_eq_zero.mpr (by omega : -b ≤ 0),
      pow_add, mul_pow, pow_zero, mul_one]
    ring
  · simp only [term, if_neg hb, ex, ey, Int.toNat_eq_zero.mpr (by omega : b ≤ 0),
      pow_add, mul_pow, pow_zero, mul_one]
    ring

/-- The complete inversion phase is already exact term by term after the
integer substitution b ↦ -b-m. No horizontal factor is inverted. -/
lemma term_rev {R : Type*} [CommRing R] (m : ℕ) (he : Even m)
    (j : Fin (2*m)) (b : ℤ) (x y : R) :
    term m j.val b x y = term m (Fin.rev j).val (-b-m) y x := by
  rw [term_eq, term_eq, ex_rev m he j b, ey_rev m he j b]
  exact mul_comm _ _

end Weighted

namespace Numerators
open ArithmeticThetaScaledAnnularR0050

def weight (m j : ℕ) : Hat k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ ((2*m)^2-thetaShift 1 j) *
    (ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (j*(m/2)) *
      ArithmeticThetaAnnularTorsionPrereqR0053.cx k ^ (m/2))

lemma term_reduction (m j n : ℕ) (b : ℤ) :
    Weighted.term m j b (coordX k n) (coordY k n) =
      completedReduction k n (weight k m j * thetaTerm k 1 1 j b) := by
  have ht : completedReduction k n (tau k 1) =
      coordX k n * coordY k n :=
    (reduction_tau k n).trans (ArithmeticThetaInfinitesimalPolygonR0129.coordX_mul_coordY k n).symm
  have hx : completedReduction k n (cx k 1) = coordX k n := reduction_cx k n
  have hy : completedReduction k n (cy k 1) = coordY k n := reduction_cy k n
  change _ = completedReduction k n
    ((tau k 1 ^ ((2*m)^2-thetaShift 1 j) *
      (tau k 1 ^ (j*(m/2)) * cx k 1 ^ (m/2))) * thetaTerm k 1 1 j b)
  by_cases hb : 0 ≤ b
  · simp only [Weighted.term, thetaTerm, if_pos hb, map_mul, map_pow, ht, hx]
    ring
  · simp only [Weighted.term, thetaTerm, if_neg hb, map_mul, map_pow, ht, hx, hy]
    ring

lemma term_tail (m j n : ℕ) (b : ℤ)
    (hb : b < -((n+1+2*(j+1)+1 : ℕ) : ℤ) ∨ ((n+1+2*(j+1)+1 : ℕ) : ℤ) < b) :
    Weighted.term m j b (coordX k n) (coordY k n) = 0 := by
  rw [term_reduction, map_mul]
  have hz := reduction_kills k n (thetaTerm k 1 1 j b)
    (theta_term_tail k 1 1 j (n+1) (by decide) (by decide) b (by simpa only [one_mul] using hb))
  rw [hz, mul_zero]

def weightedPartial (m j n : ℕ) (ν : Fin m) (N : ℕ) : A k n :=
  ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then
      Weighted.term m j b (coordX k n) (coordY k n) else 0

lemma weighted_theta_reduction (m : ℕ) (hm : 0 < m) (he : Even m)
    (j n : ℕ) (ν : Fin m) (N : ℕ) (hN : n+1+2*(j+1)+1 ≤ N) :
    completedReduction k n (weight k m j *
      ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he j ν) = weightedPartial k m j n ν N := by
  have h := (Classical.choose_spec (theta_completed_limit k 1 m 1 j (ν.val : ℤ)
    (by decide) hm he (by decide))).1 (n+1) N (by simpa only [one_mul] using hN)
  have hz := reduction_kills k n _ h
  rw [map_sub, sub_eq_zero] at hz
  change completedReduction k n (ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he j ν) =
    completedReduction k n (thetaPartial k 1 m 1 j (ν.val : ℤ) N) at hz
  rw [map_mul, hz]
  simp only [thetaPartial, weightedPartial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hb
  · rw [← map_mul, term_reduction]
  · rw [map_zero, mul_zero]

lemma neg_residue (m : ℕ) (hm : 0 < m) (ν : Fin m) (b : ℤ) :
    b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) ↔
      (-b-m) % (m : ℤ) = ((negIndex m hm ν).val : ℤ) % (m : ℤ) := by
  have hν : ((negIndex m hm ν).val : ℤ) = (-(ν.val : ℤ)) % (m : ℤ) := by
    simp only [negIndex, Int.natCast_mod, Int.ofNat_sub (Nat.le_of_lt ν.isLt)]
    exact Int.neg_emod_eq_sub_emod.symm
  rw [hν, Int.emod_emod, Int.sub_emod_right]
  constructor
  · exact Int.ModEq.neg
  · intro h
    have hh := Int.ModEq.neg h
    change Int.ModEq (m : ℤ) b (ν.val : ℤ)
    simpa only [neg_neg] using hh

lemma partial_swap (m : ℕ) (hm : 0 < m) (he : Even m)
    (j : Fin (2*m)) (n : ℕ) (ν : Fin m) :
    TowerInversionR0137.swap k n (weightedPartial k m (Fin.rev j).val n ν (n+1+4*m+1+m)) =
      weightedPartial k m j.val n (negIndex m hm ν) (n+1+4*m+1+m) := by
  classical
  let N := n+1+4*m+1+m
  let B := n+1+4*m+1
  let f (b : ℤ) : A k n := if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then
    Weighted.term m (Fin.rev j).val b (coordY k n) (coordX k n) else 0
  let g (b : ℤ) : A k n := if b % (m : ℤ) = ((negIndex m hm ν).val : ℤ) % (m : ℤ) then
    Weighted.term m j.val b (coordX k n) (coordY k n) else 0
  have heq (b : ℤ) : f b = g (-b-m) := by
    dsimp only [f, g]
    simp only [← neg_residue m hm ν b]
    split_ifs
    · simpa only [Fin.rev_rev] using Weighted.term_rev m he (Fin.rev j) b (coordY k n) (coordX k n)
    · rfl
  have hfbound (b : ℤ) (hb : f b ≠ 0) : -(B : ℤ) ≤ b ∧ b ≤ B := by
    have ht : n+1+2*((Fin.rev j).val+1)+1 ≤ B := by dsimp [B]; have := (Fin.rev j).isLt; omega
    by_contra h
    have hz := term_tail k m (Fin.rev j).val n b (by push Not at h; omega)
    have hzz := congrArg (TowerInversionR0137.swap k n) hz
    have hswap : TowerInversionR0137.swap k n
        (Weighted.term m (Fin.rev j).val b (coordX k n) (coordY k n)) =
        Weighted.term m (Fin.rev j).val b (coordY k n) (coordX k n) := by
      rw [Weighted.term_eq, Weighted.term_eq]
      simp only [map_mul, map_pow, TowerInversionR0137.swap_x, TowerInversionR0137.swap_y]
    rw [hswap, map_zero] at hzz
    exact hb (by simp only [f, hzz, ite_self])
  have hgbound (b : ℤ) (hb : g b ≠ 0) : -(B : ℤ) ≤ b ∧ b ≤ B := by
    have ht : n+1+2*(j.val+1)+1 ≤ B := by dsimp [B]; have := j.isLt; omega
    by_contra h
    have hz := term_tail k m j.val n b (by push Not at h; omega)
    exact hb (by simp only [g, hz, ite_self])
  have hsum : (∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f b) =
      ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g b := by
    apply Finset.sum_bij_ne_zero (fun (b : ℤ) _ _ => -b-(m : ℤ))
    · intro b hb hne
      have hh := hfbound b hne
      simp only [Finset.mem_Icc]
      dsimp [N, B] at *
      constructor <;> omega
    · intro b hb hne c hc hne' heq
      omega
    · intro b hb hne
      have hh := hgbound b hne
      have hbb : -(-b-(m : ℤ))-(m : ℤ) = b := by ring
      refine ⟨-b-m, ?_, ?_, hbb⟩
      · simp only [Finset.mem_Icc]
        dsimp [N, B] at *
        constructor <;> omega
      · rw [heq, hbb]
        exact hne
    · intro b _ _
      exact heq b
  change TowerInversionR0137.swap k n (weightedPartial k m (Fin.rev j).val n ν N) = weightedPartial k m j.val n (negIndex m hm ν) N
  rw [weightedPartial, map_sum]
  trans ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f b
  · apply Finset.sum_congr rfl
    intro b _
    dsimp only [f]
    split_ifs <;> simp only [map_zero, Weighted.term_eq, map_mul, map_pow,
      TowerInversionR0137.swap_x, TowerInversionR0137.swap_y]
  · exact hsum

lemma numerator_basis (m : ℕ) (hm : 0 < m) (he : Even m) (i : Fin (2*m)) (ν : Fin m) :
    thetaNumerator k m hm he (thetaVector k m ν) i =
      (weight k m i.val * ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he i.val ν) *
        (↑((gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹) : Hat k)^m := by
  classical
  have hc : ArithmeticThetaAnnularThetaR0128.combine k m hm he i.val (thetaVector k m ν) =
      ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he i.val ν := by
    simp [ArithmeticThetaAnnularThetaR0128.combine, thetaVector]
  simp only [thetaNumerator, ArithmeticThetaAnnularThetaR0128.uniformSection, hc,
    ArithmeticThetaAnnularThetaR0128.commonShift, ArithmeticThetaAnnularThetaR0128.shift, weight]
  ring

lemma swap_gammaTail_inv (n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n
      (completedReduction k n (↑((gammaTail k r hr (Fin.rev i))⁻¹) : Hat k)) =
    completedReduction k n (↑((gammaTail k r hr i)⁻¹) : Hat k) := by
  have hu : Units.map (TowerInversionR0137.swap k n).toMonoidHom
      (Units.map (completedReduction k n).toMonoidHom (gammaTail k r hr (Fin.rev i))) =
      Units.map (completedReduction k n).toMonoidHom (gammaTail k r hr i) :=
    Units.ext (swap_gammaTail k n i)
  exact congrArg (fun v : (A k n)ˣ => (↑v⁻¹ : A k n)) hu

/-- Exact residue reversal of the full theta numerators, with the complete
gamma-tail units and the same vertical clearing power. -/
lemma swap_finiteNumerator (m : ℕ) (hm : 0 < m) (he : Even m)
    (n : ℕ) (i : Fin (2*m)) (ν : Fin m) :
    TowerInversionR0137.swap k n (finiteNumerator k m hm he (thetaVector k m ν) n (Fin.rev i)) =
      finiteNumerator k m hm he (thetaVector k m (negIndex m hm ν)) n i := by
  have hc (j : Fin (2*m)) : n+1+2*(j.val+1)+1 ≤ n+1+4*m+1+m := by
    have := j.isLt
    omega
  simp only [finiteNumerator, numerator_basis, map_mul, map_pow, swap_gammaTail_inv]
  congr 1
  rw [← map_mul, ← map_mul, ← map_mul,
    weighted_theta_reduction k m hm he (Fin.rev i).val n ν _ (hc (Fin.rev i)),
    weighted_theta_reduction k m hm he i.val n (negIndex m hm ν) _ (hc i)]
  exact partial_swap k m hm he i n ν

end Numerators

end ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141

namespace ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (witness_iso pull_witness idealPullbackIso_inclusion)

/-- Transport of an actual sheaf lift through a commuting square. -/
def baseChangedLift {X X' Y : Scheme.{u}} (c : X ⟶ Y) (c' : X' ⟶ Y)
    (f : X ⟶ X') (v : Y ⟶ Y) (h : c ≫ v = f ≫ c')
    (L : Y.Modules) (e : L ≅ (Scheme.Modules.pullback v).obj L) :
    (Scheme.Modules.pullback c).obj L ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback c').obj L) :=
  (Scheme.Modules.pullback c).mapIso e ≪≫
    (Scheme.Modules.pullbackComp c v).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    ((Scheme.Modules.pullbackComp f c').app L).symm

lemma baseChangedLift_dual {X X' Y : Scheme.{u}} (c : X ⟶ Y) (c' : X' ⟶ Y)
    (f : X ⟶ X') (v : Y ⟶ Y) (h : c ≫ v = f ≫ c')
    (L : Y.Modules) (e : L ≅ (Scheme.Modules.pullback v).obj L)
    (φ : L ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    (baseChangedLift c c' f v h L e).hom ≫ pulledInclusion f (pulledInclusion c' φ) =
      pulledInclusion c (e.hom ≫ pulledInclusion v φ) := by
  simp only [baseChangedLift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [pulledInclusion_comp_inv, pulledInclusion_congr, pulledInclusion_comp]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma modelLift_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) (d : ℕ) :
    (modelLift k h3 M hM s hs rot scal iv ha d).hom ≫
      pulledInclusion iv.hom (idealInclusion (s.ker^d)) = idealInclusion (s.ker^d) := by
  have h := idealPullbackIso_inclusion iv.hom (s.ker^d) (s.ker^d)
    (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d)
    (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d)
    (inversion_power_ideal k h3 M hM s hs rot scal iv ha d)
  change _ = pulledInclusion iv.hom (idealInclusion (s.ker^d)) at h
  rw [← h]
  exact Iso.inv_hom_id_assoc _ _

lemma swap_top_value (n : ℕ) (a : A k n) :
    (TowerInversionR0137.chartSwap k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (TowerInversionR0137.swap k n a) := by
  have h := congrArg (fun f => f a) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TowerInversionR0137.swap k n)))
  exact h.symm

/-- The finite numerator identity determines the algebraic transformed section
on every chart and every thickness. -/
lemma modelLift_theta (m : ℕ) (hm : 0 < m) (he : Even m)
    {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k TT) (hM : IsModel k TT M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) (ν : Fin m) :
    (modelLift k (thetaChartBound m hm he) M hM s hs rot scal iv ha m).hom ≫
      pulledInclusion iv.hom (thetaSection k m hm he M hM s hs ν) =
      thetaSection k m hm he M hM s hs (negIndex m hm ν) := by
  let L := powerModule k M s m
  let e := modelLift k (thetaChartBound m hm he) M hM s hs rot scal iv ha m
  let φ := thetaSection k m hm he M hM s hs ν
  have hφ := (Classical.choose_spec (algebraized_theta_sections k m hm he TT M hM s hs
    (thetaVector k m ν))).1
  have ht : Realizes k (hm := hm) he M s 0 (thetaVector k m (negIndex m hm ν))
      (e.hom ≫ pulledInclusion iv.hom φ) := by
    intro n i
    let c := (TT.atlas n).chart i ≫ M.inclusion n
    let c' := (TT.atlas n).chart (Fin.rev i) ≫ M.inclusion n
    let f := TowerInversionR0137.chartSwap k n
    have hc : c ≫ iv.hom = f ≫ c' := AlgebraizedActionLawsR0137.chart_inversion M ha.2.2 n i
    let E := baseChangedLift c c' f iv.hom hc L e
    let j := idealInclusion (s.ker^m)
    have hj : E.hom ≫ pulledInclusion f (pulledInclusion c' j) = pulledInclusion c j := by
      rw [baseChangedLift_dual, modelLift_inclusion]
    have hq : E.hom ≫ pulledInclusion f (pulledInclusion c' φ) =
        pulledInclusion c (e.hom ≫ pulledInclusion iv.hom φ) :=
      baseChangedLift_dual c c' f iv.hom hc L e φ
    have hφ' : ∃ z : Γ((Scheme.Modules.pullback c').obj L, ⊤),
        (pulledInclusion c' j).app ⊤ z =
          (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k (2*m) n (Fin.rev i))^m) ∧
        (pulledInclusion c' φ).app ⊤ z =
          (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
            (finiteNumerator k m hm he (thetaVector k m ν) n (Fin.rev i)) := by
      obtain ⟨z, hz, hv⟩ := hφ n (Fin.rev i)
      refine ⟨z, hz, ?_⟩
      simp only [pow_zero, map_one, one_mul] at hv
      exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.eq_symm_apply.mpr hv
    have hp := pull_witness f _ _ _ _ _ hφ'
    have ha' : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        ((equation k (2*m) n (Fin.rev i))^m)) =
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k (2*m) n i)^m) := by
      rw [swap_top_value, map_pow, Numerators.swap_equation]
    have hb' : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (finiteNumerator k m hm he (thetaVector k m ν) n (Fin.rev i))) =
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
          (finiteNumerator k m hm he (thetaVector k m (negIndex m hm ν)) n i) := by
      rw [swap_top_value, Numerators.swap_finiteNumerator]
    rw [ha', hb'] at hp
    obtain ⟨z, hz, hv⟩ := (witness_iso E _ _ _ _ hj hq _ _).mpr hp
    refine ⟨z, hz, ?_⟩
    simp only [pow_zero, map_one, one_mul]
    exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.eq_symm_apply.mp hv
  exact (algebraized_theta_sections k m hm he TT M hM s hs
    (thetaVector k m (negIndex m hm ν))).unique ht
      (Classical.choose_spec (algebraized_theta_sections k m hm he TT M hM s hs
        (thetaVector k m (negIndex m hm ν)))).1

lemma genericLift_reverses (m : ℕ) (hm : 0 < m) (he : Even m)
    {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k TT) (hM : IsModel k TT M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    Reverses k M s m m hm (inversionMap k M rot scal iv ha)
      (genericLift k (thetaChartBound m hm he) M hM s hs rot scal iv ha m)
      (genericTheta k m hm he M hM s hs) := by
  intro ν
  change (baseChangedLift (genericInclusion k M) (genericInclusion k M)
    (inversionMap k M rot scal iv ha) iv.hom
    (inversionMap_inclusion k M rot scal iv ha).symm (powerModule k M s m)
    (modelLift k (thetaChartBound m hm he) M hM s hs rot scal iv ha m)).hom ≫
    pulledInclusion (inversionMap k M rot scal iv ha)
      (pulledInclusion (genericInclusion k M) (thetaSection k m hm he M hM s hs ν)) = _
  rw [baseChangedLift_dual, modelLift_theta]
  rfl

end ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141

namespace ArithmeticThetaGeometricLiftsR0141
open GeometricInversionLiftR0141

/-- The unique symmetric theta lift above the actual generic inversion map. -/
theorem geometric_inversion_lift :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∃! eS : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha), ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) := by
  intro k _ _ m hm he T M hM s hs rot scal iv ha
  let e := genericLift k (ArithmeticThetaGenericEvaluationR0140.thetaChartBound m hm he) M hM s hs rot scal iv ha m
  have h := genericLift_reverses k m hm he M hM s hs rot scal iv ha
  refine ⟨e, h, ?_⟩
  intro e' he'
  exact reversing_lift_unique k m hm he M hM s hs rot scal iv ha e' e he' h

end ArithmeticThetaGeometricLiftsR0141

#print axioms ArithmeticThetaGeometricLiftsR0141.geometric_inversion_lift
