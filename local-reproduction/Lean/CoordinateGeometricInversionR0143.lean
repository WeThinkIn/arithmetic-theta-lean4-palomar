import AlgebraicTateCoordinatesR0143

/-! Geometric inversion parity of the literal algebraic Tate coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraicCoordinatesR0143
namespace CoordinateGeometricInversionR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141

variable (k : Type u) [Field k] [CharZero k]

lemma swap_geometric (n : ℕ) (v : A k n) :
    TowerInversionR0137.swap k n (geometric k n v) =
      geometric k n (TowerInversionR0137.swap k n v) := by
  simp only [geometric, map_sum, map_pow]

lemma swap_term (odd : Bool) (n : ℕ) (v : A k n) :
    TowerInversionR0137.swap k n (term k odd n v) =
      term k odd n (TowerInversionR0137.swap k n v) := by
  cases odd <;> simp [term, swap_geometric]

lemma term_tail_zero (odd : Bool) (n e : ℕ) (he : n+1 ≤ e) (v : A k n) :
    term k odd n (tau k n ^ e * v) = 0 := by
  rw [TateXNumeratorSystemR0143.tau_pow_zero k n e he, zero_mul]
  simp [term]

def leftTerm (odd : Bool) (r n : ℕ) (i : Fin r) (a : ℕ) : A k n :=
  if a = 0 ∧ i.val = 0 then coordX k n * (if odd then 1+coordX k n else 1)
  else equation k r n i ^ degree odd * term k odd n (tau k n ^ (r*a+i.val) * coordX k n)

def rightTerm (odd : Bool) (r n : ℕ) (i : Fin r) (a : ℕ) : A k n :=
  if a = 0 ∧ i.val+1 = r then coordY k n * (if odd then 1+coordY k n else 1)
  else equation k r n i ^ degree odd * term k odd n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)

def leftSum (odd : Bool) (r n : ℕ) (i : Fin r) : A k n :=
  ∑ a ∈ Finset.range (n+1), leftTerm k odd r n i a

def rightSum (odd : Bool) (r n : ℕ) (i : Fin r) : A k n :=
  ∑ a ∈ Finset.range (n+1), rightTerm k odd r n i a

lemma leftSum_eq (odd : Bool) (r n : ℕ) (i : Fin r) :
    leftSum k odd r n i =
      (if i.val = 0 then coordX k n * (if odd then 1+coordX k n else 1)
       else equation k r n i ^ degree odd * term k odd n (tau k n ^ i.val * coordX k n)) +
      equation k r n i ^ degree odd * ∑ a ∈ Finset.range (n+1),
        term k odd n (tau k n ^ (r*(a+1)+i.val) * coordX k n) := by
  have hz : leftTerm k odd r n i (n+1) = 0 := by
    simp only [leftTerm, show ¬ (n+1 = 0 ∧ i.val = 0) by omega, ↓reduceIte]
    rw [term_tail_zero k odd n _ (by have hi := i.isLt; nlinarith), mul_zero]
  have hh := Finset.sum_range_succ' (leftTerm k odd r n i) (n+1)
  rw [Finset.sum_range_succ, hz, add_zero] at hh
  rw [leftSum, hh]
  simp only [leftTerm, Nat.succ_ne_zero, false_and,
    ↓reduceIte, mul_zero, zero_add, true_and, Finset.mul_sum]
  ring

lemma swap_leftTerm (odd : Bool) (r n : ℕ) (i : Fin r) (a : ℕ) :
    TowerInversionR0137.swap k n (leftTerm k odd r n (Fin.rev i) a) =
      rightTerm k odd r n i a := by
  have hi : (Fin.rev i).val = 0 ↔ i.val+1 = r := by simp only [Fin.rev]; omega
  have he : r*a+(Fin.rev i).val = r*(a+1)-i.val-1 := by
    simp only [Fin.rev, Nat.mul_add, Nat.mul_one]; omega
  unfold leftTerm rightTerm
  simp only [hi]
  split_ifs <;> cases odd <;>
    simp only [he, map_mul, map_pow, Numerators.swap_equation, swap_term, tau,
      TowerInversionR0137.swap_base_apply, TowerInversionR0137.swap_x,
      map_add, map_one]

lemma swap_leftSum (odd : Bool) (r n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n (leftSum k odd r n (Fin.rev i)) =
      rightSum k odd r n i := by
  simp only [leftSum, rightSum, map_sum, swap_leftTerm]

lemma swap_rightSum (odd : Bool) (r n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n (rightSum k odd r n (Fin.rev i)) =
      leftSum k odd r n i := by
  rw [← swap_leftSum, Fin.rev_rev]
  exact RingHom.congr_fun (TowerInversionR0137.swap_sq k n) _

lemma swap_numerator (odd : Bool) (r n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n (numerator k odd r n (Fin.rev i)) =
      if odd then -numerator k odd r n i else numerator k odd r n i := by
  have hn (j : Fin r) : numerator k odd r n j =
      if odd then
        base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) *
          (leftSum k odd r n j - rightSum k odd r n j)
      else leftSum k odd r n j + rightSum k odd r n j -
        2 * equation k r n j ^ degree odd * ∑ a ∈ Finset.range (n+1),
          (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1))) := by
    rw [leftSum_eq]
    rfl
  rw [hn, hn]
  cases odd <;>
    simp only [Bool.false_eq_true, ↓reduceIte, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_sum, map_natCast, swap_geometric, tau,
      TowerInversionR0137.swap_base_apply, Numerators.swap_equation,
      swap_leftSum, swap_rightSum] <;> ring

open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (witness_iso pull_witness)

def signed {X : Scheme.{u}} {L : X.Modules} (odd : Bool)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :=
  if odd then -φ else φ

lemma signed_app {X : Scheme.{u}} {L : X.Modules} (odd : Bool)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (U : X.Opens) (x : Γ(L, U)) :
    (signed odd φ).app U x =
      if odd then -(show Γ(X, U) from φ.app U x) else (show Γ(X, U) from φ.app U x) := by
  cases odd <;> rfl

lemma pull_signed {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (odd : Bool) (φ : L ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    pulledInclusion f (signed odd φ) = signed odd (pulledInclusion f φ) := by
  cases odd <;> simp [signed, pulledInclusion, Functor.map_neg]

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Transport the literal numerator through the canonical lift. The sign is
applied twice, once by the chart calculation and once on the morphism. -/
lemma signed_action_realizes (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    RealizesCoordinate k odd M s
      (signed odd (inversionAction k h3 M hM s hs rot scal iv ha (degree odd) φ)) := by
  intro n i
  let L := powerModule k M s (degree odd)
  let e := modelLift k h3 M hM s hs rot scal iv ha (degree odd)
  let c := (T.atlas n).chart i ≫ M.inclusion n
  let c' := (T.atlas n).chart (Fin.rev i) ≫ M.inclusion n
  let f := TowerInversionR0137.chartSwap k n
  have hc : c ≫ iv.hom = f ≫ c' := AlgebraizedActionLawsR0137.chart_inversion M ha.2.2 n i
  let E := baseChangedLift c c' f iv.hom hc L e
  let j := idealInclusion (s.ker ^ degree odd)
  have hj : E.hom ≫ pulledInclusion f (pulledInclusion c' j) = pulledInclusion c j := by
    rw [baseChangedLift_dual, modelLift_inclusion]
  have hq : E.hom ≫ pulledInclusion f (pulledInclusion c' φ) =
      pulledInclusion c (e.hom ≫ pulledInclusion iv.hom φ) :=
    baseChangedLift_dual c c' f iv.hom hc L e φ
  have hφ' : ∃ z : Γ((Scheme.Modules.pullback c').obj L, ⊤),
      (pulledInclusion c' j).app ⊤ z =
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
          (equation k r n (Fin.rev i) ^ degree odd) ∧
      (pulledInclusion c' φ).app ⊤ z =
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
          (numerator k odd r n (Fin.rev i)) := hφ n (Fin.rev i)
  have hp := pull_witness f _ _ _ _ _ hφ'
  have ha' : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (equation k r n (Fin.rev i) ^ degree odd)) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (equation k r n i ^ degree odd) := by
    rw [swap_top_value, map_pow, Numerators.swap_equation]
  have hb' : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (numerator k odd r n (Fin.rev i))) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (if odd then -numerator k odd r n i else numerator k odd r n i) := by
    rw [swap_top_value, swap_numerator]
  rw [ha', hb'] at hp
  obtain ⟨z, hz, hv⟩ := (witness_iso E _ _ _ _ hj hq _ _).mpr hp
  refine ⟨z, hz, ?_⟩
  change (pulledInclusion c (signed odd
    (e.hom ≫ pulledInclusion iv.hom φ))).app ⊤ z = _
  rw [pull_signed, signed_app, hv]
  cases odd <;> simp

end CoordinateGeometricInversionR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaIdentitySectionsR0138
open CoordinateGeometricInversionR0143

/-- Actual inversion fixes the algebraic Tate X and negates the algebraic Tate Y,
using the canonical lift on the second and third powers of the identity ideal. -/
theorem coordinate_geometric_inversion :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → ∀ (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (iv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal iv), ∀ (U : M.X.Opens) (x : ((ArithmeticThetaIdentitySectionsR0138.powerModule k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)).presheaf.obj (Opposite.op U))), (ArithmeticThetaAlgebraicCoordinatesR0143.inversionAction k h3 M hM s hs rot scal iv ha (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) φ).app U x = (if odd then -(show M.X.presheaf.obj (Opposite.op U) from φ.app U x) else (show M.X.presheaf.obj (Opposite.op U) from φ.app U x)) := by
  intro k _ _ r hr h3 T M hM s hs odd φ hφ rot scal iv ha U x
  have he := (algebraic_tate_coordinates k r hr h3 T M hM s hs odd).unique
    (signed_action_realizes k h3 M hM s hs odd φ hφ rot scal iv ha) hφ
  have hv := congrArg (fun ψ : Dual k M s (degree odd) => ψ.app U x) he
  rw [signed_app] at hv
  cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv ⊢
  · exact hv
  · exact neg_eq_iff_eq_neg.mp hv

end ArithmeticThetaAlgebraicCoordinatesR0143

#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_geometric_inversion
