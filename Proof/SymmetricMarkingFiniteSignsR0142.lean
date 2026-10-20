module

public import GenericLiftScalarComparisonR0142

@[expose] public section

/-! Finite signs for genuine symmetric sheaf lifts. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaSymmetricMarkingR0142
namespace SymmetricMarkingFiniteSignsR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141
open GeometricThetaRelationsR0141

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
variable (s : baseScheme k ⟶ M.X) (d : ℕ)

lemma act_scaled (f : genericScheme k M ⟶ genericScheme k M)
    (e e' : Lift k M s d f) (c : LaurentSeries k)
    (h : LiftScaled k M s d f c e e') (φ : GenericDual k M s d) :
    act k M s d f e' φ = sc k M s d c (act k M s d f e φ) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  unfold act
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [h U x, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  exact (sc_app k M s d c (act k M s d f e φ) U x).symm

lemma scalar_faithful (m : ℕ) (hm : 0 < m)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (a c : LaurentSeries k) (h : ∀ φ, sc k M s d a φ = sc k M s d c φ) : a = c := by
  let ν : Fin m := ⟨0, hm⟩
  have hc : a • ArithmeticThetaSchrodingerR0119.delta k m ν =
      c • ArithmeticThetaSchrodingerR0119.delta k m ν := by
    apply GeometricIntertwinerRigidityR0141.combine_injective k M s d m b hb
    rw [GeometricIntertwinerRigidityR0141.combine_smul,
      GeometricIntertwinerRigidityR0141.combine_smul,
      GeometricIntertwinerRigidityR0141.combine_delta]
    exact h (b ν)
  have hh := congrFun hc ν
  simpa [ArithmeticThetaSchrodingerR0119.delta] using hh

lemma symmetry_square (m : ℕ) (hm : 0 < m)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (A S : GenericDual k M s d → GenericDual k M s d)
    (hA : LinearAction k M s d m A) (hS : LinearAction k M s d m S)
    (hn : ∀ φ, S (A (S (A φ))) = φ)
    (c : LaurentSeries k)
    (hc : ∀ φ, S (sc k M s d c (A (S (sc k M s d c (A φ))))) = φ) :
    c ^ 2 = 1 := by
  apply scalar_faithful k M s d m hm b hb
  intro φ
  have h := hc φ
  erw [hS.scale, hS.scale, hA.scale, hS.scale, sc_mul, hn] at h
  simpa only [pow_two, sc_one] using h

lemma constant_injective : Function.Injective (constant k) :=
  (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp PowerSeries.C_injective

lemma square_constant (c : LaurentSeries k) (hc : c ^ 2 = 1) :
    ∃ ε : k, ε ^ 2 = 1 ∧ constant k ε = c := by
  rcases sq_eq_one_iff.mp hc with h | h
  · exact ⟨1, by simp, by simpa [constant] using h.symm⟩
  · exact ⟨-1, by simp, by simpa [constant] using h.symm⟩

lemma scaled_iterate (m : ℕ) (A : GenericDual k M s d → GenericDual k M s d)
    (hA : LinearAction k M s d m A) (c : LaurentSeries k) (n : ℕ)
    (φ : GenericDual k M s d) :
    ((fun ψ => sc k M s d c (A ψ))^[n]) φ = sc k M s d (c^n) ((A^[n]) φ) := by
  induction n with
  | zero => exact (sc_one k M s d φ).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hA.scale, sc_mul,
      Function.iterate_succ_apply', pow_succ']

lemma relations_scaled (m : ℕ) (he : Even m) (ζ : kˣ)
    (A B S : GenericDual k M s m → GenericDual k M s m)
    (hA : LinearAction k M s m m A) (hB : LinearAction k M s m m B)
    (hS : LinearAction k M s m m S)
    (h : Relations k M s m ζ A B S)
    (a b : LaurentSeries k) (ha : a^2 = 1) (hb : b^2 = 1) :
    Relations k M s m ζ (fun φ => sc k M s m a (A φ))
      (fun φ => sc k M s m b (B φ)) S := by
  have period (c : LaurentSeries k) (hc : c^2 = 1) : c^m = 1 := by
    obtain ⟨n, hn⟩ := he
    rw [hn, ← two_mul, pow_mul, hc, one_pow]
  refine ⟨?_, ?_, ?_, h.2.2.2.1, ?_, ?_⟩
  · intro φ
    erw [scaled_iterate k M s m m A hA, period a ha, sc_one, h.1]
  · intro φ
    erw [scaled_iterate k M s m m B hB, period b hb, sc_one, h.2.1]
  · intro φ
    apply (scaled_iff k M s m _ _ _).mpr
    change sc k M s m a (A (sc k M s m b (B φ))) =
      sc k M s m (phase k ζ 1) (sc k M s m b (B (sc k M s m a (A φ))))
    have hab := (scaled_iff k M s m _ _ _).mp (h.2.2.1 φ)
    calc
      _ = sc k M s m (a*b) (A (B φ)) := by
        rw [hA.scale]
        exact sc_mul k M s m a b (A (B φ))
      _ = sc k M s m ((a*b)*phase k ζ 1) (B (A φ)) := by
        rw [hab]
        exact sc_mul k M s m (a*b) (phase k ζ 1) (B (A φ))
      _ = sc k M s m (phase k ζ 1*(b*a)) (B (A φ)) := by
        congr 1
        ring
      _ = _ := by
        rw [hB.scale]
        exact (sc_mul k M s m (phase k ζ 1) (b*a) (B (A φ))).symm.trans
          (congrArg (sc k M s m (phase k ζ 1))
            (sc_mul k M s m b a (B (A φ))).symm)
  · intro φ
    erw [hS.scale, hS.scale, hA.scale, hS.scale, sc_mul, ← pow_two, ha,
      sc_one, h.2.2.2.2.1]
  · intro φ
    erw [hS.scale, hS.scale, hB.scale, hS.scale, sc_mul, ← pow_two, hb,
      sc_one, h.2.2.2.2.2]

end SymmetricMarkingFiniteSignsR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open GeometricThetaRelationsR0141 SymmetricMarkingFiniteSignsR0142

theorem symmetric_marking_finite_signs :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)) (eS : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ (eA' : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB' : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaSymmetricMarkingR0142.Symmetric k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS eA' → ArithmeticThetaSymmetricMarkingR0142.Symmetric k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS eB' → ∃! σ : k × k, σ.1 ^ 2 = 1 ∧ σ.2 ^ 2 = 1 ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) (ArithmeticThetaSymmetricMarkingR0142.constant k σ.1) eA eA' ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) (ArithmeticThetaSymmetricMarkingR0142.constant k σ.2) eB eB' ∧ ArithmeticThetaGeometricLiftsR0141.Relations k M s m ζ (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA') (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB') (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB eS hA hB hS eA' eB' symA symB
  have h3 : 3 ≤ 2*m := by
    obtain ⟨n, hn⟩ := he
    omega
  obtain ⟨a, ha0, hua⟩ := generic_lift_scalar_comparison k (2*m)
    (Nat.mul_pos (by decide) hm) h3 T M hM s hs m _ eA eA'
  obtain ⟨b, hb0, hub⟩ := generic_lift_scalar_comparison k (2*m)
    (Nat.mul_pos (by decide) hm) h3 T M hM s hs m _ eB eB'
  have linA := linear_act (k := k) (M := M) (s := s) (d := m) m _
    (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ) eA
  have linB := linear_act (k := k) (M := M) (s := s) (d := m) m _
    (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha) eB
  have linS := linear_act (k := k) (M := M) (s := s) (d := m) m _
    (GeometricInversionLiftR0141.inversionMap_structure k M rot scal inv ha) eS
  have rel := geometric_theta_relations k m hm he T M hM s hs rot scal inv ha ζ hζ
    eA eB hA hB eS hS
  have basis := generic_theta_basis k m hm he T M hM s hs
  have actA := act_scaled k M s m _ eA eA' a ha0.2
  have actB := act_scaled k M s m _ eB eB' b hb0.2
  have asq : a^2 = 1 := by
    apply symmetry_square k M s m m hm _ basis _ _ linA linS rel.2.2.2.2.1 a
    intro φ
    have hh := symA φ
    simp only [actA] at hh
    exact hh
  have bsq : b^2 = 1 := by
    apply symmetry_square k M s m m hm _ basis _ _ linB linS rel.2.2.2.2.2 b
    intro φ
    have hh := symB φ
    simp only [actB] at hh
    exact hh
  obtain ⟨ε, hε, hcε⟩ := square_constant k a asq
  obtain ⟨δ, hδ, hcδ⟩ := square_constant k b bsq
  refine ⟨(ε, δ), ⟨hε, hδ, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [hcε] using ha0.2
  · simpa only [hcδ] using hb0.2
  · have hnew := relations_scaled k M s m he ζ _ _ _ linA linB linS rel a b asq bsq
    have ea : act k M s m (scalarMap k M rot scal inv ha ζ) eA' =
        fun φ => sc k M s m a (act k M s m (scalarMap k M rot scal inv ha ζ) eA φ) :=
      funext actA
    have eb : act k M s m (shiftMap k M rot scal inv ha) eB' =
        fun φ => sc k M s m b (act k M s m (shiftMap k M rot scal inv ha) eB φ) :=
      funext actB
    rw [ea, eb]
    exact hnew
  · intro τ hτ
    have cnz (c : k) (hc : c^2 = 1) : constant k c ≠ 0 := by
      have hcz : c ≠ 0 := by
        intro hh
        simpa [hh] using hc
      intro hh
      apply hcz
      apply constant_injective k
      simpa [constant] using hh
    apply Prod.ext
    · apply constant_injective k
      rw [hcε]
      exact hua (constant k τ.1) ⟨cnz τ.1 hτ.1, hτ.2.2.1⟩
    · apply constant_injective k
      rw [hcδ]
      exact hub (constant k τ.2) ⟨cnz τ.2 hτ.2.1, hτ.2.2.2.1⟩

end ArithmeticThetaSymmetricMarkingR0142
#print axioms ArithmeticThetaSymmetricMarkingR0142.symmetric_marking_finite_signs
