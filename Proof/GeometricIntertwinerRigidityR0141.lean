module

public import GeometricScalarLiftR0141
public import GeometricShiftLiftR0141

@[expose] public section

/-! Transport of actual geometric sections to the accepted formal synthesis theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141.GeometricIntertwinerRigidityR0141
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open GenericThetaBasisR0140

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
variable (s : baseScheme k ⟶ M.X) (d m : ℕ)
local instance dualAdd : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

def mulSection (a : LaurentSeries k) (φ : GenericDual k M s d) : GenericDual k M s d :=
  scale (scalarAt k M ⊤ a) φ

lemma mulSection_app (a : LaurentSeries k) (φ : GenericDual k M s d)
    (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)) :
    (mulSection k M s d a φ).app U x = scalarHom k M U a *
      (show Γ(genericScheme k M, U) from φ.app U x) :=
  GeometricShiftLiftR0141.scale_scalarAt_app k M s d a φ U x

lemma scaled_iff (a : LaurentSeries k) (φ ψ : GenericDual k M s d) :
    ScaledEq k M s d a φ ψ ↔ mulSection k M s d a φ = ψ := by
  constructor
  · intro h
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    exact (mulSection_app k M s d a φ U x).trans (h U x)
  · intro h U x
    rw [← h, mulSection_app]
    rfl

def combine (b : Fin m → GenericDual k M s d) (v : Fin m → LaurentSeries k) :
    GenericDual k M s d := ∑ ν, mulSection k M s d (v ν) (b ν)

lemma combine_app (b : Fin m → GenericDual k M s d) (v : Fin m → LaurentSeries k)
    (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)) :
    (combine k M s d m b v).app U x =
      ∑ ν, scalarHom k M U (v ν) * (show Γ(genericScheme k M, U) from (b ν).app U x) := by
  unfold combine
  rw [sum_app]
  apply Finset.sum_congr rfl
  intro ν _
  exact mulSection_app k M s d _ _ U x

lemma combines_iff (b : Fin m → GenericDual k M s d) (v : Fin m → LaurentSeries k)
    (φ : GenericDual k M s d) : Combines k M s d m b v φ ↔ φ = combine k M s d m b v :=
  GeometricShiftLiftR0141.combines_iff k M s d m b v φ

lemma combine_injective (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b) :
    Function.Injective (combine k M s d m b) := by
  intro v w h
  exact (hb (combine k M s d m b v)).unique
    ((combines_iff k M s d m b v _).mpr rfl)
    ((combines_iff k M s d m b w _).mpr h)

lemma combine_add (b : Fin m → GenericDual k M s d) (v w : Fin m → LaurentSeries k) :
    combine k M s d m b (v+w) = combine k M s d m b v + combine k M s d m b w := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  erw [Scheme.Modules.Hom.add_app]
  change _ = (combine k M s d m b v).app U x + (combine k M s d m b w).app U x
  simp only [combine_app,
    Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma combine_smul (b : Fin m → GenericDual k M s d) (a : LaurentSeries k)
    (v : Fin m → LaurentSeries k) :
    combine k M s d m b (a • v) = mulSection k M s d a (combine k M s d m b v) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [combine_app, mulSection_app, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum, mul_assoc]

lemma combine_delta (b : Fin m → GenericDual k M s d) (ν : Fin m) :
    combine k M s d m b (ArithmeticThetaSchrodingerR0119.delta k m ν) = b ν := by
  classical
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp [combine_app, ArithmeticThetaSchrodingerR0119.delta]

variable (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
def coordinates (φ : GenericDual k M s d) : Fin m → LaurentSeries k := (hb φ).choose
lemma coordinates_spec (φ : GenericDual k M s d) :
    combine k M s d m b (coordinates k M s d m b hb φ) = φ :=
  ((combines_iff k M s d m b _ φ).mp (hb φ).choose_spec.1).symm

variable (β : Fin m → GenericDual k M s d)
def comparison : (Fin m → LaurentSeries k) →ₗ[LaurentSeries k] (Fin m → LaurentSeries k) where
  toFun v := coordinates k M s d m b hb (combine k M s d m β v)
  map_add' v w := by
    apply combine_injective k M s d m b hb
    simp only [coordinates_spec, combine_add]
  map_smul' a v := by
    apply combine_injective k M s d m b hb
    change combine k M s d m b (coordinates k M s d m b hb (combine k M s d m β (a • v))) = _
    simp only [coordinates_spec, combine_smul, RingHom.id_apply]

lemma comparison_spec (v : Fin m → LaurentSeries k) :
    combine k M s d m b (comparison k M s d m b hb β v) = combine k M s d m β v :=
  coordinates_spec k M s d m b hb _

lemma comparison_injective (hβ : HasBasis k M s d m β) :
    Function.Injective (comparison k M s d m b hb β) := by
  intro v w h
  apply combine_injective k M s d m β hβ
  rw [← comparison_spec k M s d m b hb β v, ← comparison_spec k M s d m b hb β w, h]

omit hb β in
lemma act_combine (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) (e : Lift k M s d f)
    (v : Fin m → LaurentSeries k) :
    act k M s d f e (combine k M s d m b v) =
      combine k M s d m (fun ν => act k M s d f e (b ν)) v := by
  unfold combine mulSection
  rw [GeometricScalarLiftR0141.act_sum]
  apply Finset.sum_congr rfl
  intro ν _
  exact GeometricScalarLiftR0141.act_scale k M s d f hf e _ _

omit [CharZero k] in
lemma phase_eq (ζ : kˣ) (n : ℕ) : phase k ζ n = ArithmeticThetaSchrodingerR0119.scalar k ((ζ : k)^n) := by
  exact PowerSeries.coe_C _

omit hb β in
lemma eigen_combine (ζ : kˣ) (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) (e : Lift k M s d f)
    (he : Eigen k M s d m ζ f e b) (v : Fin m → LaurentSeries k) :
    act k M s d f e (combine k M s d m b v) =
      combine k M s d m b (ArithmeticThetaSchrodingerR0119.standardA k m (ζ : k) v) := by
  rw [act_combine k M s d m b f hf]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [combine_app, ArithmeticThetaSchrodingerR0119.standardA, map_mul]
  apply Finset.sum_congr rfl
  intro ν _
  have hh := he ν U x
  change scalarHom k M U (phase k ζ ν.val) * _ = _ at hh
  rw [← hh, phase_eq]
  dsimp only
  ring

lemma next_prev (hm : 0 < m) [NeZero m] (ν : Fin m) :
    next m hm (ArithmeticThetaSchrodingerR0119.prev m ν) = ν := by
  apply Fin.ext
  change (((ν.val + m - 1) % m) + 1) % m = ν.val
  rw [Nat.mod_add_mod, show ν.val + m - 1 + 1 = ν.val + m by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt ν.isLt]

lemma prev_next (hm : 0 < m) [NeZero m] (ν : Fin m) :
    ArithmeticThetaSchrodingerR0119.prev m (next m hm ν) = ν := by
  apply Fin.ext
  change (((ν.val+1)%m)+m-1)%m = ν.val
  by_cases h : ν.val+1 < m
  · rw [Nat.mod_eq_of_lt h, show ν.val+1+m-1 = ν.val+m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ν.isLt]
  · have hh : ν.val+1 = m := by omega
    rw [hh, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

omit hb β in
lemma cyclic_combine (hm : 0 < m) [NeZero m]
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) (e : Lift k M s d f)
    (he : Cyclic k M s d m hm f e b) (v : Fin m → LaurentSeries k) :
    act k M s d f e (combine k M s d m b v) =
      combine k M s d m b (ArithmeticThetaSchrodingerR0119.standardB k m v) := by
  rw [act_combine k M s d m b f hf]
  have hh : ∀ ν, act k M s d f e (b ν) = b (next m hm ν) := he
  simp_rw [hh]
  let E : Fin m ≃ Fin m := ⟨next m hm, ArithmeticThetaSchrodingerR0119.prev m, prev_next m hm, next_prev m hm⟩
  unfold combine ArithmeticThetaSchrodingerR0119.standardB
  rw [← E.sum_comp (fun ν => mulSection k M s d (v (ArithmeticThetaSchrodingerR0119.prev m ν)) (b ν))]
  simp only [E, Equiv.coe_fn_mk, prev_next]


include hb in
/-- The coordinate change is an intertwiner because both geometric actions
are linear for the actual structure-map scalars. -/
lemma common_scalar (hm : 0 < m) (heven : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m)
    (fA fB : genericScheme k M ⟶ genericScheme k M)
    (hfA : fA ≫ genericStructure k M = genericStructure k M)
    (hfB : fB ≫ genericStructure k M = genericStructure k M)
    (eA : Lift k M s d fA) (eB : Lift k M s d fB)
    (hAb : Eigen k M s d m ζ fA eA b) (hBb : Cyclic k M s d m hm fB eB b)
    (hβ : HasBasis k M s d m β)
    (hAβ : Eigen k M s d m ζ fA eA β) (hBβ : Cyclic k M s d m hm fB eB β) :
    ∃! c : LaurentSeries k, c ≠ 0 ∧ ∀ ν : Fin m, ScaledEq k M s d c (b ν) (β ν) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let L := comparison k M s d m b hb β
  have hLA (v : Fin m → LaurentSeries k) :
      L (ArithmeticThetaSchrodingerR0119.standardA k m (ζ : k) v) =
      ArithmeticThetaSchrodingerR0119.standardA k m (ζ : k) (L v) := by
    apply combine_injective k M s d m b hb
    rw [comparison_spec, ← eigen_combine k M s d m β ζ fA hfA eA hAβ,
      ← comparison_spec k M s d m b hb β v,
      eigen_combine k M s d m b ζ fA hfA eA hAb]
  have hLB (v : Fin m → LaurentSeries k) :
      L (ArithmeticThetaSchrodingerR0119.standardB k m v) =
      ArithmeticThetaSchrodingerR0119.standardB k m (L v) := by
    apply combine_injective k M s d m b hb
    rw [comparison_spec, ← cyclic_combine k M s d m β hm fB hfB eB hBβ,
      ← comparison_spec k M s d m b hb β v,
      cyclic_combine k M s d m b hm fB hfB eB hBb]
  obtain ⟨S, hS, hSeq⟩ :=
    (ArithmeticThetaSchrodingerR0119.schrodinger_common_scalar k m heven (ζ : k) hζ).1
  let F := S.comp L
  have hF : ArithmeticThetaSchrodingerR0119.Intertwines k m (ζ : k) F := by
    refine ⟨hS.1.comp (comparison_injective k M s d m b hb β hβ), ?_, ?_, ?_⟩
    · intro v
      exact hS.2.1 (L v)
    · intro v
      change S (L (ArithmeticThetaSchrodingerR0119.standardA k m (ζ : k) v)) = _
      rw [hLA]
      exact hS.2.2.1 (L v)
    · intro v
      change S (L (ArithmeticThetaSchrodingerR0119.standardB k m v)) = _
      rw [hLB]
      exact hS.2.2.2 (L v)
  obtain ⟨c, hc, _⟩ :=
    (ArithmeticThetaSchrodingerR0119.schrodinger_common_scalar k m heven (ζ : k) hζ).2 F hF
  have hL (v : Fin m → LaurentSeries k) : L v = c • v := by
    apply hS.1
    rw [map_smul, hSeq v]
    exact hc.2 v
  have hcommon (ν : Fin m) : ScaledEq k M s d c (b ν) (β ν) := by
    apply (scaled_iff k M s d c (b ν) (β ν)).mpr
    calc
      mulSection k M s d c (b ν) =
          combine k M s d m b (c • ArithmeticThetaSchrodingerR0119.delta k m ν) := by
        rw [combine_smul, combine_delta]
      _ = combine k M s d m b (L (ArithmeticThetaSchrodingerR0119.delta k m ν)) := by rw [hL]
      _ = β ν := by rw [comparison_spec, combine_delta]
  refine ⟨c, ⟨hc.1, hcommon⟩, ?_⟩
  intro a ha
  have hcoords : a • ArithmeticThetaSchrodingerR0119.delta k m (0 : Fin m) =
      c • ArithmeticThetaSchrodingerR0119.delta k m (0 : Fin m) := by
    apply combine_injective k M s d m b hb
    rw [combine_smul, combine_smul, combine_delta]
    exact ((scaled_iff k M s d a _ _).mp (ha.2 0)).trans
      ((scaled_iff k M s d c _ _).mp (hcommon 0)).symm
  have hzero := congrFun hcoords (0 : Fin m)
  simpa [ArithmeticThetaSchrodingerR0119.delta] using hzero

end ArithmeticThetaGeometricLiftsR0141.GeometricIntertwinerRigidityR0141

namespace ArithmeticThetaGeometricLiftsR0141
theorem geometric_intertwiner_rigidity :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ β : Fin m → ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ArithmeticThetaGeometricLiftsR0141.HasBasis k M s m m β → ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (β) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (β) → ∃! c : LaurentSeries k, c ≠ 0 ∧ ∀ ν : Fin m, ArithmeticThetaGenericEvaluationR0140.ScaledEq k M s m c ((ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) ν) (β ν) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB hA hB β hβ hAβ hBβ
  exact GeometricIntertwinerRigidityR0141.common_scalar k M s m m
    (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs)
    (ArithmeticThetaGenericEvaluationR0140.generic_theta_basis k m hm he T M hM s hs)
    β hm he ζ hζ _ _
    (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ)
    (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha)
    eA eB hA hB hβ hAβ hBβ

end ArithmeticThetaGeometricLiftsR0141
#print axioms ArithmeticThetaGeometricLiftsR0141.geometric_intertwiner_rigidity
