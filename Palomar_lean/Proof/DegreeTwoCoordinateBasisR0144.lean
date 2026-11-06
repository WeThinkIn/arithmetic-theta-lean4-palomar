module

public import CubicModelDefinitionsR0144
public import CoordinateExactPolesR0143
public import TateXNumeratorSystemR0143

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The literal functions 1 and X give the complete degree-two section basis.
All helper declarations belong to this module's namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
namespace DegreeTwoCoordinateBasisR0144
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaIdentitySectionsR0138.IdentityPositiveSectionsRankR0138

/-- A split pair in a free module of rank two is a basis over a commutative ring. -/
lemma pair_bijective {S V : Type*} [CommRing S] [AddCommGroup V] [Module S V]
    (e : V ≃ₗ[S] (Fin 2 → S)) (v₀ v₁ : V) (a b : V →ₗ[S] S)
    (q : Sˣ) (ha₀ : a v₀ = 0) (ha₁ : a v₁ = 1) (hb₀ : b v₀ = q) :
    Function.Bijective (fun c : Fin 2 → S => c 0 • v₀ + c 1 • v₁) := by
  let f : (Fin 2 → S) →ₗ[S] V :=
    (LinearMap.proj 0).smulRight v₀ + (LinearMap.proj 1).smulRight v₁
  let p : V →ₗ[S] (Fin 2 → S) := LinearMap.pi (fun j =>
    if j = 0 then (↑q⁻¹ : S) • (b - (b v₁) • a) else a)
  have hp : p.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro c
    funext j
    fin_cases j <;>
      simp [p, f, ha₀, ha₁, hb₀, smul_eq_mul, mul_add, mul_sub]
    ring_nf
    rw [mul_right_comm, Units.inv_mul, one_mul]
  let F := e.toLinearMap.comp f
  let P := p.comp e.symm.toLinearMap
  have hPF : P.comp F = LinearMap.id := by
    apply LinearMap.ext
    intro c
    funext j
    have h := LinearMap.congr_fun hp c
    simpa [P, F] using congrFun h j
  have hFP : F.comp P = LinearMap.id := (LinearMap.comp_eq_id_comm S (Fin 2 → S)).mp hPF
  have hf : Function.Bijective F :=
    ⟨fun x y h => by simpa [← LinearMap.comp_apply, hPF] using congrArg P h,
      fun y => ⟨P y, LinearMap.congr_fun hFP y⟩⟩
  exact ⟨fun x y h => hf.1 (congrArg e h), fun v => by
    obtain ⟨c,hc⟩ := hf.2 (e v)
    exact ⟨c, e.injective hc⟩⟩

variable (k : Type u) [Field k] [CharZero k]

lemma marked_base (n : ℕ) (a : kˣ) (c : R k n) :
    markedPoint k n a (base k n c) = c := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  change (MvPolynomial.eval₂Hom ((RingHom.id (R k n)).comp (trunc _ PowerSeries.X n))
    (fun j : Fin 2 => if j = 0 then (markedUnit k n a : R k n)
      else parameter k n * ↑((markedUnit k n a)⁻¹))) (MvPolynomial.C f) = _
  simp [trunc]

lemma minus_marked_equation (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    markedPoint k n (-1) (equation k r n (zeroIndex r hr)) = 2 := by
  have hx : markedPoint k n (-1) (coordX k n) = -1 := by
    simp [markedPoint, mkPoint, coordX, markedUnit, trunc,
      ArithmeticThetaNodeCharts.x, ArithmeticThetaNodeCharts.quotientMap]
  norm_num [equation, zeroIndex, show ¬1 = r by omega, hx]

lemma basis_compatible (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (n : ℕ) (j : Fin (degree false)) :
    Compatible k r n hr (T.overlap n) (degree false) (basisNumerator k false r n j) := by
  have hj : j.val < 2 := j.isLt
  by_cases hz : j.val = 0
  · simp only [Compatible, basisNumerator, hz, ↓reduceIte]
    intro i
    simp only [map_pow]
    ring
  · have h1 : j.val = 1 := by omega
    simpa only [Compatible, basisNumerator, hz, h1, ↓reduceIte, Bool.false_eq_true, one_mul, Nat.one_ne_zero]
      using (tate_x_numerator_system k r hr h3 T).1 n

local instance nodeAlgebra (n : ℕ) : Algebra (R k n) (A k n) := (base k n).toAlgebra
local instance nodeModule (n : ℕ) : Module (R k n) (A k n) := (nodeAlgebra k n).toModule
local instance nodeAction (n : ℕ) : DistribMulAction (R k n) (A k n) :=
  (nodeModule k n).toDistribMulAction
local instance nodeMulAction (n : ℕ) : MulAction (R k n) (A k n) :=
  (nodeAction k n).toMulAction
local instance nodeScalar (n : ℕ) : SMul (R k n) (A k n) := ⟨fun c x => base k n c * x⟩
local instance nodeFamilyScalar (r n : ℕ) : SMul (R k n) (Fin r → A k n) :=
  ⟨fun c s i => base k n c * s i⟩

/-- Evaluation uses precisely the structural map of the actual nodal chart. -/
def evaluate (r n : ℕ) (hr : 0 < r) (a : kˣ) :
    (Fin r → A k n) →ₗ[R k n] R k n where
  toFun v := markedPoint k n a (v (zeroIndex r hr))
  map_add' v w := map_add _ _ _
  map_smul' c v := by
    change markedPoint k n a (base k n c * v (zeroIndex r hr)) = _
    rw [map_mul, marked_base]
    rfl

lemma coordinate_basis (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (n : ℕ) : CoordinateBasis k false (r := r) (hr := hr) (T.overlap n) := by
  classical
  refine ⟨basis_compatible k r hr h3 T n, ?_⟩
  obtain ⟨L,hL,_⟩ := truncated_laurent_presentation k n
  let E := T.overlap n
  have hE : IsAdjacent k n E := T.overlap_spec n
  let V := LinearMap.ker (difference L hL E hE r hr 2)
  let v : Fin 2 → V := fun j =>
    ⟨basisNumerator k false r n j,
      (compatible_iff_difference L hL E hE r hr h3 2 _).mp
        (basis_compatible k r hr h3 T n j)⟩
  let e : V ≃ₗ[R k n] (Fin 2 → R k n) :=
    (kernelCoordinates L hL E hE r hr h3 2 (by decide)).trans
      (Finsupp.linearEquivFunOnFinite (R k n) (R k n) (Fin 2))
  let a : V →ₗ[R k n] R k n := (evaluate k r n hr 1).comp (LinearMap.ker _).subtype
  let b : V →ₗ[R k n] R k n := (evaluate k r n hr (-1)).comp (LinearMap.ker _).subtype
  let q : (R k n)ˣ := Units.map
    ((trunc (PowerSeries k) PowerSeries.X n).comp PowerSeries.C)
    (Units.mk0 (4 : k) (by norm_num))
  have hq : (q : R k n) = 4 := by
    change (trunc (PowerSeries k) PowerSeries.X n) (PowerSeries.C (4 : k)) = 4
    rw [map_ofNat, map_ofNat]
  have ha₀ : a (v 0) = 0 := by
    change markedPoint k n 1 (basisNumerator k false r n (0 : Fin 2) (zeroIndex r hr)) = 0
    simp [basisNumerator, map_pow, CoordinateExactPolesR0143.marked_equation, degree]
  have ha₁ : a (v 1) = 1 := by
    change markedPoint k n 1 (basisNumerator k false r n (1 : Fin 2) (zeroIndex r hr)) = 1
    simpa [basisNumerator, degree] using CoordinateExactPolesR0143.numerator_identity k false r n hr h3
  have hb₀ : b (v 0) = q := by
    change markedPoint k n (-1) (basisNumerator k false r n (0 : Fin 2) (zeroIndex r hr)) = q
    rw [hq]
    norm_num [basisNumerator, map_pow, minus_marked_equation k r n hr h3, degree]
  have hf := pair_bijective e (v 0) (v 1) a b q ha₀ ha₁ hb₀
  intro s
  let s' : V := (sectionsKernel L hL E hE r hr h3 2) s
  obtain ⟨c,hc⟩ := hf.2 s'
  have hval (d : Fin 2 → R k n) (i : Fin r) :
      (d 0 • v 0 + d 1 • v 1).val i =
        ∑ j : Fin 2, base k n (d j) * basisNumerator k false r n j i := by
    rw [Fin.sum_univ_two]
    rfl
  refine ⟨c, ?_, ?_⟩
  · intro i
    exact (congrArg (fun w : V => w.val i) hc).symm.trans (hval c i)
  · intro d hd
    apply hf.1
    apply Subtype.ext
    funext i
    exact (hval d i).trans ((hd i).symm.trans (congrArg (fun w : V => w.val i) hc).symm)

end DegreeTwoCoordinateBasisR0144

/-- At every finite thickness, 1 and the literal Tate X have unique coefficients
for every section of the second power of the identity divisor. -/
theorem degree_two_coordinate_basis :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr), ∀ n : ℕ,
      CoordinateBasis k false (r := r) (hr := hr) (T.overlap n) := by
  intro k _ _ r hr h3 T n
  exact DegreeTwoCoordinateBasisR0144.coordinate_basis k r hr h3 T n

end ArithmeticThetaCubicModelR0144
#print axioms ArithmeticThetaCubicModelR0144.degree_two_coordinate_basis
